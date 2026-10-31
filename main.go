package main

import (
	"bufio"
	"bytes"
	"context"
	"crypto/rand"
	"encoding/hex"
	"encoding/json"
	"errors"
	"flag"
	"fmt"
	"io"
	"math"
	"math/big"
	"math/bits"
	mrand "math/rand"
	"net/http"
	"net/url"
	"os"
	"os/signal"
	"path/filepath"
	"regexp"
	"runtime"
	"strconv"
	"strings"
	"sync"
	"sync/atomic"
	"syscall"
	"time"
)

// DefaultServer is used when no -server flag, PI_SERVER variable or saved
// setting names one. Put your pi.php address here before building, and the
// people you give the program to can just run it.
const DefaultServer = ""

const (
	version   = "1.0.0"
	proto     = 4 // keep equal to PROTO in pi.php
	gamma     = 1.2041199826559248
	pi64      = "243f6a8885a308d313198a2e03707344a4093822299f31d0082efa98ec4e6c89"
	bailey1e6 = "26c65e52cb" // Bailey's published hex digits from position 1,000,000
	userAgent = "Mozilla/5.0 (compatible; pi-cli/" + version + ")"
	authMsg   = "pi.php no longer accepts this login (the id has another key, or it was banned). " +
		"To use your website login here: pi login CODE"
)

// historic records in decimal digits, the same levels the website uses
var records = []struct {
	d    float64
	name string
}{
	{2, "archimedes"}, {7, "zu chongzhi"}, {16, "al-kashi"}, {35, "van ceulen"},
	{100, "machin"}, {200, "dase"}, {527, "shanks"}, {620, "ferguson"},
	{2037, "eniac"}, {10000, "ibm 704"}, {100265, "ibm 7090"}, {250000, "ibm 7030"},
	{500000, "cdc 6600"}, {1001250, "cdc 7600"}, {2000036, "facom m-200"},
	{29360111, "cray-2"}, {1011196691, "chudnovsky"},
}

func level(d float64) int {
	i := -1
	for k, r := range records {
		if r.d <= d {
			i = k
		}
	}
	return i
}

/* ---------- arithmetic ---------- */

// Bellard 1997:
//   pi = 2^-6 sum_n (-1)^n 2^-10n ( -2^5/(4n+1) - 1/(4n+3) + 2^8/(10n+1)
//        - 2^6/(10n+3) - 2^2/(10n+5) - 2^2/(10n+7) + 1/(10n+9) )
// term i: modulus bsA*n+bsB, an extra power of two bsK, and its sign
var (
	bsA   = [7]int64{4, 4, 10, 10, 10, 10, 10}
	bsB   = [7]int64{1, 3, 1, 3, 5, 7, 9}
	bsK   = [7]int64{5, 0, 8, 6, 2, 2, 0}
	bsPos = [7]bool{false, false, true, false, false, false, true}
)

// Montgomery product a*b/2^32 mod m, for odd m below 2^32 and a, b below m,
// with inv = 1/m mod 2^32: three multiplies, no division, nothing overflows
func mont(a, b, m, inv uint64) uint64 {
	t := a * b
	q := uint64(uint32(t) * uint32(inv))
	th, qh := t>>32, (q*m)>>32
	r := th - qh
	if th < qh {
		r += m
	}
	return r
}

// the seven terms of one n, for e = 4p-6-10n >= 0 and every modulus below
// 2^32, in lockstep: the seven chains of squarings share one exponent and
// do not depend on each other, so the cpu runs them side by side
func termsN(n int64, e uint64, neg bool) uint64 {
	var m, inv, r [7]uint64
	top, rest := e, 0
	if l := bits.Len64(e); l > 5 {
		rest = l - 5
		top = e >> uint(rest)
	}
	for i := 0; i < 7; i++ {
		mi := uint64(bsA[i]*n + bsB[i])
		x := uint32(mi)
		y := x // right to 3 bits for any odd x, and each step doubles that
		y *= 2 - x*y
		y *= 2 - x*y
		y *= 2 - x*y
		y *= 2 - x*y
		m[i], inv[i] = mi, uint64(y)
		r[i] = (uint64(1) << (32 + top)) % mi // 2^top in Montgomery form
	}
	for b := rest - 1; b >= 0; b-- {
		if e>>uint(b)&1 == 0 {
			for i := 0; i < 7; i++ {
				r[i] = mont(r[i], r[i], m[i], inv[i])
			}
		} else {
			for i := 0; i < 7; i++ {
				x := mont(r[i], r[i], m[i], inv[i]) << 1
				if x >= m[i] {
					x -= m[i]
				}
				r[i] = x
			}
		}
	}
	var s uint64
	for i := 0; i < 7; i++ {
		x := r[i]
		for k := bsK[i]; k > 0; k-- {
			x <<= 1
			if x >= m[i] {
				x -= m[i]
			}
		}
		x = mont(x, 1, m[i], inv[i]) // out of Montgomery form: 2^(e+k) mod m
		t, _ := bits.Div64(x, 0, m[i])
		if bsPos[i] != neg {
			s += t
		} else {
			s -= t
		}
	}
	return s
}

func mulmod(a, b, m uint64) uint64 {
	if m <= 1<<32 {
		return a * b % m
	}
	hi, lo := bits.Mul64(a, b)
	return bits.Rem64(hi, lo, m)
}

func pow2mod(e, m uint64) uint64 {
	if m == 1 {
		return 0
	}
	r, b := uint64(1), uint64(2)%m
	for ; e > 0; e >>= 1 {
		if e&1 == 1 {
			r = mulmod(r, b, m)
		}
		b = mulmod(b, b, m)
	}
	return r
}

// one term, frac(2^E / m), as a 64-bit binary fraction rounded down
func term(E int64, m uint64) uint64 {
	if E >= 0 {
		q, _ := bits.Div64(pow2mod(uint64(E), m), 0, m)
		return q
	}
	if E > -64 {
		return (uint64(1) << uint(64+E)) / m
	}
	return 0
}

// frac(16^p * pi) to 44 bits: the 11 hex digits from 0-indexed position p,
// the same quantity the page's evalX returns. Each term is floored to 2^-64,
// so the error stays far below the 2^-33 the carry settling tolerates.
func evalWith(p int64, stop *atomic.Bool, fast bool) (uint64, bool) {
	base := 4*p - 6
	nEnd := (base+8)/10 + 8
	var s uint64
	for n := int64(0); n <= nEnd; n++ {
		if n&2047 == 0 && stop != nil && stop.Load() {
			return 0, false
		}
		e0 := base - 10*n
		neg := n&1 == 1
		if fast && e0 >= 0 && 10*n+9 < 1<<32 {
			s += termsN(n, uint64(e0), neg)
			continue
		}
		for i := 0; i < 7; i++ {
			t := term(e0+bsK[i], uint64(bsA[i]*n+bsB[i]))
			if bsPos[i] != neg {
				s += t
			} else {
				s -= t
			}
		}
	}
	return s >> 20, true
}

func evalX(p int64, stop *atomic.Bool) (uint64, bool) { return evalWith(p, stop, true) }

func hex8(d uint32) string { return fmt.Sprintf("%08x", d) }

// evals overlap by 3 hex digits: rounding each against the next one's
// leading digits settles any carry, exactly as the page does
func digitsOf(xs []uint64) string {
	E := len(xs) - 1
	ds := make([]uint32, E)
	nx := int64(xs[E] >> 32)
	for i := E - 1; i >= 0; i-- {
		d := uint32((int64(xs[i]) - nx + 2048) >> 12)
		ds[i] = d
		nx = int64(d >> 20)
	}
	var sb strings.Builder
	sb.Grow(8*E + 4)
	for _, d := range ds {
		sb.WriteString(hex8(d))
	}
	fmt.Fprintf(&sb, "%04x", xs[E]>>28)
	return sb.String()
}

// a spot check: 8 digits at pos, the carry settled exactly as a slice settles it
func spot(pos int64, stop *atomic.Bool) (string, bool) {
	a, ok := evalX(pos, stop)
	if !ok {
		return "", false
	}
	b, ok := evalX(pos+8, stop)
	if !ok {
		return "", false
	}
	return hex8(uint32((int64(a) - int64(b>>32) + 2048) >> 12)), true
}

// a job: 8*E hex digits from start, then the 4 guard digits that follow
func computeSlice(start int64, E int, stop *atomic.Bool, each func(time.Duration)) (string, bool) {
	xs := make([]uint64, E+1)
	for i := range xs {
		t0 := time.Now()
		x, ok := evalX(start+8*int64(i), stop)
		if !ok {
			return "", false
		}
		xs[i] = x
		if each != nil {
			each(time.Since(t0))
		}
	}
	return digitsOf(xs), true
}

/* ---------- self checks ---------- */

type check struct {
	name string
	run  func() error
}

func localChecks(deep bool) []check {
	ps := []int64{0, 1, 2, 3, 7, 64, 1000, 65537, 250000}
	if deep {
		ps = append(ps, 2000000)
	}
	return []check{
		{"fast arithmetic agrees with plain arithmetic", func() error {
			for _, p := range ps {
				a, _ := evalWith(p, nil, true)
				b, _ := evalWith(p, nil, false)
				if a != b {
					return fmt.Errorf("they differ at position %d", p)
				}
			}
			return nil
		}},
		{"first 60 hex digits match pi.php's constant", func() error {
			d, _ := computeSlice(0, 7, nil, nil)
			if d != pi64[:60] {
				return fmt.Errorf("got %s", d)
			}
			return nil
		}},
		{"spot checks match pi.php's constant", func() error {
			for _, p := range []int64{8, 27, 56} {
				if d, _ := spot(p, nil); d != pi64[p:p+8] {
					return fmt.Errorf("position %d: got %s, want %s", p, d, pi64[p:p+8])
				}
			}
			return nil
		}},
		{"position 1,000,000 matches Bailey's published digits", func() error {
			x, _ := evalX(1000000, nil)
			if got := fmt.Sprintf("%011x", x)[:10]; got != bailey1e6 {
				return fmt.Errorf("got %s, want %s", got, bailey1e6)
			}
			return nil
		}},
	}
}

var errMismatch = errors.New("wrong digits")

// compare a few random positions with the server's verified chain
func remoteCheck(ctx context.Context, a *api, hexLen int64) error {
	n := hexLen
	if n > 40000 {
		n = 40000
	}
	if n < 200 {
		return nil
	}
	chain, err := a.hexChain(ctx, n)
	if err != nil {
		return err
	}
	for i := 0; i < 4; i++ {
		p := 64 + mrand.Int63n(n-72)
		got, _ := spot(p, nil)
		if want := chain[p : p+8]; got != want {
			return fmt.Errorf("%w: at hex position %s this build computes %s, pi.hex has %s",
				errMismatch, commas(p), got, want)
		}
	}
	return nil
}

/* ---------- talking to pi.php ---------- */

type api struct {
	base     string
	sid, key string
	hc       *http.Client // ordinary calls, with a timeout
	long     *http.Client // the hex chain and conversions, bounded by a context
}

func newAPI(base, sid, key string, conns int) *api {
	tr := http.DefaultTransport.(*http.Transport).Clone()
	tr.MaxIdleConns = 2*conns + 8
	tr.MaxIdleConnsPerHost = 2*conns + 8
	return &api{
		base: base, sid: sid, key: key,
		hc:   &http.Client{Transport: tr, Timeout: 90 * time.Second},
		long: &http.Client{Transport: tr},
	}
}

type workResp struct {
	ID    int64   `json:"id"`
	Start int64   `json:"start"`
	Evals int     `json:"evals"`
	Au    []int64 `json:"au"`
	Cv    string  `json:"cv"`
	N     int64   `json:"n"`
	D     int64   `json:"d"`
	K     int64   `json:"k"`
	Wait  float64 `json:"wait"`
	Err   string  `json:"err"`
}

func (w *workResp) valid() bool {
	return w.Cv != "" || w.Wait > 0 || (w.ID > 0 && w.Evals >= 1 && w.Evals <= 1024 && w.Start >= 0)
}

type submitResp struct {
	OK     bool   `json:"ok"`
	Dup    bool   `json:"dup"`
	Digits int64  `json:"digits"`
	Hex    int64  `json:"hex"`
	Err    string `json:"err"`
}

type convResp struct {
	OK     bool   `json:"ok"`
	Digits int64  `json:"digits"`
	Err    string `json:"err"`
}

type nameResp struct {
	OK   bool   `json:"ok"`
	Name string `json:"name"`
	Err  string `json:"err"`
}

type findResp struct {
	N   int64  `json:"n"`
	At  int64  `json:"at"`
	Ctx string `json:"ctx"`
	K   int    `json:"k"`
	Err string `json:"err"`
}

type youResp struct {
	Name string `json:"name"`
	D    int64  `json:"d"`
	J    int64  `json:"j"`
	CV   int64  `json:"cv"`
	Rank int64  `json:"rank"`
	WD   int64  `json:"wd"`
	WR   int64  `json:"wr"`
}

type statsResp struct {
	Digits  int64            `json:"digits"`
	Hex     int64            `json:"hex"`
	PerMin  float64          `json:"per_min"`
	Active  int64            `json:"active"`
	Ever    int64            `json:"ever"`
	Checked int64            `json:"checked"`
	Feed    [][2]interface{} `json:"feed"`
	Warn    string           `json:"warn"`
	Tail    string           `json:"tail"`
	Top     [][2]interface{} `json:"top"`
	You     *youResp         `json:"you"`
	Err     string           `json:"err"`
}

func (a *api) request(ctx context.Context, c *http.Client, method, q string, body interface{}) (*http.Response, error) {
	var rd io.Reader
	if body != nil {
		b, err := json.Marshal(body)
		if err != nil {
			return nil, err
		}
		rd = bytes.NewReader(b)
	}
	req, err := http.NewRequestWithContext(ctx, method, a.base+q, rd)
	if err != nil {
		return nil, err
	}
	req.Header.Set("User-Agent", userAgent)
	req.Header.Set("X-Pi-Key", a.key) // the secret key travels in a header, never the URL
	req.Header.Set("Cache-Control", "no-store")
	if body != nil {
		req.Header.Set("Content-Type", "application/json")
	}
	return c.Do(req)
}

// do sends a request and decodes pi.php's JSON; its "err" field is left to the caller
func (a *api) do(ctx context.Context, c *http.Client, method, q string, body, out interface{}) error {
	resp, err := a.request(ctx, c, method, q, body)
	if err != nil {
		return err
	}
	defer resp.Body.Close()
	raw, err := io.ReadAll(io.LimitReader(resp.Body, 8<<20))
	if err != nil {
		return err
	}
	if json.Unmarshal(raw, out) != nil {
		s := strings.TrimSpace(string(raw))
		if strings.HasPrefix(s, "<") {
			return fmt.Errorf("got a web page (status %d) instead of pi.php's answer: check the address, "+
				"or a firewall on the host may be blocking this program", resp.StatusCode)
		}
		if len(s) > 60 {
			s = s[:60]
		}
		return fmt.Errorf("status %d, not pi.php's JSON: %q", resp.StatusCode, s)
	}
	return nil
}

func (a *api) call(ctx context.Context, method, q string, body, out interface{}) error {
	return a.do(ctx, a.hc, method, q, body, out)
}

func (a *api) work(ctx context.Context, want int, conv bool) (*workResp, error) {
	cv := "0"
	if conv {
		cv = "1"
	}
	// c=1 marks a native client; pi.php ignores it unless you add the optional tweak
	q := fmt.Sprintf("?a=work&v=%d&cv=%s&c=1&sid=%s&w=%d", proto, cv, a.sid, want)
	var w workResp
	if err := a.call(ctx, "GET", q, nil, &w); err != nil {
		return nil, err
	}
	return &w, nil
}

func (a *api) stats(ctx context.Context, w string) (*statsResp, error) {
	var s statsResp
	if err := a.call(ctx, "GET", "?a=stats&w="+w+"&sid="+a.sid, nil, &s); err != nil {
		return nil, err
	}
	if s.Err != "" {
		return nil, errors.New("pi.php: " + s.Err)
	}
	return &s, nil
}

func (a *api) hexChain(ctx context.Context, n int64) (string, error) {
	resp, err := a.request(ctx, a.long, "GET", "?a=hex&n="+strconv.FormatInt(n, 10), nil)
	if err != nil {
		return "", err
	}
	defer resp.Body.Close()
	if resp.StatusCode != http.StatusOK {
		return "", fmt.Errorf("pi.hex: status %d", resp.StatusCode)
	}
	b, err := io.ReadAll(io.LimitReader(resp.Body, n+1))
	if err != nil {
		return "", err
	}
	if int64(len(b)) != n {
		return "", fmt.Errorf("pi.hex: got %d digits, wanted %d", len(b), n)
	}
	return string(b), nil
}

/* ---------- the engine: one worker per thread, like the page's web workers ---------- */

const (
	stStart int32 = iota
	stWait
	stNet
	stWork
	stConv
)

type fetched struct {
	w   *workResp
	err error
}

type engine struct {
	api    *api
	power  int
	conv   bool
	ctx    context.Context
	cancel context.CancelFunc
	stop   atomic.Bool
	subs   sync.WaitGroup
	states []atomic.Int32
	events chan string

	hexDone  atomic.Int64 // hex digits computed this run
	accepted atomic.Int64 // hex digits pi.php accepted this run
	convd    atomic.Int64 // decimal digits converted this run
	landed   atomic.Bool
	oldHint  atomic.Bool

	mu    sync.Mutex
	fatal string
}

func (e *engine) say(s string) {
	select {
	case e.events <- s:
	default:
	}
}

func (e *engine) die(msg string) {
	e.mu.Lock()
	if e.fatal == "" {
		e.fatal = msg
	}
	e.mu.Unlock()
	e.stop.Store(true)
	e.cancel()
}

// the busiest state across workers: converting, computing, offline, waiting, starting
func (e *engine) state() int32 {
	var best int32
	for i := range e.states {
		if s := e.states[i].Load(); s > best {
			best = s
		}
	}
	return best
}

// pipeline: prefetch the next job while computing, submit in the background
// with retries, so the cpu never idles on the network
func (e *engine) worker(id int, wg *sync.WaitGroup) {
	defer wg.Done()
	st := &e.states[id]
	evalMs := 500.0
	fails := 0
	var last time.Time
	var next chan fetched
	prefetch := func() {
		if next != nil || e.stop.Load() {
			return
		}
		want := int(math.Round(15000 / math.Max(evalMs, 0.003)))
		if want < 1 {
			want = 1
		}
		if want > 1024 {
			want = 1024
		}
		ch := make(chan fetched, 1)
		next = ch
		go func() {
			if d := 300*time.Millisecond - time.Since(last); d > 0 {
				sleepCtx(e.ctx, d)
			}
			last = time.Now()
			w, err := e.api.work(e.ctx, want, e.conv)
			ch <- fetched{w, err}
		}()
	}
	for {
		prefetch()
		if next == nil {
			return
		}
		var f fetched
		select {
		case f = <-next:
		case <-e.ctx.Done():
			return
		}
		next = nil
		if e.stop.Load() {
			return
		}
		w := f.w
		if f.err != nil || w == nil || w.Err != "" || !w.valid() {
			st.Store(stNet)
			fails++
			back := math.Min(30000, 1000*math.Pow(2, math.Min(float64(fails), 5))) * (0.5 + mrand.Float64())
			sleepCtx(e.ctx, time.Duration(back*float64(time.Millisecond)))
			continue
		}
		fails = 0
		if w.Cv != "" {
			st.Store(stConv)
			e.convert(w)
			continue
		}
		if w.Wait > 0 {
			st.Store(stWait)
			if w.Wait >= 60 && e.oldHint.CompareAndSwap(false, true) {
				e.say("pi.php asked this client to wait; if that keeps happening it wants a newer pi-cli")
			}
			sleepCtx(e.ctx, time.Duration((w.Wait*500+mrand.Float64()*w.Wait*1000)*float64(time.Millisecond)))
			continue
		}

		st.Store(stWork)
		prefetch() // overlap the next fetch with this compute
		var spent time.Duration
		d, ok := computeSlice(w.Start, w.Evals, &e.stop, func(dt time.Duration) {
			spent += dt
			evalMs = evalMs*0.7 + math.Max(dt.Seconds()*1000, 0.003)*0.3
			e.hexDone.Add(8)
			if e.power < 100 {
				sleepCtx(e.ctx, dt*time.Duration(100-e.power)/time.Duration(e.power))
			}
		})
		if !ok {
			return
		}
		var au []interface{}
		if len(w.Au) == 2 {
			if v, ok := spot(w.Au[1], &e.stop); ok {
				au = []interface{}{w.Au[0], v}
			}
		}
		e.subs.Add(1)
		go e.submit(w, d, spent, au)
	}
}

func (e *engine) submit(w *workResp, d string, spent time.Duration, au []interface{}) {
	defer e.subs.Done()
	body := map[string]interface{}{"id": w.ID, "sid": e.api.sid, "k": e.api.key, "ms": spent.Milliseconds(), "d": d}
	if au != nil {
		body["au"] = au
	}
	for try := 0; try < 3; try++ {
		if try > 0 {
			time.Sleep(time.Duration(1500*try) * time.Millisecond)
		}
		ctx, cancel := context.WithTimeout(context.Background(), 60*time.Second)
		var r submitResp
		err := e.api.call(ctx, "POST", "?a=submit", body, &r)
		cancel()
		if err != nil {
			continue
		}
		n := int64(8 * w.Evals)
		switch {
		case r.Err == "auth":
			e.die(authMsg)
		case r.OK && !r.Dup:
			e.accepted.Add(n)
			if r.Hex >= w.Start+n && e.landed.CompareAndSwap(false, true) {
				e.say("your first slice of this run just joined the chain")
			}
		}
		return
	}
}

// decimal conversion: the chain's next decimal digits, plus the remainder pi.php verifies
func (e *engine) convert(w *workResp) {
	if w.N <= 0 || w.D < 0 || w.K <= w.D {
		return
	}
	secs := 90 + w.N/2000
	if secs > 1800 {
		secs = 1800
	}
	ctx, cancel := context.WithTimeout(e.ctx, time.Duration(secs)*time.Second)
	defer cancel()
	t0 := time.Now()
	chain, err := e.api.hexChain(ctx, w.N)
	if err != nil {
		return
	}
	k, digits, rem, err := toDecimal(chain, w.N, w.D, w.K)
	if err != nil || e.stop.Load() {
		return
	}
	// as on the page: the key goes in the header, and "k" is the digit count
	body := map[string]interface{}{"tok": w.Cv, "sid": e.api.sid, "k": k, "d": digits, "r": rem}
	var r convResp
	if err := e.api.do(ctx, e.api.long, "POST", "?a=conv", body, &r); err != nil {
		e.say("a decimal conversion could not be sent: " + err.Error())
		return
	}
	switch {
	case r.Err == "auth":
		e.die(authMsg)
	case r.Err != "":
		e.say("pi.php turned down a decimal conversion (" + r.Err + ")")
	case k > w.D:
		e.convd.Add(k - w.D)
		e.say(fmt.Sprintf("you converted %s digits to decimal in %.0fs", commas(k-w.D), time.Since(t0).Seconds()))
	}
}

// H*5^K = D*2^B + R with B = 4N-K: the first K decimal digits and the remainder,
// keeping only digits no later hex digit can change (the page's convJob, in math/big)
func toDecimal(chain string, N, D, K int64) (int64, string, string, error) {
	H, ok := new(big.Int).SetString(chain, 16)
	if !ok {
		return 0, "", "", errors.New("the hex chain is not hex")
	}
	if K <= D || 4*N-K < 1 {
		return D, "", "0", nil
	}
	one, five := big.NewInt(1), big.NewInt(5)
	B0 := uint(4*N - D)
	mask := new(big.Int).Lsh(one, B0)
	mask.Sub(mask, one)
	p5 := new(big.Int).Exp(five, big.NewInt(D), nil)
	a := new(big.Int).And(H, mask)
	a.Mul(a, p5).And(a, mask)
	jj := K - D
	B := B0 - uint(jj)
	f := new(big.Int).Exp(five, big.NewInt(jj), nil)
	y := new(big.Int).Mul(a, f)
	p5k := new(big.Int).Mul(p5, f)
	rem, lim, t := new(big.Int), new(big.Int), new(big.Int)
	for jj > 0 {
		lim.Lsh(one, B)
		rem.Sub(lim, one).And(rem, y)
		t.Add(rem, p5k)
		if B > 20 {
			lim.Sub(lim, new(big.Int).Lsh(one, B-20))
		}
		if t.Cmp(lim) <= 0 {
			break
		}
		jj--
		B++
		y.Quo(y, five)
		p5k.Quo(p5k, five)
	}
	if jj == 0 {
		return D, "", "0", nil
	}
	s := new(big.Int).Rsh(y, B).Text(10)
	if pad := int(jj) - len(s); pad > 0 {
		s = strings.Repeat("0", pad) + s
	}
	return D + jj, s, rem.Text(16), nil
}

/* ---------- the terminal ---------- */

type sample struct {
	t time.Time
	n int64
}

type screen struct {
	tty   bool
	width int
	last  time.Time
	seen  map[string]bool
	lvl   int
	rank  int64
	warn  string
}

func (u *screen) clear() {
	if u.tty && u.width > 0 {
		fmt.Print("\r" + strings.Repeat(" ", u.width) + "\r")
		u.width = 0
	}
}

func (u *screen) println(s string) {
	u.clear()
	fmt.Println(time.Now().Format("15:04") + "  " + s)
}

// one line rewritten in place with \r, which every terminal understands
func (u *screen) status(s string) {
	if !u.tty {
		if time.Since(u.last) >= time.Minute {
			u.last = time.Now()
			fmt.Println(time.Now().Format("15:04") + "  " + s)
		}
		return
	}
	if len(s) > 78 {
		s = s[:78]
	}
	pad := ""
	if u.width > len(s) {
		pad = strings.Repeat(" ", u.width-len(s))
	}
	fmt.Print("\r" + s + pad)
	u.width = len(s)
}

// new items in the live feed, levels and rank changes
func (u *screen) news(s *statsResp, quiet bool) {
	cur := make(map[string]bool, len(s.Feed))
	for i := len(s.Feed) - 1; i >= 0; i-- {
		t, _ := s.Feed[i][0].(float64)
		msg, _ := s.Feed[i][1].(string)
		k := strconv.FormatFloat(t, 'f', 0, 64) + "|" + msg
		cur[k] = true
		if !quiet && msg != "" && !u.seen[k] {
			u.println("live: " + msg)
		}
	}
	u.seen = cur
	if !quiet && s.Warn != "" && s.Warn != u.warn {
		u.println("server: " + s.Warn)
	}
	u.warn = s.Warn
	y := s.You
	if y == nil {
		return
	}
	L := level(float64(y.D) * gamma)
	if !quiet && L > u.lvl {
		u.println(fmt.Sprintf("level %d: you out-computed %s (%s digits)", L+1, records[L].name, commas(int64(records[L].d))))
	}
	if L > u.lvl {
		u.lvl = L
	}
	if !quiet && y.Name != "" && y.Rank > 0 && u.rank > 0 && y.Rank < u.rank {
		if y.Rank == 1 {
			u.println("you're #1 on the leaderboard!")
		} else {
			u.println(fmt.Sprintf("you climbed to #%d", y.Rank))
		}
	}
	u.rank = y.Rank
}

func statusLine(e *engine, s *statsResp, rate float64, spin int) string {
	st := "starting"
	switch e.state() {
	case stConv:
		st = "converting to decimal"
	case stWork:
		st = "computing"
	case stNet:
		st = "offline, retrying"
	case stWait:
		st = "waiting for work"
	}
	i := spin % 4
	line := `|/-\`[i:i+1] + " " + st
	if rate > 0 {
		line += " | " + compact(rate) + " digits/min"
	}
	if s != nil {
		if y := s.You; y != nil {
			line += " | you " + compact(float64(y.D)*gamma)
			if y.Name != "" && y.Rank > 0 {
				line += " #" + strconv.FormatInt(y.Rank, 10)
			}
		}
		line += " | pi.txt " + compact(float64(s.Digits))
	}
	return line
}

func printBoard(s *statsResp, day bool) {
	if day {
		fmt.Println("top contributors, last 24 hours")
	} else {
		fmt.Println("top contributors, all time")
	}
	my := ""
	if s.You != nil {
		my = s.You.Name
	}
	if len(s.Top) == 0 {
		fmt.Println("   no names yet, be the first")
	}
	for i, r := range s.Top {
		name, _ := r[0].(string)
		d, _ := r[1].(float64)
		mark := " "
		if my != "" && name == my {
			mark = ">"
		}
		fmt.Printf("  %s%2d  %-16s %8s\n", mark, i+1, name, compact(d*gamma))
	}
	if y := s.You; y != nil && y.WD > 0 {
		who := "you would be"
		if y.Name != "" {
			who = "you are"
		}
		fmt.Printf("  %s #%d with %s digits\n", who, y.WR, compact(float64(y.WD)*gamma))
	}
}

/* ---------- commands ---------- */

func cmdRun(a *api, threads, power int, conv bool) int {
	fmt.Printf("pi-cli %s for %s\n", version, a.base)
	fmt.Print("checking this build's arithmetic... ")
	for _, c := range localChecks(false) {
		if err := c.run(); err != nil {
			fmt.Printf("failed\n  %s: %v\n", c.name, err)
			fmt.Println("not contributing: wrong digits fail the spot checks, and that bans the name")
			return 1
		}
	}
	fmt.Println("ok")

	ctx, cancel := context.WithTimeout(context.Background(), 2*time.Minute)
	defer cancel()
	s, err := a.stats(ctx, "all")
	if err != nil {
		fmt.Println("cannot reach pi.php:", err)
		return 1
	}
	if s.You == nil {
		fmt.Println(authMsg)
		return 1
	}
	fmt.Print("checking against pi.hex on the server... ")
	switch err = remoteCheck(ctx, a, s.Hex); {
	case err == nil:
		fmt.Println("ok")
	case errors.Is(err, errMismatch):
		fmt.Printf("failed\n  %v\nnot contributing: this build or the server's chain is wrong\n", err)
		return 1
	default:
		fmt.Println("skipped,", err)
	}

	if y := s.You; y.Name != "" {
		fmt.Printf("signed in as %s, %s digits", y.Name, compact(float64(y.D)*gamma))
		if y.Rank > 0 {
			fmt.Printf(", #%d", y.Rank)
		}
		fmt.Println()
	} else {
		fmt.Println("computing anonymously:  pi name NAME  lists you,  pi login CODE  joins your browser's name")
	}
	fmt.Printf("%d threads of %d at %d%% power | pi.txt has %s digits | %d online\n\n",
		threads, runtime.NumCPU(), power, commas(s.Digits), s.Active)
	printBoard(s, false)
	fmt.Println("\nctrl+c stops (finished work is sent first)")

	e := &engine{api: a, power: power, conv: conv, states: make([]atomic.Int32, threads), events: make(chan string, 64)}
	e.ctx, e.cancel = context.WithCancel(context.Background())
	sig := make(chan os.Signal, 2)
	signal.Notify(sig, os.Interrupt, syscall.SIGTERM)
	var wg sync.WaitGroup
	for i := 0; i < threads; i++ {
		wg.Add(1)
		go e.worker(i, &wg)
	}

	u := &screen{tty: isTTY(), lvl: -1, last: time.Now()}
	u.news(s, true)
	t0 := time.Now()
	tick := time.NewTicker(time.Second)
	defer tick.Stop()
	fresh := make(chan *statsResp, 1)
	polling, lastPoll := false, time.Now()
	var samples []sample
	spin := 0
loop:
	for {
		select {
		case <-sig:
			break loop
		case <-e.ctx.Done():
			break loop
		case m := <-e.events:
			u.println(m)
		case ns := <-fresh:
			polling = false
			if ns != nil {
				u.news(ns, false)
				s = ns
			}
		case now := <-tick.C:
			spin++
			samples = append(samples, sample{now, e.hexDone.Load()})
			for len(samples) > 2 && now.Sub(samples[0].t) > 20*time.Second {
				samples = samples[1:]
			}
			rate := 0.0
			if f, l := samples[0], samples[len(samples)-1]; l.t.After(f.t) {
				rate = float64(l.n-f.n) / l.t.Sub(f.t).Seconds() * 60 * gamma
			}
			if !polling && now.Sub(lastPoll) >= 10*time.Second {
				polling, lastPoll = true, now
				go func() {
					c, cancel := context.WithTimeout(context.Background(), 30*time.Second)
					defer cancel()
					ns, err := a.stats(c, "all")
					if err != nil {
						ns = nil
					}
					fresh <- ns
				}()
			}
			u.status(statusLine(e, s, rate, spin))
		}
	}

	e.stop.Store(true)
	e.cancel()
	u.clear()
	fmt.Println("stopping, sending finished work (ctrl+c again quits at once)")
	done := make(chan struct{})
	go func() {
		wg.Wait()
		e.subs.Wait()
		close(done)
	}()
	select {
	case <-done:
	case <-sig:
	case <-time.After(45 * time.Second):
	}
	e.mu.Lock()
	fatal := e.fatal
	e.mu.Unlock()
	fmt.Printf("this run: %s, %s digits computed, %s accepted", time.Since(t0).Round(time.Second),
		compact(float64(e.hexDone.Load())*gamma), compact(float64(e.accepted.Load())*gamma))
	if n := e.convd.Load(); n > 0 {
		fmt.Printf(", %s converted to decimal", compact(float64(n)))
	}
	fmt.Println()
	if fatal != "" {
		fmt.Println(fatal)
		return 1
	}
	return 0
}

func cmdStats(a *api) int {
	ctx, cancel := context.WithTimeout(context.Background(), time.Minute)
	defer cancel()
	s, err := a.stats(ctx, "all")
	if err != nil {
		fmt.Println("cannot reach pi.php:", err)
		return 1
	}
	fmt.Printf("pi.txt    %s decimal digits from %s verified hex digits\n", commas(s.Digits), commas(s.Hex))
	if s.PerMin > 0 {
		fmt.Printf("growing   %s digits a minute\n", compact(s.PerMin))
	}
	fmt.Printf("people    %s online, %s have contributed\n", commas(s.Active), commas(s.Ever))
	fmt.Printf("checked   %s slices spot-checked by other computers\n", commas(s.Checked))
	if t := s.Tail; t != "" {
		if len(t) > 16 {
			t = t[len(t)-16:]
		}
		fmt.Printf("ends      ...%s\n", t)
	}
	if y := s.You; y != nil {
		name := y.Name
		if name == "" {
			name = "anonymous"
		}
		fmt.Printf("you       %s, %s digits", name, compact(float64(y.D)*gamma))
		if y.Name != "" && y.Rank > 0 {
			fmt.Printf(", #%d", y.Rank)
		}
		if L := level(float64(y.D) * gamma); L >= 0 {
			fmt.Printf(", level %d (%s)", L+1, records[L].name)
		}
		if y.CV > 0 {
			fmt.Printf(", %s converted", compact(float64(y.CV)))
		}
		fmt.Println()
	}
	fmt.Println()
	printBoard(s, false)
	return 0
}

func cmdTop(a *api, day bool) int {
	w := "all"
	if day {
		w = "day"
	}
	ctx, cancel := context.WithTimeout(context.Background(), time.Minute)
	defer cancel()
	s, err := a.stats(ctx, w)
	if err != nil {
		fmt.Println("cannot reach pi.php:", err)
		return 1
	}
	printBoard(s, day)
	return 0
}

var nameRe = regexp.MustCompile(`^[A-Za-z0-9][A-Za-z0-9 ._-]{0,15}$`)

func cmdName(a *api, name string) int {
	name = strings.Join(strings.Fields(name), " ")
	if name != "" && !nameRe.MatchString(name) {
		fmt.Println("a name is 1 to 16 letters, digits, spaces, dots, dashes or underscores, starting with a letter or digit")
		return 2
	}
	ctx, cancel := context.WithTimeout(context.Background(), time.Minute)
	defer cancel()
	var r nameResp
	body := map[string]interface{}{"sid": a.sid, "k": a.key, "name": name}
	if err := a.call(ctx, "POST", "?a=name", body, &r); err != nil {
		fmt.Println("cannot reach pi.php:", err)
		return 1
	}
	switch {
	case r.OK && r.Name == "":
		fmt.Println("saved: you are anonymous")
	case r.OK:
		fmt.Println("saved: you are listed as", r.Name)
	case r.Err == "taken":
		fmt.Println("taken, or too close to a name in use")
		return 1
	default:
		fmt.Println("pi.php said:", r.Err)
		return 1
	}
	return 0
}

func cmdCode(c *config) int {
	fmt.Println(c.SID + "-" + c.Key)
	fmt.Fprintln(os.Stderr, "keep it secret, it signs in as you. On the website open \"your name\" and paste it into \"use code\".")
	return 0
}

func cmdLogin(c *config, code, srv string) int {
	var b strings.Builder
	for _, r := range strings.ToLower(code) {
		if (r >= '0' && r <= '9') || (r >= 'a' && r <= 'f') {
			b.WriteRune(r)
		}
	}
	h := b.String()
	if len(h) != 48 {
		fmt.Println("a login code has 48 letters and digits: on the website open \"your name\", then \"show my code\"")
		return 2
	}
	if h[:16] == c.SID && h[16:] == c.Key {
		fmt.Println("that is already this computer's login")
		return 0
	}
	fmt.Printf("previous login code, in case you want it back: %s-%s\n", c.SID, c.Key)
	c.SID, c.Key = h[:16], h[16:]
	if err := c.save(); err != nil {
		fmt.Println("could not save:", err)
		return 1
	}
	if srv == "" {
		fmt.Println("saved")
		return 0
	}
	ctx, cancel := context.WithTimeout(context.Background(), time.Minute)
	defer cancel()
	s, err := newAPI(srv, c.SID, c.Key, 1).stats(ctx, "all")
	switch {
	case err != nil:
		fmt.Println("saved, but pi.php could not be reached to confirm:", err)
	case s.You == nil:
		fmt.Println("saved, but pi.php turned this code down (wrong key, or banned)")
		return 1
	case s.You.Name != "":
		fmt.Printf("signed in as %s, with %s digits\n", s.You.Name, compact(float64(s.You.D)*gamma))
	default:
		fmt.Println("signed in (no name yet:  pi name NAME)")
	}
	return 0
}

func cmdFind(a *api, q string) int {
	q = strings.Map(func(r rune) rune {
		if r >= '0' && r <= '9' {
			return r
		}
		return -1
	}, q)
	if len(q) < 1 || len(q) > 20 {
		fmt.Println("give 1 to 20 digits, like a birthday:  pi find 140396")
		return 2
	}
	ctx, cancel := context.WithTimeout(context.Background(), time.Minute)
	defer cancel()
	var r findResp
	if err := a.call(ctx, "GET", "?a=find&q="+q+"&from=0", nil, &r); err != nil {
		fmt.Println("cannot reach pi.php:", err)
		return 1
	}
	if r.Err != "" {
		fmt.Println("pi.php said:", r.Err)
		return 1
	}
	if r.At < 1 {
		fmt.Printf("not in the first %s digits yet\n", commas(r.N))
		return 0
	}
	fmt.Printf("found at digit %s of %s\n", commas(r.At), commas(r.N))
	if c, k, L := r.Ctx, r.K, len(q); k >= 0 && k+L <= len(c) {
		fmt.Printf("  ...%s[%s]%s...\n", c[:k], c[k:k+L], c[k+L:])
	}
	return 0
}

func cmdSelftest(a *api, online bool) int {
	failed := false
	for _, c := range localChecks(true) {
		t0 := time.Now()
		if err := c.run(); err != nil {
			failed = true
			fmt.Printf("FAIL  %s: %v\n", c.name, err)
		} else {
			fmt.Printf("ok    %s (%.1fs)\n", c.name, time.Since(t0).Seconds())
		}
	}
	if online {
		ctx, cancel := context.WithTimeout(context.Background(), 2*time.Minute)
		defer cancel()
		s, err := a.stats(ctx, "all")
		if err == nil {
			err = remoteCheck(ctx, a, s.Hex)
		}
		switch {
		case err == nil:
			fmt.Println("ok    random positions match pi.hex on the server")
		case errors.Is(err, errMismatch):
			failed = true
			fmt.Println("FAIL ", err)
		default:
			fmt.Println("skip  could not compare with the server:", err)
		}
	}
	if failed {
		return 1
	}
	fmt.Println("this build computes the same digits as the website")
	return 0
}

func cmdBench(a *api, online bool, threads int) int {
	p := int64(1000000)
	if online {
		ctx, cancel := context.WithTimeout(context.Background(), 30*time.Second)
		if s, err := a.stats(ctx, "all"); err == nil && s.Hex > 1000 {
			p = s.Hex
		}
		cancel()
	}
	fmt.Printf("timing evaluations at hex position %s on %d threads for about 10 seconds...\n", commas(p), threads)
	rates := make([]float64, threads)
	var wg sync.WaitGroup
	for i := 0; i < threads; i++ {
		wg.Add(1)
		go func(i int) {
			defer wg.Done()
			t0 := time.Now()
			n := 0
			for n == 0 || time.Since(t0) < 10*time.Second {
				evalX(p+8*int64(1000*i+n), nil)
				n++
			}
			rates[i] = float64(n) / time.Since(t0).Seconds()
		}(i)
	}
	wg.Wait()
	sum := 0.0
	for _, r := range rates {
		sum += r
	}
	fmt.Printf("%.1f ms an evaluation per thread, %.1f evaluations a second in all\n", 1000*float64(threads)/sum, sum)
	fmt.Printf("about %s decimal digits a minute at this depth, before job overhead\n", compact(sum*8*60*gamma))
	return 0
}

/* ---------- settings and login ---------- */

type config struct {
	Server string `json:"server,omitempty"`
	SID    string `json:"sid"`
	Key    string `json:"key"`
}

var (
	sidRe = regexp.MustCompile(`^[0-9a-f]{16}$`)
	keyRe = regexp.MustCompile(`^[0-9a-f]{32}$`)
)

func configPath() string {
	dir, err := os.UserConfigDir()
	if err != nil || dir == "" {
		dir, _ = os.UserHomeDir()
	}
	return filepath.Join(dir, "pi-cli", "config.json")
}

func loadConfig() *config {
	c := &config{}
	if b, err := os.ReadFile(configPath()); err == nil {
		_ = json.Unmarshal(b, c)
	}
	return c
}

func (c *config) save() error {
	p := configPath()
	if err := os.MkdirAll(filepath.Dir(p), 0o700); err != nil {
		return err
	}
	b, err := json.MarshalIndent(c, "", "  ")
	if err != nil {
		return err
	}
	return os.WriteFile(p, append(b, '\n'), 0o600)
}

// a public id and a secret key, the same shape a browser makes
func (c *config) ensureID() bool {
	changed := false
	if !sidRe.MatchString(c.SID) {
		c.SID, changed = rnd(8), true
	}
	if !keyRe.MatchString(c.Key) {
		c.Key, changed = rnd(16), true
	}
	return changed
}

func rnd(n int) string {
	b := make([]byte, n)
	if _, err := rand.Read(b); err != nil {
		panic(err)
	}
	return hex.EncodeToString(b)
}

func normServer(s string) string {
	s = strings.TrimSpace(s)
	if s == "" {
		return ""
	}
	if !strings.Contains(s, "://") {
		s = "https://" + s
	}
	u, err := url.Parse(s)
	if err != nil || u.Host == "" {
		return s
	}
	u.RawQuery, u.Fragment = "", ""
	if u.Path == "" {
		u.Path = "/"
	}
	return u.String()
}

/* ---------- small helpers ---------- */

func commas(n int64) string {
	s := strconv.FormatInt(n, 10)
	neg := strings.HasPrefix(s, "-")
	if neg {
		s = s[1:]
	}
	var b strings.Builder
	for i, c := range s {
		if i > 0 && (len(s)-i)%3 == 0 {
			b.WriteByte(',')
		}
		b.WriteRune(c)
	}
	if neg {
		return "-" + b.String()
	}
	return b.String()
}

// like the page's compact numbers: 9,999 then 12.3K, 4.56M, 1.2B
func compact(x float64) string {
	if x < 10000 {
		return commas(int64(math.Round(x)))
	}
	units := []string{"K", "M", "B", "T"}
	u := -1
	for x >= 999.5 && u < len(units)-1 {
		x /= 1000
		u++
	}
	prec := 0
	if x < 9.995 {
		prec = 2
	} else if x < 99.95 {
		prec = 1
	}
	s := strconv.FormatFloat(x, 'f', prec, 64)
	if strings.Contains(s, ".") {
		s = strings.TrimRight(strings.TrimRight(s, "0"), ".")
	}
	return s + units[u]
}

func sleepCtx(ctx context.Context, d time.Duration) {
	if d <= 0 {
		return
	}
	t := time.NewTimer(d)
	defer t.Stop()
	select {
	case <-t.C:
	case <-ctx.Done():
	}
}

func isTTY() bool {
	fi, err := os.Stdout.Stat()
	return err == nil && fi.Mode()&os.ModeCharDevice != 0
}

func usage() {
	fmt.Printf(`pi-cli %s: computes digits of pi for a pi.php site, on every core

usage: pi [command] [flags]

  run             compute and submit until ctrl+c (what plain "pi" does)
  stats           the shared pi.txt, your numbers and the leaderboard
  top [-day]      the leaderboard, all time or the last 24 hours
  name NAME       set your leaderboard name (pi name "" goes anonymous)
  code            print this computer's login code, to use it in a browser
  login CODE      use a login code from the website, so both count as one name
  find DIGITS     look for a digit string in pi.txt
  selftest        check this build's arithmetic against known digits
  bench           measure speed at the current depth

  -server URL     your pi.php, like https://example.com/pi.php (remembered)
  -t, -threads N  compute threads (default: all %d cores)
  -p, -power P    percent of each thread's time to use, 5 to 100 (default 100)
  -no-convert     never take decimal conversion jobs
  -day            with top: the last 24 hours

settings and your login are kept in %s
`, version, runtime.NumCPU(), configPath())
}

/* ---------- main ---------- */

func realMain() int {
	cmd, args, explicit := "run", os.Args[1:], false
	if len(args) > 0 && !strings.HasPrefix(args[0], "-") {
		cmd, args, explicit = args[0], args[1:], true
	}
	var (
		server      string
		threads     int
		power       int
		noConv, day bool
	)
	fs := flag.NewFlagSet("pi", flag.ContinueOnError)
	fs.Usage = usage
	fs.StringVar(&server, "server", "", "")
	fs.IntVar(&threads, "threads", runtime.NumCPU(), "")
	fs.IntVar(&threads, "t", runtime.NumCPU(), "")
	fs.IntVar(&power, "power", 100, "")
	fs.IntVar(&power, "p", 100, "")
	fs.BoolVar(&noConv, "no-convert", false, "")
	fs.BoolVar(&day, "day", false, "")
	if err := fs.Parse(args); err != nil {
		if errors.Is(err, flag.ErrHelp) {
			return 0
		}
		return 2
	}
	rest := fs.Args()
	if !explicit && len(rest) > 0 { // flags first, then the command: pi -server X top
		cmd = rest[0]
		if err := fs.Parse(rest[1:]); err != nil {
			return 2
		}
		rest = fs.Args()
	}

	c := loadConfig()
	changed := c.ensureID()
	srv := ""
	switch {
	case server != "":
		srv = normServer(server)
		if srv != c.Server {
			c.Server, changed = srv, true
		}
	case os.Getenv("PI_SERVER") != "":
		srv = normServer(os.Getenv("PI_SERVER"))
	case c.Server != "":
		srv = c.Server
	default:
		srv = normServer(DefaultServer)
	}
	if changed {
		if err := c.save(); err != nil {
			fmt.Fprintln(os.Stderr, "warning: could not save settings:", err)
		}
	}
	if threads < 1 {
		threads = 1
	}
	if threads > 512 {
		threads = 512
	}
	if power < 5 {
		power = 5
	}
	if power > 100 {
		power = 100
	}
	a := newAPI(srv, c.SID, c.Key, threads)
	need := func() bool {
		if srv != "" {
			return true
		}
		fmt.Println("no server yet. Run this once and it is remembered:")
		fmt.Println("  pi -server https://your-site.example/pi.php")
		return false
	}

	switch cmd {
	case "run":
		if !need() {
			return 2
		}
		return cmdRun(a, threads, power, !noConv)
	case "stats":
		if !need() {
			return 2
		}
		return cmdStats(a)
	case "top":
		if !need() {
			return 2
		}
		return cmdTop(a, day)
	case "name":
		if len(rest) == 0 {
			fmt.Println(`usage: pi name NAME   (pi name "" goes anonymous)`)
			return 2
		}
		if !need() {
			return 2
		}
		return cmdName(a, strings.Join(rest, " "))
	case "code":
		return cmdCode(c)
	case "login":
		if len(rest) == 0 {
			fmt.Println("usage: pi login CODE")
			return 2
		}
		return cmdLogin(c, strings.Join(rest, ""), srv)
	case "find":
		if !need() {
			return 2
		}
		return cmdFind(a, strings.Join(rest, ""))
	case "selftest":
		return cmdSelftest(a, srv != "")
	case "bench":
		return cmdBench(a, srv != "", threads)
	case "version":
		fmt.Println("pi-cli", version)
		return 0
	case "help":
		usage()
		return 0
	}
	fmt.Printf("unknown command %q\n\n", cmd)
	usage()
	return 2
}

func main() {
	code := realMain()
	if code != 0 && runtime.GOOS == "windows" && len(os.Args) == 1 {
		// probably started by a double click: keep the window open long enough to read why
		fmt.Print("\npress enter to close ")
		bufio.NewReader(os.Stdin).ReadString('\n')
	}
	os.Exit(code)
}
