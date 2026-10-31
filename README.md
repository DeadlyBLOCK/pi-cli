# pi-cli

Compute digits of pi for [deadlyblock.com/pi](https://deadlyblock.com/pi/) on every core of your computer.
It shares the website's leaderboard.

## Download

| System | File |
|---|---|
| Windows | [pi-windows-amd64.exe](https://github.com/DeadlyBLOCK/pi-cli/releases/latest/download/pi-windows-amd64.exe) |
| Mac (Apple Silicon) | [pi-macos-arm64](https://github.com/DeadlyBLOCK/pi-cli/releases/latest/download/pi-macos-arm64) |
| Mac (Intel) | [pi-macos-amd64](https://github.com/DeadlyBLOCK/pi-cli/releases/latest/download/pi-macos-amd64) |
| Linux | [pi-linux-amd64](https://github.com/DeadlyBLOCK/pi-cli/releases/latest/download/pi-linux-amd64) |

Other builds are on the [releases page](https://github.com/DeadlyBLOCK/pi-cli/releases/latest).

## Build it yourself

You need [Go](https://go.dev/dl/) 1.21 or newer. Nothing else is required: the program uses only Go's standard library.

1. Get the source, either with git:

       git clone https://github.com/DeadlyBLOCK/pi-cli.git
       cd pi-cli

   or by downloading **Code → Download ZIP** on this page and unzipping it.

2. Build for your own computer:

       go build -trimpath -ldflags "-s -w" -o pi .

   On Windows, use `-o pi.exe` instead.

3. Check your build before using it:

       ./pi selftest

   On Windows, run `pi.exe selftest`. Every line should say `ok`.
   The program also runs these checks each time it starts, and it won't submit anything if they fail.

### Building for other systems

Go can build for any platform from any platform. On macOS or Linux, set `GOOS` and `GOARCH`:

    GOOS=windows GOARCH=amd64 go build -trimpath -ldflags "-s -w" -o pi.exe .
    GOOS=darwin  GOARCH=arm64 go build -trimpath -ldflags "-s -w" -o pi-macos-arm64 .
    GOOS=linux   GOARCH=amd64 go build -trimpath -ldflags "-s -w" -o pi-linux-amd64 .

or build all six release files into `dist/` at once:

    sh build-all.sh

On Windows in PowerShell, set the variables first:

    $env:GOOS="linux"; $env:GOARCH="amd64"; go build -trimpath -ldflags "-s -w" -o pi-linux-amd64 .

### Using it with another server

The binary talks to `https://deadlyblock.com/pi/` by default. To use it with your own copy of pi.php, either change `DefaultServer` near the top of `main.go` before building, or run it once with:

    pi -server https://example.com/pi.php

The address you pass is remembered for later runs.

## Run

    pi                 compute until ctrl+c
    pi login CODE      use your website login (your name, then "show my code") so both count as one name
    pi name NAME       or pick a name for this computer
    pi top             the leaderboard
    pi help            everything else

- **Mac:** first run `chmod +x pi-macos-arm64 && xattr -d com.apple.quarantine pi-macos-arm64`, then `./pi-macos-arm64`.
- **Windows:** SmartScreen may warn about an unknown app. Choose "More info", then "Run anyway".
