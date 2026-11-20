#!/bin/sh
# build-all.sh: puts a binary for each platform in dist/
set -e
mkdir -p dist
for t in linux/amd64 linux/arm64 darwin/amd64 darwin/arm64 windows/amd64 windows/arm64; do
  os=${t%/*}; arch=${t#*/}; name=$os; ext=
  [ "$os" = darwin ] && name=macos
  [ "$os" = windows ] && ext=.exe
  CGO_ENABLED=0 GOOS=$os GOARCH=$arch go build -trimpath -ldflags "-s -w" -o "dist/pi-$name-$arch$ext" .
done
