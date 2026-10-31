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

## Run

    pi                 compute until ctrl+c
    pi login CODE      use your website login (your name, then "show my code") so both count as one name
    pi name NAME       or pick a name for this computer
    pi top             the leaderboard
    pi help            everything else

- **Mac:** first run `chmod +x pi-macos-arm64 && xattr -d com.apple.quarantine pi-macos-arm64`, then `./pi-macos-arm64`.
- **Windows:** SmartScreen may warn about an unknown app. Choose "More info", then "Run anyway".
