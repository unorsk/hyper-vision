#!/usr/bin/env sh
# Records docs/demo.gif with VHS; scripts/drive.py supplies the mouse and keyboard input.
# Needs vhs (with ttyd and ffmpeg) and python3.
set -eu
cd "$(dirname "$0")/.."
lake build hyper-vision-demo
vhs docs/demo.tape
