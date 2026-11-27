#!/usr/bin/env bash
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
: "${GENG:=geng}"
out=$(mktemp -d "${TMPDIR:-/tmp}/odd-block-search.XXXXXXXX")
c++ -O3 -std=c++20 "$here/CutScan.cpp" -o "$out/cutscan"
c++ -O3 -std=c++20 "$here/WingScan.cpp" -o "$out/wingscan"
for n in 4 5 6 7 8 9; do "$GENG" -Cq "$n" | "$out/cutscan"; done > "$out/cutscan.log"
for n in 3 4 5 6 7; do "$GENG" -Cq "$n" | "$out/wingscan" --ports; done > "$out/wings7.g6"
"$out/wingscan" < "$out/wings7.g6" > "$out/wings7.log"
"$GENG" -Cq 8 | "$out/wingscan" --ports | "$out/wingscan" --pendant > "$out/pendant8.log"
"$GENG" -Cq 9 | "$out/wingscan" --raw-ports | "$out/wingscan" --pendant > "$out/pendant9.log"
for f in cutscan wings7 pendant8 pendant9; do diff -u "$here/$f.log" "$out/$f.log"; cat "$out/$f.log"; done
