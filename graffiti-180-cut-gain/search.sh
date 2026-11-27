#!/usr/bin/env bash
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
: "${GENG:=geng}"
out=$(mktemp -d "${TMPDIR:-/tmp}/cut-gain-search.XXXXXXXX")
c++ -O3 -Wall -Wextra -Werror -std=c++20 "$here/MarkSearch.cpp" -o "$out/marks"
for n in 3 4 5 6 7 8; do "$GENG" -Cq "$n"; done | "$out/marks" > "$out/marks3-8.log"
"$GENG" -Cq 9 | "$out/marks" > "$out/marks9.log"
"$GENG" -Cq 10 10:15 | "$out/marks" > "$out/marks10.log"
"$out/marks" < "$here/historical.g6" > "$out/historical.log"
for f in marks3-8 marks9 marks10 historical; do
  diff -u "$here/$f.log" "$out/$f.log"
  cat "$out/$f.log"
done
