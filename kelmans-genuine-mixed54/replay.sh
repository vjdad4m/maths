#!/usr/bin/env bash
set -euo pipefail
here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
checkout="${MATHS_REPO_ROOT:-$(cd "$here/.." && pwd)}"
if (( $# > 1 )) || [[ -n "${1:-}" && "$1" != '--fixtures' ]]; then
  echo 'usage: bash replay.sh [--fixtures]' >&2
  exit 2
fi
build="$(mktemp -d)"
trap 'rm -rf "$build"' EXIT
export LEAN_PATH="$build${LEAN_PATH:+:$LEAN_PATH}"

version="$(lean --version)"
printf '%s\n' "$version"
[[ "$version" == *'version 4.19.0'* ]] || {
  echo 'This package requires Lean 4.19.0.' >&2
  exit 2
}
compile() {
  local source="$1" module="$2"
  printf '\n=== %s ===\n' "$module"
  lean -j1 -s65536 -DElab.async=false -DwarningAsError=true \
    --root="$(dirname "$source")" -o "$build/$module.olean" "$source"
}
replay_dependencies() {
  local list="$1" expected path source module
  while read -r expected path; do
    [[ -z "${expected:-}" || "$expected" == \#* ]] && continue
    source="$checkout/$path"
    if [[ ! -f "$source" ]] || [[ "$(git hash-object "$source")" != "$expected" ]]; then
      echo "Missing or nonmatching upstream source: $path" >&2
      exit 2
    fi
    module="$(basename "$source" .lean)"
    [[ -f "$build/$module.olean" ]] || compile "$source" "$module"
  done < "$list"
}
(cd "$here" && sha256sum -c sources.sha256)
replay_dependencies "$here/dependencies.tsv"
while IFS= read -r module; do
  [[ -z "$module" ]] || compile "$here/src/$module.lean" "$module"
done < "$here/modules.txt"
if [[ "${1:-}" == '--fixtures' ]]; then
  replay_dependencies "$here/fixture-dependencies.tsv"
  while IFS= read -r module; do
    [[ -z "$module" ]] || compile "$here/fixtures/$module.lean" "$module"
  done < "$here/fixture-modules.txt"
fi
