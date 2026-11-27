#!/usr/bin/env bash
set -euo pipefail
here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
build="$(mktemp -d)"
trap 'rm -rf "$build"' EXIT
mkdir "$build/src" "$build/obj"
base64 -d "$here/lean-dependencies.tar.gz.b64" | tar -xz -C "$build/src"
cp "$here"/src/*.lean "$build/src/"
(cd "$build/src" && sha256sum -c "$here/sha256sums.txt" >/dev/null)
export LEAN_PATH="$build/obj${LEAN_PATH:+:$LEAN_PATH}"
lean --version
while IFS= read -r module; do
  lean -j1 -s 65536 -DwarningAsError=true --root="$build/src" -o "$build/obj/$module.olean" "$build/src/$module.lean"
done < "$here/modules.txt"
