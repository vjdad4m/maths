#!/usr/bin/env bash
set -euo pipefail
project="$(cd "$(dirname "$0")" && pwd)"
workspace="$(dirname "$project")"
scratch="$(mktemp -d)"
trap 'rm -rf "$scratch"' EXIT
repository="${1:-$workspace}"

if [[ -f "$workspace/graff199-k3-integration-codex/env.sh" ]]; then
  export GRAFF199_OBJ="$scratch"
  source "$workspace/graff199-k3-integration-codex/env.sh"
else
  : "${GRAFF199_MATHLIB:?Set GRAFF199_MATHLIB to the pinned Mathlib checkout}"
  mathlib="$GRAFF199_MATHLIB"
  if [[ -n "${GRAFF199_LEAN_BIN:-}" ]]; then
    export PATH="$GRAFF199_LEAN_BIN:$PATH"
  fi
  export LEAN_PATH="$scratch:$mathlib/.lake/build/lib/lean"
  for package in "$mathlib"/.lake/packages/*; do
    if [[ -d "$package/.lake/build/lib/lean" ]]; then
      export LEAN_PATH="$LEAN_PATH:$package/.lake/build/lib/lean"
    fi
  done
fi

version="$(lean --version)"
printf '%s\n' "$version"
[[ "$version" == *"version 4.19.0,"* ]]
revision="$(git -C "$mathlib" rev-parse HEAD)"
printf 'Mathlib revision %s\n' "$revision"
[[ "$revision" == c44e0c8ee63ca166450922a373c7409c5d26b00b ]]

compile() {
  local source="$1" output="$2" module_root="$3"
  printf 'Checking %s\n' "$(basename "$source")"
  lean --root="$module_root" -j1 -s 65536 -DwarningAsError=true -o "$output" "$source"
}

check_sha() {
  printf '%s  %s\n' "$1" "$2" | sha256sum --check
}

hamiltonian=Mathlib/Combinatorics/SimpleGraph/Hamiltonian
if [[ ! -f "$mathlib/.lake/build/lib/lean/$hamiltonian.olean" ]]; then
  cp -as "$mathlib/.lake/build/lib/lean/Mathlib" "$scratch/Mathlib"
  mkdir -p "$scratch/$(dirname "$hamiltonian")"
  compile "$mathlib/$hamiltonian.lean" "$scratch/$hamiltonian.olean" "$mathlib"
fi
while IFS=$'\t' read -r published hash local_package imports; do
  [[ "$published" == public_path ]] && continue
  if [[ -n "$repository" ]]; then
    source_file="$repository/$published"
  else
    matches=("$workspace"/publish199-*/"$published")
    source_file="${matches[0]}"
  fi
  check_sha "$hash" "$source_file"
  name="$(basename "$published" .lean)"
  compile "$source_file" "$scratch/$name.olean" "$(dirname "$source_file")"
done < "$project/PublishedSources.tsv"
while IFS=$'\t' read -r name hash imports; do
  [[ "$name" == source ]] && continue
  check_sha "$hash" "$project/$name"
  compile "$project/$name" "$scratch/${name%.lean}.olean" "$project"
done < "$project/SourceManifest.tsv"
printf '%s\n' 'Strict high-cut insertion source replay passed.'
