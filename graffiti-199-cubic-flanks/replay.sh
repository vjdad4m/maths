#!/usr/bin/env bash
set -euo pipefail
project="$(cd "$(dirname "$0")" && pwd)"
workspace="$(dirname "$project")"
frozen="$workspace/graff199-k3-integration-codex"
scratch="$(mktemp -d)"
trap 'rm -rf "$scratch"' EXIT

mode="${1:---cached}"
case "$mode" in
  --cached|--from-source) ;;
  *) printf 'Usage: %s [--cached | --from-source [repository-root]]\n' "$0" >&2; exit 2 ;;
esac

if [[ -f "$frozen/env.sh" ]]; then
  export GRAFF199_OBJ="$scratch"
  source "$frozen/env.sh"
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

check_sha() {
  printf '%s  %s\n' "$1" "$2" | sha256sum --check --status
}
compile() {
  local source="$1" output="$2" module_root="$3"
  printf 'Checking %s\n' "$(basename "$source")"
  lean --root="$module_root" -j1 -s 65536 -DElab.async=false -DwarningAsError=true -o "$output" "$source"
}

if [[ "$mode" == --cached ]]; then
  declare -A seen
  rebuild=()
  while IFS=$'\t' read -r published hash package imports; do
    [[ "$published" == public_path ]] && continue
    name="$(basename "$published")"
    source_file="$workspace/$package/$name"
    check_sha "$hash" "$source_file"
    if [[ ! -f "$workspace/$package/obj/${name%.lean}.olean" ]]; then
      rebuild+=("$source_file")
    fi
    if [[ ! -v "seen[$package]" ]]; then
      export LEAN_PATH="$workspace/$package/obj:$LEAN_PATH"
      seen["$package"]=1
    fi
  done < "$project/PublishedSources.tsv"
  for source_file in "${rebuild[@]}"; do
    name="$(basename "$source_file" .lean)"
    compile "$source_file" "$scratch/$name.olean" "$(dirname "$source_file")"
  done
  printf 'Using %s source-hash-checked project dependencies.\n' \
    "$(($(wc -l < "$project/PublishedSources.tsv") - 1))"
else
  hamiltonian=Mathlib/Combinatorics/SimpleGraph/Hamiltonian
  if [[ ! -f "$mathlib/.lake/build/lib/lean/$hamiltonian.olean" ]]; then
    cp -as "$mathlib/.lake/build/lib/lean/Mathlib" "$scratch/Mathlib"
    mkdir -p "$scratch/$(dirname "$hamiltonian")"
    compile "$mathlib/$hamiltonian.lean" "$scratch/$hamiltonian.olean" "$mathlib"
  fi
  while IFS=$'\t' read -r published hash package imports; do
    [[ "$published" == public_path ]] && continue
    if [[ -n "${2:-}" ]]; then
      source_file="$2/$published"
    else
      matches=("$workspace"/publish199-*/"$published")
      source_file="${matches[0]}"
    fi
    check_sha "$hash" "$source_file"
    name="$(basename "$published" .lean)"
    compile "$source_file" "$scratch/$name.olean" "$(dirname "$source_file")"
  done < "$project/PublishedSources.tsv"
fi

while IFS=$'\t' read -r name hash imports; do
  [[ "$name" == source ]] && continue
  check_sha "$hash" "$project/$name"
  compile "$project/$name" "$scratch/${name%.lean}.olean" "$project"
done < "$project/SourceManifest.tsv"
printf '%s\n' 'Strict one-omission flank replay passed.'
