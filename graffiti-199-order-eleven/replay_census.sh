#!/usr/bin/env bash
set -euo pipefail
project="$(cd "$(dirname "$0")" && pwd)"
scratch="$(mktemp -d)"
trap 'rm -rf "$scratch"' EXIT
"${CXX:-g++}" -std=c++20 -O3 -Wall -Wextra -Werror "$project/census.cpp" -o "$scratch/census"
"$scratch/census" "$@"
