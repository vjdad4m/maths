#!/usr/bin/env bash
set -euo pipefail
here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
lean --version
lean -j1 -DwarningAsError=true "$here/Lollipop.lean"
