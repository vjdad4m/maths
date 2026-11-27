#!/usr/bin/env bash
set -euo pipefail
src=$(cd -- "$(dirname -- "$0")" && pwd)
obj=$(mktemp -d)
trap 'rm -rf -- "$obj"' EXIT
export OBJDIR="$obj"
modules=(PowerBasis ChordalBasis DegreeBasis Book Forts)
names=(hit_twins subTotal_two_of_pair power_exact family567)
case ${1:-all} in
  567) ;;
  383|all)
    modules+=(PlaneBasis PlanarFamily)
    names+=(Drawing.bookDrawing Drawing.family383)
    ;;
  *) echo "Use replay.sh [567|383|all]" >&2; exit 2 ;;
esac
bash "$src/compile.sh" "${modules[@]}" | tee "$obj/axioms.log"
for name in "${names[@]}"; do
  grep -Fxq "'Book567.$name' depends on axioms: [propext, Classical.choice, Quot.sound]" "$obj/axioms.log"
done
