#!/usr/bin/env bash
# Build the sub-800 Lean files in dependency order against the 1419 package's Mathlib and AKS
# build (`upper-bound/best`). Each module's .olean goes to ./build so later files can import it.
#   usage: bash build.sh [Module ...]      (default: all, in order)
set -euo pipefail
here="$(cd "$(dirname "$0")" && pwd)"
best="$here/../../../best"
# Read-only sources compiled from the tapered experiment (never modified here).
ext="$here/../../tapered"
mkdir -p "$here/build"
mods=("$@")
if [ ${#mods[@]} -eq 0 ]; then
  mods=(NegAssoc Ville LayerCake RowMgf Pushforward Round2Det Round2Col Round2Fixed Round2Union Round1 ExpBounds NumGlue Round1Num CellLemmas R1Cells Round2Num CellLemmas2 R2Cells F2D F2DR1 F2DSR F2DR2 F2DR2b F2DR2c F2DR2d F2DCells F2DBounds Fringe406109 Fringe7934 R1Sched R1Wire R1Exec R1NodeSpec R1Window R1BadSend R1Kernel R1Lemma41 R1FringeSend R1StageKernel R1Fields R1Induction PrefixPadding VariableSeparator AnyCutBounds RectanglePadding PaddedSeparator PaddedFringe TruncatedScrambleMeasure BaselineFringeD SepExists)
fi
winbuild="$(cygpath -w "$here/build" 2>/dev/null || echo "$here/build")"
lp="$(cd "$best" && lake env printenv LEAN_PATH)"
for m in "${mods[@]}"; do
  if [ -f "$here/$m.lean" ]; then dir="$here"
  elif [ -f "$ext/$m.lean" ]; then dir="$ext"
  else continue; fi
  echo "== $m"
  src="$(cygpath -w "$dir/$m.lean" 2>/dev/null || echo "$dir/$m.lean")"
  (cd "$best" && LEAN_PATH="$lp;$winbuild" lean --root="$(cygpath -w "$dir")" -o "$winbuild/$m.olean" "$src")
done
