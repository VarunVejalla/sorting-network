#!/usr/bin/env bash
# Build the sub-800 Lean files in dependency order against the 1419 package's Mathlib and AKS
# build (`upper-bound/best`). Each module's .olean goes to ./build so later files can import it.
#   usage: bash build.sh [Module ...]      (default: all, in order)
set -euo pipefail
here="$(cd "$(dirname "$0")" && pwd)"
best="$here/../../../best"
mkdir -p "$here/build"
mods=("$@")
if [ ${#mods[@]} -eq 0 ]; then
  mods=(NegAssoc Ville LayerCake RowMgf Pushforward Round2Det Round2Col Round2Fixed Round2Union Round1 ExpBounds NumGlue Round1Num CellLemmas)
fi
winbuild="$(cygpath -w "$here/build" 2>/dev/null || echo "$here/build")"
lp="$(cd "$best" && lake env printenv LEAN_PATH)"
for m in "${mods[@]}"; do
  [ -f "$here/$m.lean" ] || continue
  echo "== $m"
  src="$(cygpath -w "$here/$m.lean" 2>/dev/null || echo "$here/$m.lean")"
  (cd "$best" && LEAN_PATH="$lp;$winbuild" lean --root="$(cygpath -w "$here")" -o "$winbuild/$m.olean" "$src")
done
