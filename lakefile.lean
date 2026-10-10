import Lake
open Lake DSL

/- Root project: shared Mathlib cache. Build each proof package separately;
   their AKS module names intentionally overlap. -/
package sorting_network where

require "leanprover-community" / "mathlib" @ git "master"
