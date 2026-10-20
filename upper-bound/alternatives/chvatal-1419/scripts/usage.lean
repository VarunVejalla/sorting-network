import Lean
import AKS.Bounds.Chvatal1830Final

/-!
Declaration-level proof graph for the two headline theorems.

Run from `upper-bound/best/`:  `lake env lean scripts/usage.lean`

Writes
* `scripts/data/decls.txt`: `module|name|startLine|endLine|U or N` for every AKS definition,
  theorem, inductive or opaque with a source range (`U` = reachable from the headline theorems
  through types and values, `N` = not reachable);
* `scripts/data/edges.txt`: `from|to` for every direct dependency between AKS declarations.
Note: constants that only occur in tactic syntax (e.g. `simp only [foo]` arguments that act by
`rfl`) are not visible in proof terms; `scripts/prune_driver.py` adds a textual safety margin.
-/
open Lean Elab Command

def roots : List Name :=
  [`SortingDepth.minimum_depth_le_1770_logb, `SortingDepth.limsup_minimum_div_logb_le_1770]

def directDeps (env : Environment) (n : Name) : Array Name :=
  match env.find? n with
  | none => #[]
  | some ci =>
    let cs : Array Name := ci.type.getUsedConstants
    let cs := match ci.value? (allowOpaque := true) with
      | some v => cs ++ v.getUsedConstants
      | none => cs
    match ci with
    | .inductInfo i => cs ++ i.ctors.toArray
    | .ctorInfo c => cs.push c.induct
    | _ => cs

/-- Imported Mathlib/Lean modules precede AKS and cannot depend on its declarations.
Restricting traversal to AKS therefore preserves the project dependency closure. -/
def isAKS (env : Environment) (n : Name) : Bool :=
  match env.getModuleIdxFor? n with
  | some idx => (env.header.moduleNames[idx.toNat]!).getRoot == `AKS
  | none => false

partial def reach (env : Environment) (rs : List Name) :
    Std.HashSet Name × Std.HashMap Name (Array Name) := Id.run do
  let mut seen : Std.HashSet Name := {}
  let mut deps : Std.HashMap Name (Array Name) := {}
  let mut stack := rs
  while !stack.isEmpty do
    match stack with
    | [] => break
    | n :: rest =>
      stack := rest
      if seen.contains n then continue
      seen := seen.insert n
      let cs := directDeps env n
      deps := deps.insert n cs
      for c in cs do
        if isAKS env c && !seen.contains c then stack := c :: stack
  return (seen, deps)

run_cmd do
  let env ← getEnv
  for root in roots do
    unless (env.find? root).isSome do
      throwError "Unknown proof graph root: {root}"
  -- Compile-check the exporter without traversing proof terms or writing files.
  if (← IO.getEnv "AKS_GRAPH_SKIP_EXPORT") == some "1" then return
  let (used, deps) := reach env roots
  let mut decls : Array String := #[]
  let mut edges : Array String := #[]
  for (n, ci) in env.constants.map₁.toList do
    unless isAKS env n do continue
    unless (ci matches .thmInfo _) || (ci matches .defnInfo _) || (ci matches .inductInfo _) ||
        (ci matches .opaqueInfo _) do continue
    let r ← liftCoreM (findDeclarationRanges? n)
    let some dr := r | continue
    let m := env.header.moduleNames[(env.getModuleIdxFor? n).get!.toNat]!
    decls := decls.push s!"{m}|{n}|{dr.range.pos.line}|{dr.range.endPos.line}|{if used.contains n then "U" else "N"}"
    let cs := match deps[n]? with
      | some cs => cs
      | none => directDeps env n
    for c in cs do
      if isAKS env c then edges := edges.push s!"{n}|{c}"
  IO.FS.writeFile "scripts/data/decls.txt" ("\n".intercalate decls.toList)
  IO.FS.writeFile "scripts/data/edges.txt" ("\n".intercalate edges.toList)
