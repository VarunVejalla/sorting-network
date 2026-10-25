import AKS.Bounds.FiniteLower
import AKS.Bounds.KahaleUnconditional

/-! Kernel dependency checks for the finite bounds (LB-01) and the
upper-bound-free asymptotic statements (LB-11). -/

/-- info: 'SortingDepth.minimum_ge_max_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms SortingDepth.minimum_ge_max_bounds
/-- info: 'SortingDepth.factorial_le_two_pow_depth_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms SortingDepth.factorial_le_two_pow_depth_mul
/-- info: 'SortingDepth.le_two_pow_depth' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms SortingDepth.le_two_pow_depth
/-- info: 'SortingDepth.two_mul_sub_two_le_minimum_two_pow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms SortingDepth.two_mul_sub_two_le_minimum_two_pow
/-- info: 'SortingDepth.minimum_two_pow_sixteen_ge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms SortingDepth.minimum_two_pow_sixteen_ge
/-- info: 'SortingDepth.eventually_mul_logb_le_minimum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms SortingDepth.eventually_mul_logb_le_minimum
/-- info: 'SortingDepth.ereal_liminf_minimum_div_logb_ge_kahale' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms SortingDepth.ereal_liminf_minimum_div_logb_ge_kahale
/-- info: 'SortingDepth.liminf_minimum_div_logb_ge_kahale_of_cobounded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms SortingDepth.liminf_minimum_div_logb_ge_kahale_of_cobounded

/-! The new statements do not use any upper-bound construction: their constant
closures avoid the legacy `minimum_depth_le` and the coboundedness lemma built on it. -/

open Lean in
/-- Does the transitive constant closure of `root` mention `target`? -/
private partial def closureMentions (env : Environment) (target root : Name) : Bool :=
  (go [root] {}).1
where
  go : List Name → NameSet → Bool × NameSet
    | [], seen => (false, seen)
    | n :: rest, seen =>
      if n == target then (true, seen)
      else if seen.contains n then go rest seen
      else
        let deps := match env.find? n with
          | some ci => ci.getUsedConstantsAsSet.toList
          | none => []
        go (deps ++ rest) (seen.insert n)

open Lean Elab Command in
elab "#guard_avoids " root:ident target:ident : command => do
  let env ← getEnv
  let r ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo root
  let t ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo target
  if closureMentions env t r then
    throwError "{r} depends on {t}"

#guard_avoids SortingDepth.eventually_mul_logb_le_minimum SortingDepth.minimum_depth_le
#guard_avoids SortingDepth.ereal_liminf_minimum_div_logb_ge_kahale SortingDepth.minimum_depth_le
#guard_avoids SortingDepth.liminf_minimum_div_logb_ge_kahale_of_cobounded
  SortingDepth.minimum_depth_le
#guard_avoids SortingDepth.minimum_ge_max_bounds SortingDepth.minimum_depth_le
#guard_avoids SortingDepth.minimum_two_pow_sixteen_ge SortingDepth.minimum_depth_le
#guard_avoids SortingDepth.eventually_minimum_depth_ge_kahale_logb SortingDepth.minimum_depth_le
