module

public import AKS.Sort.Defs
public import AKS.Sort.Depth
public import AKS.Sort.Monotone

/-! Untangling generalized comparator networks (Knuth TAOCP 5.3.4, ex. 16): a generalized
network sorting into the output order `τ` converts to a standard sorting network of the same
greedy depth.  `untangleAux` walks the list with a wire permutation `p` (invariant
`G-state = S-state ∘ p`); the same invariant holds for wire times. -/

@[expose] public section

namespace Untangle

/-- Generalized comparator: minimum goes to wire `a`, maximum to wire `b`. -/
structure GenComparator (n : ℕ) where
  a : Fin n
  b : Fin n
  hab : a ≠ b

/-- Generalized comparator network. -/
structure GenNetwork (n : ℕ) where
  comparators : List (GenComparator n)

def GenComparator.apply {n : ℕ} {α : Type*} [LinearOrder α]
    (c : GenComparator n) (v : Fin n → α) : Fin n → α :=
  fun k ↦
    if k = c.a then min (v c.a) (v c.b)
    else if k = c.b then max (v c.a) (v c.b)
    else v k

def GenNetwork.exec {n : ℕ} {α : Type*} [LinearOrder α]
    (net : GenNetwork n) (v : Fin n → α) : Fin n → α :=
  net.comparators.foldl (fun acc c ↦ c.apply acc) v

def genDepthStep {n : ℕ} (state : (Fin n → ℕ) × ℕ) (c : GenComparator n) :
    (Fin n → ℕ) × ℕ :=
  let wt := state.1
  let t := max (wt c.a) (wt c.b) + 1
  (Function.update (Function.update wt c.a t) c.b t, max state.2 t)

/-- Greedy critical-path depth, as `ComparatorNetwork.depth`. -/
def GenNetwork.depth {n : ℕ} (net : GenNetwork n) : ℕ :=
  (net.comparators.foldl genDepthStep (fun _ ↦ 0, 0)).2

/-- One untangling step: the standard comparator and the updated permutation. -/
def stepU {n : ℕ} (p : Equiv.Perm (Fin n)) (g : GenComparator n) :
    Comparator n × Equiv.Perm (Fin n) :=
  if h : p g.a < p g.b then (⟨p g.a, p g.b, h⟩, p)
  else (⟨p g.b, p g.a, lt_of_le_of_ne (not_lt.1 h)
          (fun e ↦ g.hab (p.injective e.symm))⟩, p * Equiv.swap g.a g.b)

/-- The untangled comparator list and final permutation. -/
def untangleAux {n : ℕ} : Equiv.Perm (Fin n) → List (GenComparator n) →
    List (Comparator n) × Equiv.Perm (Fin n)
  | p, [] => ([], p)
  | p, g :: gs =>
    let s := stepU p g
    let r := untangleAux s.2 gs
    (s.1 :: r.1, r.2)

theorem step_apply {n : ℕ} {α : Type*} [LinearOrder α] (p : Equiv.Perm (Fin n))
    (g : GenComparator n) (x y : Fin n → α) (hx : ∀ k, x k = y (p k)) (k : Fin n) :
    g.apply x k = (stepU p g).1.apply y ((stepU p g).2 k) := by
  have hne : g.a ≠ g.b := g.hab
  unfold stepU
  by_cases h : p g.a < p g.b
  · simp only [h, dif_pos]
    simp only [GenComparator.apply, Comparator.apply, hx, p.injective.eq_iff]
  · simp only [h, dif_neg, not_false_eq_true]
    simp only [GenComparator.apply, Comparator.apply, hx, Equiv.Perm.mul_apply]
    by_cases ka : k = g.a
    · subst ka
      simp [Equiv.swap_apply_left, min_comm]
    · by_cases kb : k = g.b
      · subst kb
        simp [Equiv.swap_apply_right, max_comm, Ne.symm hne, hne]
      · rw [Equiv.swap_apply_of_ne_of_ne ka kb]
        simp [ka, kb, p.injective.eq_iff]

theorem untangleAux_exec {n : ℕ} {α : Type*} [LinearOrder α] :
    ∀ (gs : List (GenComparator n)) (p : Equiv.Perm (Fin n)) (x y : Fin n → α),
      (∀ k, x k = y (p k)) →
      ∀ k, gs.foldl (fun acc c ↦ c.apply acc) x k =
        (untangleAux p gs).1.foldl (fun acc c ↦ c.apply acc) y ((untangleAux p gs).2 k)
  | [], p, x, y, hx, k => by simp [untangleAux, hx]
  | g :: gs, p, x, y, hx, k => by
    simp only [List.foldl_cons, untangleAux]
    exact untangleAux_exec gs _ _ _ (fun k ↦ step_apply p g x y hx k) k

theorem step_depth {n : ℕ} (p : Equiv.Perm (Fin n)) (g : GenComparator n)
    (wG wS : Fin n → ℕ) (d : ℕ) (hw : ∀ k, wG k = wS (p k)) :
    (∀ k, (genDepthStep (wG, d) g).1 k = (depthStep (wS, d) (stepU p g).1).1
        ((stepU p g).2 k)) ∧
    (genDepthStep (wG, d) g).2 = (depthStep (wS, d) (stepU p g).1).2 := by
  have hne : g.a ≠ g.b := g.hab
  unfold stepU
  by_cases h : p g.a < p g.b
  · simp only [h, dif_pos]
    simp only [genDepthStep, depthStep, hw, Function.update_apply, p.injective.eq_iff]
    simp
  · simp only [h, dif_neg, not_false_eq_true]
    simp only [genDepthStep, depthStep, hw, Function.update_apply, Equiv.Perm.mul_apply]
    refine ⟨fun k ↦ ?_, by simp [max_comm]⟩
    by_cases ka : k = g.a
    · subst ka
      simp [Equiv.swap_apply_left, max_comm, hne]
    · by_cases kb : k = g.b
      · subst kb
        simp [Equiv.swap_apply_right, max_comm]
      · rw [Equiv.swap_apply_of_ne_of_ne ka kb]
        simp [ka, kb, p.injective.eq_iff]

theorem untangleAux_depth {n : ℕ} :
    ∀ (gs : List (GenComparator n)) (p : Equiv.Perm (Fin n)) (wG wS : Fin n → ℕ) (d : ℕ),
      (∀ k, wG k = wS (p k)) →
      (gs.foldl genDepthStep (wG, d)).2 =
        ((untangleAux p gs).1.foldl depthStep (wS, d)).2
  | [], p, wG, wS, d, hw => by simp [untangleAux]
  | g :: gs, p, wG, wS, d, hw => by
    simp only [List.foldl_cons, untangleAux]
    obtain ⟨h1, h2⟩ := step_depth p g wG wS d hw
    have := untangleAux_depth gs (stepU p g).2 (genDepthStep (wG, d) g).1
      (depthStep (wS, d) (stepU p g).1).1 (genDepthStep (wG, d) g).2 h1
    have e : depthStep (wS, d) (stepU p g).1 =
        ((depthStep (wS, d) (stepU p g).1).1, (genDepthStep (wG, d) g).2) :=
      Prod.ext rfl h2.symm
    rw [e]
    exact this

/-- Untangled standard network. -/
def untangleNet {n : ℕ} (G : GenNetwork n) : ComparatorNetwork n :=
  ⟨(untangleAux (1 : Equiv.Perm (Fin n)) G.comparators).1⟩

/-- The final permutation. -/
def untanglePerm {n : ℕ} (G : GenNetwork n) : Equiv.Perm (Fin n) :=
  (untangleAux (1 : Equiv.Perm (Fin n)) G.comparators).2

theorem untangle_exec {n : ℕ} {α : Type*} [LinearOrder α] (G : GenNetwork n)
    (v : Fin n → α) (k : Fin n) :
    G.exec v k = (untangleNet G).exec v (untanglePerm G k) :=
  untangleAux_exec G.comparators 1 v v (fun _ ↦ rfl) k

theorem untangle_depth {n : ℕ} (G : GenNetwork n) : (untangleNet G).depth = G.depth := by
  unfold untangleNet ComparatorNetwork.depth GenNetwork.depth
  exact (untangleAux_depth G.comparators 1 _ _ 0 (fun _ ↦ rfl)).symm

theorem untangle {n : ℕ} (G : GenNetwork n) (τ : Equiv.Perm (Fin n))
    (hG : ∀ (α : Type) [LinearOrder α] (v : Fin n → α),
      Monotone (fun r : Fin n => G.exec v (τ.symm r))) :
    ∃ S : ComparatorNetwork n, S.depth = G.depth ∧ ComparatorNetwork.Sorts.{0} S := by
  refine ⟨untangleNet G, untangle_depth G, ?_⟩
  set p := untanglePerm G
  have hmono : Monotone (fun r : Fin n => p (τ.symm r)) := by
    have h := hG (Fin n) id
    convert h using 2 with r
    rw [untangle_exec, ComparatorNetwork.exec_eq_of_monotone _ monotone_id]
    rfl
  have hid : ∀ r, p (τ.symm r) = r := by
    have hs : StrictMono (fun r : Fin n => p (τ.symm r)) :=
      hmono.strictMono_of_injective (p.injective.comp τ.symm.injective)
    have hr : Set.range (fun r : Fin n => p (τ.symm r)) = Set.range (id : Fin n → Fin n) := by
      have h1 : Function.Surjective (fun r : Fin n => p (τ.symm r)) :=
        p.surjective.comp τ.symm.surjective
      rw [h1.range_eq, Function.Surjective.range_eq Function.surjective_id]
    exact fun r => congrFun ((hs.range_inj strictMono_id).1 hr) r
  intro α _ v
  have : (untangleNet G).exec v = fun r => G.exec v (τ.symm r) := by
    funext r
    rw [untangle_exec, hid r]
  rw [this]
  exact hG α v

end Untangle
