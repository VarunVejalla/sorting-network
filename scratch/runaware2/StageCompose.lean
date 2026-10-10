module

public import AKS.Chvatal.FinalSorts

@[expose] public section

/-! # Stage composition with inter-stage wire permutations (GenNetwork)

Stages `net_t : ComparatorNetwork N` interleaved with wire permutations `π_t`:
`x_{t+1} = net_t.exec (x_t ∘ π_t)`.  The conjugated stage `conjNet P net` has comparators
`(P i, P j)` (min to `P i`), so `(conjNet P net).exec y = (net.exec (y ∘ P)) ∘ P⁻¹`.  Conjugating
stage `t` by the cumulative permutation `P_t = π_0 * ... * π_t` gives a `GenNetwork` whose
execution is `x_T ∘ P_{T-1}⁻¹`; `Untangle.untangle` then turns it into a standard network of the
same depth. -/

namespace Untangle

variable {N : ℕ}

/-! ## Concatenation of generalized networks -/

def GenNetwork.append (G H : GenNetwork N) : GenNetwork N :=
  ⟨G.comparators ++ H.comparators⟩

theorem GenNetwork.exec_append {α : Type*} [LinearOrder α] (G H : GenNetwork N)
    (v : Fin N → α) : (G.append H).exec v = H.exec (G.exec v) := by
  simp [GenNetwork.exec, GenNetwork.append, List.foldl_append]

/-- The empty generalized network. -/
def GenNetwork.nil (N : ℕ) : GenNetwork N := ⟨[]⟩

theorem GenNetwork.exec_nil {α : Type*} [LinearOrder α] (v : Fin N → α) :
    (GenNetwork.nil N).exec v = v := rfl

theorem GenNetwork.depth_nil : (GenNetwork.nil N).depth = 0 := by
  simp [GenNetwork.nil, GenNetwork.depth]

lemma gen_wt_le_running_max (cs : List (GenComparator N)) (wt : Fin N → ℕ) (dm : ℕ)
    (hwt : ∀ k, wt k ≤ dm) :
    ∀ k, (cs.foldl genDepthStep (wt, dm)).1 k ≤ (cs.foldl genDepthStep (wt, dm)).2 := by
  induction cs generalizing wt dm with
  | nil => exact hwt
  | cons c cs ih =>
    refine ih _ _ fun k ↦ ?_
    have := hwt k
    simp only [Function.update_apply]
    split_ifs <;> omega

lemma gen_foldl_pointwise_shift (cs : List (GenComparator N))
    (wt wt₀ : Fin N → ℕ) (dm dm₀ d : ℕ)
    (hwt : ∀ k, wt k ≤ d + wt₀ k) (hdm : dm ≤ d + dm₀) :
    (cs.foldl genDepthStep (wt, dm)).2 ≤ d + (cs.foldl genDepthStep (wt₀, dm₀)).2 := by
  induction cs generalizing wt wt₀ dm dm₀ with
  | nil => exact hdm
  | cons c cs ih =>
    refine ih _ _ _ _ (fun k ↦ ?_) ?_
    · have := hwt k; have := hwt c.a; have := hwt c.b
      simp only [Function.update_apply]
      split_ifs <;> omega
    · have := hwt c.a; have := hwt c.b
      dsimp only [genDepthStep]; omega

theorem GenNetwork.depth_append_le (G H : GenNetwork N) :
    (G.append H).depth ≤ G.depth + H.depth := by
  simp only [GenNetwork.depth, GenNetwork.append, List.foldl_append]
  have := gen_foldl_pointwise_shift H.comparators
    (G.comparators.foldl genDepthStep (fun _ ↦ 0, 0)).1 (fun _ ↦ 0) _ 0
    (G.comparators.foldl genDepthStep (fun _ ↦ 0, 0)).2
    (fun k ↦ by simpa using gen_wt_le_running_max G.comparators (fun _ ↦ 0) 0 (fun _ ↦ le_rfl) k)
    le_rfl
  simpa using this

/-! ## The conjugated stage -/

/-- Conjugate a standard network by a wire permutation `π`: comparator `(i, j)` becomes the
generalized comparator `(π i, π j)` (min to `π i`). -/
def conjNet (π : Equiv.Perm (Fin N)) (net : ComparatorNetwork N) : GenNetwork N :=
  ⟨net.comparators.map fun c => ⟨π c.i, π c.j, fun h => c.h.ne (π.injective h)⟩⟩

theorem GenComparator.apply_conj {α : Type*} [LinearOrder α] (π : Equiv.Perm (Fin N))
    (c : Comparator N) (x : Fin N → α) :
    (GenComparator.apply ⟨π c.i, π c.j, fun h => c.h.ne (π.injective h)⟩ x) ∘ π =
      c.apply (x ∘ π) := by
  funext a
  simp only [Function.comp, GenComparator.apply, Comparator.apply,
    EmbeddingLike.apply_eq_iff_eq]

private theorem foldl_conj {α : Type*} [LinearOrder α] (π : Equiv.Perm (Fin N))
    (cs : List (Comparator N)) (x : Fin N → α) :
    ((cs.map fun c => (⟨π c.i, π c.j, fun h => c.h.ne (π.injective h)⟩ : GenComparator N)).foldl
        (fun acc c => c.apply acc) x) ∘ π = cs.foldl (fun acc c => c.apply acc) (x ∘ π) := by
  induction cs generalizing x with
  | nil => rfl
  | cons c cs ih =>
    simp only [List.map_cons, List.foldl_cons]
    refine (ih _).trans ?_
    rw [GenComparator.apply_conj π c x]

/-- **(1) Execution of a conjugated stage:** `(conjNet π net).exec x = (net.exec (x ∘ π)) ∘ π⁻¹`. -/
theorem conjNet_exec {α : Type*} [LinearOrder α] (π : Equiv.Perm (Fin N))
    (net : ComparatorNetwork N) (x : Fin N → α) :
    (conjNet π net).exec x = fun w => net.exec (x ∘ π) (π.symm w) := by
  funext w
  have := congrFun (foldl_conj π net.comparators x) (π.symm w)
  simpa [conjNet, GenNetwork.exec, ComparatorNetwork.exec] using this

private theorem foldl_depth_conj (π : Equiv.Perm (Fin N)) (cs : List (Comparator N))
    (wt : Fin N → ℕ) (d : ℕ) :
    ((cs.map fun c => (⟨π c.i, π c.j, fun h => c.h.ne (π.injective h)⟩ : GenComparator N)).foldl
        genDepthStep (wt ∘ π.symm, d)) =
      ((cs.foldl depthStep (wt, d)).1 ∘ π.symm, (cs.foldl depthStep (wt, d)).2) := by
  induction cs generalizing wt d with
  | nil => rfl
  | cons c cs ih =>
    simp only [List.map_cons, List.foldl_cons]
    have hstep : genDepthStep (wt ∘ π.symm, d)
        ⟨π c.i, π c.j, fun h => c.h.ne (π.injective h)⟩
        = ((depthStep (wt, d) c).1 ∘ π.symm, (depthStep (wt, d) c).2) := by
      simp only [genDepthStep, depthStep, Function.comp, Equiv.symm_apply_apply]
      refine Prod.ext ?_ rfl
      show _ = (Function.update (Function.update wt c.i _) c.j _) ∘ π.symm
      rw [Function.update_comp_equiv, Function.update_comp_equiv]
      rfl
    rw [hstep]
    have := ih (depthStep (wt, d) c).1 (depthStep (wt, d) c).2
    rw [Prod.mk.eta] at this
    exact this

/-- **(2) Conjugation preserves depth.** -/
theorem conjNet_depth (π : Equiv.Perm (Fin N)) (net : ComparatorNetwork N) :
    (conjNet π net).depth = net.depth := by
  have := foldl_depth_conj π net.comparators (fun _ => 0) 0
  have h0 : ((fun _ => 0 : Fin N → ℕ) ∘ π.symm) = fun _ => 0 := rfl
  rw [h0] at this
  simp only [ComparatorNetwork.depth, conjNet, GenNetwork.depth]
  rw [this]

/-! ## Composition of stages with inter-stage permutations -/

/-- The iteration `x_{t+1} = net_t.exec (x_t ∘ π_t)` over a list of stages `(net_t, π_t)`. -/
def iterStages {α : Type*} [LinearOrder α] :
    List (ComparatorNetwork N × Equiv.Perm (Fin N)) → (Fin N → α) → (Fin N → α)
  | [], x => x
  | (net, π) :: rest, x => iterStages rest (net.exec (x ∘ π))

/-- The product `P * π_0 * π_1 * ...` of the permutations of the stages. -/
def finalPerm : Equiv.Perm (Fin N) → List (ComparatorNetwork N × Equiv.Perm (Fin N)) →
    Equiv.Perm (Fin N)
  | P, [] => P
  | P, (_, π) :: rest => finalPerm (P * π) rest

/-- The generalized network of a list of stages, each conjugated by the cumulative permutation
`P * π_0 * ... * π_t`. -/
def composeGen : Equiv.Perm (Fin N) → List (ComparatorNetwork N × Equiv.Perm (Fin N)) →
    GenNetwork N
  | _, [] => GenNetwork.nil N
  | P, (net, π) :: rest => (conjNet (P * π) net).append (composeGen (P * π) rest)

/-- **(4a) Execution.** If the physical state `y` is the logical state `x` read through `P⁻¹`
(`y = x ∘ P⁻¹`), then `composeGen P stages` produces the logical output read through the final
cumulative permutation. -/
theorem composeGen_exec {α : Type*} [LinearOrder α] :
    ∀ (stages : List (ComparatorNetwork N × Equiv.Perm (Fin N))) (P : Equiv.Perm (Fin N))
      (x y : Fin N → α), (∀ w, y w = x (P.symm w)) →
      (composeGen P stages).exec y = fun w => iterStages stages x ((finalPerm P stages).symm w)
  | [], P, x, y, hxy => by
    funext w
    simp [composeGen, finalPerm, iterStages, GenNetwork.exec_nil, hxy]
  | (net, π) :: rest, P, x, y, hxy => by
    simp only [composeGen, GenNetwork.exec_append, finalPerm, iterStages]
    have h1 : (conjNet (P * π) net).exec y = fun w => net.exec (x ∘ π) ((P * π).symm w) := by
      rw [conjNet_exec]
      funext w
      congr 1
      funext a
      simp only [Function.comp, Equiv.Perm.mul_apply]
      rw [hxy]
      simp
    rw [h1]
    exact composeGen_exec rest (P * π) (net.exec (x ∘ π)) _ (fun w => rfl)

/-- **(4b) Depth.** -/
theorem composeGen_depth_le :
    ∀ (stages : List (ComparatorNetwork N × Equiv.Perm (Fin N))) (P : Equiv.Perm (Fin N)),
      (composeGen P stages).depth ≤ (stages.map fun s => s.1.depth).sum
  | [], P => by simp [composeGen, GenNetwork.depth_nil]
  | (net, π) :: rest, P => by
    simp only [composeGen, List.map_cons, List.sum_cons]
    refine (GenNetwork.depth_append_le _ _).trans ?_
    rw [conjNet_depth]
    exact Nat.add_le_add_left (composeGen_depth_le rest (P * π)) _

/-- The whole composite, starting from the identity cumulative permutation: on input `x` it
outputs the iteration `iterStages stages x` read through `(finalPerm 1 stages)⁻¹`. -/
theorem composeGen_exec_one {α : Type*} [LinearOrder α]
    (stages : List (ComparatorNetwork N × Equiv.Perm (Fin N))) (x : Fin N → α) :
    (composeGen 1 stages).exec x =
      fun w => iterStages stages x ((finalPerm 1 stages).symm w) :=
  composeGen_exec stages 1 x x (fun w => by simp)

/-! ## From a generalized network to a standard sorting network -/

theorem GenNetwork.exec_comp_monotone {α β : Type*} [LinearOrder α] [LinearOrder β]
    (G : GenNetwork N) {f : α → β} (hf : Monotone f) (v : Fin N → α) :
    f ∘ G.exec v = G.exec (f ∘ v) := by
  funext k
  have h := congrFun (ComparatorNetwork.exec_comp_monotone (untangleNet G) hf v)
    (untanglePerm G k)
  simp only [Function.comp] at h ⊢
  rw [untangle_exec, untangle_exec]
  exact h

theorem GenNetwork.exec_eq_comp_perm {α : Type*} [LinearOrder α] (G : GenNetwork N)
    (v : Fin N → α) : ∃ ρ : Equiv.Perm (Fin N), G.exec v = v ∘ ρ := by
  obtain ⟨ρ, hρ⟩ := Chvatal.ComparatorNetwork.exec_eq_comp_perm (untangleNet G) v
  refine ⟨ρ * untanglePerm G, funext fun k => ?_⟩
  rw [untangle_exec, hρ]
  rfl

/-- **Generic final theorem.** A generalized network whose output on every permutation input is
the same vector is, after untangling, a sorting network of the same depth. -/
theorem GenNetwork.sorts_of_const (G : GenNetwork N)
    (hconst : ∀ p : Equiv.Perm (Fin N),
      G.exec (fun w => p w) = G.exec (fun w => (1 : Equiv.Perm (Fin N)) w)) :
    ∃ S : ComparatorNetwork N, S.depth = G.depth ∧ ComparatorNetwork.Sorts.{0} S := by
  obtain ⟨ρ, hρ⟩ := GenNetwork.exec_eq_comp_perm G (fun w => (1 : Equiv.Perm (Fin N)) w)
  have hY : ∀ (p : Equiv.Perm (Fin N)) r, G.exec (fun w => p w) (ρ.symm r) = r := by
    intro p r
    rw [hconst p, hρ]
    simp
  have hmono : ∀ (α : Type) [LinearOrder α] (v : Fin N → α),
      Monotone (fun r : Fin N => G.exec v (ρ.symm r)) := by
    intro α _ v
    obtain ⟨σ, hσ⟩ := exists_sorting_perm v
    have h := GenNetwork.exec_comp_monotone G hσ (fun w => σ w)
    have : ∀ r, G.exec v (ρ.symm r) = (v ∘ ⇑σ.symm) r := fun r => by
      have h2 : G.exec v (ρ.symm r) = G.exec ((v ∘ ⇑σ.symm) ∘ (fun w => σ w)) (ρ.symm r) := by
        congr 1; funext w; simp only [Function.comp_apply, Equiv.symm_apply_apply]
      rw [h2, ← h]
      show (v ∘ ⇑σ.symm) (G.exec (fun w => σ w) (ρ.symm r)) = _
      rw [hY σ r]
    intro r s hrs
    show G.exec v (ρ.symm r) ≤ G.exec v (ρ.symm s)
    rw [this, this]
    exact hσ hrs
  exact Untangle.untangle G ρ hmono

/-- **(4c) Stages to a standard sorting network.**  If the iteration
`x_{t+1} = net_t.exec (x_t ∘ π_t)` produces the same output on all permutation inputs, then there
is a standard sorting network of depth at most `Σ depth net_t`. -/
theorem stages_sort (stages : List (ComparatorNetwork N × Equiv.Perm (Fin N)))
    (hconst : ∀ p : Equiv.Perm (Fin N),
      iterStages stages (fun w => p w) = iterStages stages (fun w => (1 : Equiv.Perm (Fin N)) w)) :
    ∃ S : ComparatorNetwork N,
      S.depth ≤ (stages.map fun s => s.1.depth).sum ∧ ComparatorNetwork.Sorts.{0} S := by
  have hc : ∀ p : Equiv.Perm (Fin N),
      (composeGen 1 stages).exec (fun w => p w) =
        (composeGen 1 stages).exec (fun w => (1 : Equiv.Perm (Fin N)) w) := by
    intro p
    rw [composeGen_exec_one, composeGen_exec_one, hconst p]
  obtain ⟨S, hS, hSs⟩ := GenNetwork.sorts_of_const _ hc
  exact ⟨S, hS ▸ composeGen_depth_le stages 1, hSs⟩

end Untangle
