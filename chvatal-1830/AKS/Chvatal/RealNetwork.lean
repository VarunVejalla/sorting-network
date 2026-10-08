module

/-
  # The full real Chvátal network: stages followed by the final layer

  `stagesNet F nets T` is the sequential composition of the first `T` stage networks
  `stageNet (wireSets F t) (nets t)`; `finalLayer S` is the parallel bitonic sorters on the
  wire sets `S b`. Generic in `nets` and `S`; depth bound `totalDepth d` for the real nets.
-/

public import AKS.Chvatal.ExecPlacement
public import AKS.Chvatal.StageNet
public import AKS.Chvatal.RealNets
public import AKS.Chvatal.DepthSkeleton
public import AKS.Bitonic.TightDepth
public import AKS.Sort.Depth

@[expose] public section

namespace Chvatal

variable {d tf : ℕ}

/-- The first `t` stages, composed sequentially. -/
noncomputable def stagesNet (F : FlowSizes d tf)
    (nets : ℕ → (b : KBag 64 d) → (n : ℕ) → ComparatorNetwork n) :
    ℕ → ComparatorNetwork (64 ^ d)
  | 0 => ⟨[]⟩
  | t + 1 => (stagesNet F nets t).append (stageNet (wireSets F t) (nets t))

theorem stagesNet_exec (F : FlowSizes d tf)
    (nets : ℕ → (b : KBag 64 d) → (n : ℕ) → ComparatorNetwork n)
    (v : Equiv.Perm (Fin (64 ^ d))) :
    ∀ t, (stagesNet F nets t).exec (fun w => v w) = X F nets v t := by
  intro t
  induction t with
  | zero => rfl
  | succ t ih =>
    show ((stagesNet F nets t).append (stageNet (wireSets F t) (nets t))).exec _ = _
    unfold ComparatorNetwork.append
    rw [ComparatorNetwork.exec_append, ih]
    rfl

theorem stagesNet_depth_le (F : FlowSizes d tf)
    (nets : ℕ → (b : KBag 64 d) → (n : ℕ) → ComparatorNetwork n)
    (D : ℕ → ℕ) (T : ℕ) (hT : T ≤ tf + 1)
    (hD : ∀ t < T, ∀ b n, (nets t b n).depth ≤ D t) :
    (stagesNet F nets T).depth ≤ ∑ t ∈ Finset.range T, D t := by
  induction T with
  | zero => simp [stagesNet, ComparatorNetwork.depth]
  | succ T ih =>
    rw [Finset.sum_range_succ]
    refine (ComparatorNetwork.depth_append_le _ _).trans (add_le_add
      (ih (by omega) (fun t ht => hD t (by omega))) ?_)
    exact stageNet_depth_le _ (wireSets_disjoint F (by omega)) _
      (fun b => hD T (by omega) b _)

/-- Parallel bitonic sorters on the wire sets `S b`. -/
noncomputable def finalLayer {d : ℕ} (S : KBag 64 d → Finset (Fin (64 ^ d))) :
    ComparatorNetwork (64 ^ d) :=
  stageNet S (fun _ n => bitonicNetwork n)

theorem finalLayer_depth_le {d : ℕ} (S : KBag 64 d → Finset (Fin (64 ^ d)))
    (hdisj : ∀ b b', b ≠ b' → Disjoint (S b) (S b'))
    (hcard : ∀ b, (S b).card = 0 ∨ (S b).card = 2 ^ 42) :
    (finalLayer S).depth ≤ 903 := by
  refine stageNet_depth_le S hdisj _ (fun b => ?_)
  rcases hcard b with h | h
  · rw [h]
    refine (bitonicNetwork_depth_le_budget 0).trans ?_
    simp [bitonicDepthBudget]
  · rw [h]; exact bitonicNetwork_2pow42_depth_le_903

end Chvatal
