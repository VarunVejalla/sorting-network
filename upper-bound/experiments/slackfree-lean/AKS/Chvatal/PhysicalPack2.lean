module

/-
  # Physical two-round separator: sort, scramble `σ1`, sort, scramble `σ2`, sort

  Semantic map `semanticExec2 hn σ1 σ2 = C ∘ (· ∘ ρ2⁻¹) ∘ C ∘ (· ∘ ρ1⁻¹) ∘ C` (`C` = column sort,
  `ρi = rowScrambleWirePerm σi`).  The physical network is `C`, then `C` relabeled by `ρ1⁻¹`,
  then `C` relabeled by `(ρ2 * ρ1)⁻¹`; all relabelings are row preserving, so the relabeled
  comparators stay standard.  Physical output = semantic output composed with `ρ2 * ρ1`.
-/

public import AKS.Chvatal.PhysicalPack

@[expose] public section

namespace Chvatal

/-- Two-round semantic map: column sort, scramble `σ1`, column sort, scramble `σ2`, column sort. -/
def semanticExec2 {m n : Nat} (hn : 0 < n) (σ1 σ2 : Scramble m n) {α : Type*} [LinearOrder α]
    (v : Fin (m * n) → α) : Fin (m * n) → α :=
  (columnSortNetwork m n hn).exec
    (semanticExec hn σ1 v ∘ (rowScrambleWirePerm m n hn σ2).symm)

/-- Cumulative wire permutation of both scrambles (`σ1` applied first). -/
def rowScrambleWirePerm2 (m n : Nat) (hn : 0 < n) (σ1 σ2 : Scramble m n) :
    Equiv.Perm (Fin (m * n)) :=
  rowScrambleWirePerm m n hn σ2 * rowScrambleWirePerm m n hn σ1

theorem matrixRow_rowScrambleWirePerm2 {m n : Nat} (hn : 0 < n) (σ1 σ2 : Scramble m n)
    (w : Fin (m * n)) :
    matrixRow m n hn (rowScrambleWirePerm2 m n hn σ1 σ2 w) = matrixRow m n hn w := by
  show matrixRow m n hn (rowScrambleWirePerm m n hn σ2 (rowScrambleWirePerm m n hn σ1 w)) = _
  rw [matrixRow_rowScrambleWirePerm, matrixRow_rowScrambleWirePerm]

theorem matrixRow_rowScrambleWirePerm2_symm {m n : Nat} (hn : 0 < n) (σ1 σ2 : Scramble m n)
    (w : Fin (m * n)) :
    matrixRow m n hn ((rowScrambleWirePerm2 m n hn σ1 σ2).symm w) = matrixRow m n hn w := by
  simpa using (matrixRow_rowScrambleWirePerm2 hn σ1 σ2
    ((rowScrambleWirePerm2 m n hn σ1 σ2).symm w)).symm

theorem columnSortNetwork_relabel2_lt {m n : ℕ} (hn : 0 < n) (σ1 σ2 : Scramble m n)
    (c : Comparator (m * n)) (hc : c ∈ (columnSortNetwork m n hn).comparators) :
    (rowScrambleWirePerm2 m n hn σ1 σ2).symm c.i < (rowScrambleWirePerm2 m n hn σ1 σ2).symm c.j := by
  apply wire_lt_of_matrixRow_lt hn
  rw [matrixRow_rowScrambleWirePerm2_symm, matrixRow_rowScrambleWirePerm2_symm]
  exact columnSortNetwork_comparator_rows hn c hc

/-- Physical two-round network: three column sorts, the second relabeled by `ρ1⁻¹`, the third by
`(ρ2 * ρ1)⁻¹`. -/
def physicalPack2Net (m n : ℕ) (hn : 0 < n) (σ1 σ2 : Scramble m n) :
    ComparatorNetwork (m * n) :=
  ⟨(columnSortNetwork m n hn).comparators ++
    (relabelNet (rowScrambleWirePerm m n hn σ1).symm (columnSortNetwork m n hn)
      (columnSortNetwork_relabel_lt hn σ1)).comparators ++
    (relabelNet (rowScrambleWirePerm2 m n hn σ1 σ2).symm (columnSortNetwork m n hn)
      (columnSortNetwork_relabel2_lt hn σ1 σ2)).comparators⟩

/-- Physical output = semantic output with columns permuted within rows by `ρ2 * ρ1`. -/
theorem physicalPack2Net_exec {m n : ℕ} (hn : 0 < n) (σ1 σ2 : Scramble m n)
    {α : Type*} [LinearOrder α] (v : Fin (m * n) → α) :
    (physicalPack2Net m n hn σ1 σ2).exec v =
      (semanticExec2 hn σ1 σ2 v) ∘ rowScrambleWirePerm2 m n hn σ1 σ2 := by
  have hx := ComparatorNetwork.exec_append
    (⟨(columnSortNetwork m n hn).comparators ++
      (relabelNet (rowScrambleWirePerm m n hn σ1).symm (columnSortNetwork m n hn)
        (columnSortNetwork_relabel_lt hn σ1)).comparators⟩ : ComparatorNetwork (m * n))
    (relabelNet (rowScrambleWirePerm2 m n hn σ1 σ2).symm (columnSortNetwork m n hn)
      (columnSortNetwork_relabel2_lt hn σ1 σ2)) v
  have hy := ComparatorNetwork.exec_append (columnSortNetwork m n hn)
    (relabelNet (rowScrambleWirePerm m n hn σ1).symm (columnSortNetwork m n hn)
      (columnSortNetwork_relabel_lt hn σ1)) v
  unfold physicalPack2Net
  rw [hx, hy, relabelNet_exec, relabelNet_exec]
  funext w
  have key : ((fun w => (columnSortNetwork m n hn).exec
        ((columnSortNetwork m n hn).exec v ∘ ⇑(rowScrambleWirePerm m n hn σ1).symm)
        ((rowScrambleWirePerm m n hn σ1).symm.symm w)) ∘
      ⇑(rowScrambleWirePerm2 m n hn σ1 σ2).symm) =
      semanticExec hn σ1 v ∘ (rowScrambleWirePerm m n hn σ2).symm := by
    funext w'
    simp only [Function.comp_apply, Equiv.symm_symm, semanticExec]
    congr 1
    have e : (rowScrambleWirePerm2 m n hn σ1 σ2).symm w' =
        (rowScrambleWirePerm m n hn σ1).symm ((rowScrambleWirePerm m n hn σ2).symm w') := rfl
    rw [e, Equiv.apply_symm_apply]
  rw [key]
  rfl

/-- Count form: for every predicate `P` and set of rows `R`, the number of wires in rows of `R`
whose value satisfies `P` agrees between physical and semantic two-round output. -/
theorem physicalPack2Net_rowRegion_card {m n : ℕ} (hn : 0 < n) (σ1 σ2 : Scramble m n)
    {α : Type*} [LinearOrder α] (v : Fin (m * n) → α) (R : Finset (Fin m))
    (P : α → Prop) [DecidablePred P] :
    (Finset.univ.filter fun w : Fin (m * n) =>
        matrixRow m n hn w ∈ R ∧ P ((physicalPack2Net m n hn σ1 σ2).exec v w)).card =
    (Finset.univ.filter fun w : Fin (m * n) =>
        matrixRow m n hn w ∈ R ∧ P (semanticExec2 hn σ1 σ2 v w)).card := by
  set ρ := rowScrambleWirePerm2 m n hn σ1 σ2 with hρ
  refine Finset.card_bij (fun w _ => ρ w) ?_ ?_ ?_
  · intro w hw
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw ⊢
    rw [hρ, matrixRow_rowScrambleWirePerm2 hn σ1 σ2]
    refine ⟨hw.1, ?_⟩
    have := hw.2
    rwa [physicalPack2Net_exec] at this
  · intro a _ b _ h; exact ρ.injective h
  · intro w hw
    refine ⟨ρ.symm w, ?_, by simp⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw ⊢
    rw [hρ, matrixRow_rowScrambleWirePerm2_symm hn σ1 σ2, physicalPack2Net_exec]
    exact ⟨hw.1, by simpa using hw.2⟩

/-! ## Depth -/

theorem physicalPack2Net_depth_le (m n : ℕ) (hn : 0 < n) (σ1 σ2 : Scramble m n) :
    (physicalPack2Net m n hn σ1 σ2).depth ≤ 3 * (columnSortNetwork m n hn).depth := by
  have h1 := ComparatorNetwork.depth_append_le
    ((columnSortNetwork m n hn).append
      (relabelNet (rowScrambleWirePerm m n hn σ1).symm (columnSortNetwork m n hn)
        (columnSortNetwork_relabel_lt hn σ1)))
    (relabelNet (rowScrambleWirePerm2 m n hn σ1 σ2).symm (columnSortNetwork m n hn)
      (columnSortNetwork_relabel2_lt hn σ1 σ2))
  have h2 := ComparatorNetwork.depth_append_le (columnSortNetwork m n hn)
    (relabelNet (rowScrambleWirePerm m n hn σ1).symm (columnSortNetwork m n hn)
      (columnSortNetwork_relabel_lt hn σ1))
  rw [relabelNet_depth] at h1 h2
  have e : physicalPack2Net m n hn σ1 σ2 =
      (((columnSortNetwork m n hn).append
        (relabelNet (rowScrambleWirePerm m n hn σ1).symm (columnSortNetwork m n hn)
          (columnSortNetwork_relabel_lt hn σ1))).append
        (relabelNet (rowScrambleWirePerm2 m n hn σ1 σ2).symm (columnSortNetwork m n hn)
          (columnSortNetwork_relabel2_lt hn σ1 σ2))) := rfl
  rw [e]
  omega

theorem physicalPack2Net_depth_le_budget (m n : ℕ) (hn : 0 < n) (σ1 σ2 : Scramble m n) :
    (physicalPack2Net m n hn σ1 σ2).depth ≤ 3 * bitonicDepthBudget (Nat.clog 2 m) :=
  (physicalPack2Net_depth_le m n hn σ1 σ2).trans
    (Nat.mul_le_mul_left 3 (columnSortNetwork_depth_le_budget m n hn))

end Chvatal
