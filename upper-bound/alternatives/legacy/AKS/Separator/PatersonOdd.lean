module

public import AKS.Separator.PatersonPrefix
public import AKS.Sort.Shrink

/-! # Odd restricted halvers via a virtual maximum -/

@[expose] public section

namespace Paterson

/-- Simulate an even-wire halver on `2*m-1` real wires by placing a virtual
maximum on the final wire. Comparators touching that wire are no-ops. -/
def oddInitialHalver {m : ℕ} (net : ComparatorNetwork (2 * m))
    (hm : 0 < m) : ComparatorNetwork (2 * m - 1) :=
  net.restrictWires (2 * m - 1) (by omega)

theorem oddInitialHalver_depth_le {m : ℕ} (net : ComparatorNetwork (2 * m))
    (hm : 0 < m) : (oddInitialHalver net hm).depth ≤ net.depth :=
  restrictWires_depth_le net (2 * m - 1) (by omega)

private theorem filter_card_without_last {m : ℕ} (hm : 0 < m)
    (P : Fin (2 * m) → Prop) (Q : Fin (2 * m - 1) → Prop)
    [DecidablePred P] [DecidablePred Q]
    (hagrees : ∀ i : Fin (2 * m - 1),
      P ⟨i.val, by have := i.isLt; omega⟩ ↔ Q i)
    (hlast : ∀ i : Fin (2 * m), 2 * m - 1 ≤ i.val → ¬ P i) :
    (Finset.univ.filter P).card = (Finset.univ.filter Q).card := by
  apply Finset.card_nbij'
    (fun i : Fin (2 * m) ↦
      if hi : i.val < 2 * m - 1 then ⟨i.val, hi⟩ else ⟨0, by omega⟩)
    (fun i : Fin (2 * m - 1) ↦ ⟨i.val, by have := i.isLt; omega⟩)
  · intro i hi
    have hPi := (Finset.mem_filter.mp hi).2
    have hlt : i.val < 2 * m - 1 := by
      by_contra h
      exact hlast i (by omega) hPi
    simp only [dif_pos hlt]
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      (hagrees ⟨i.val, hlt⟩).mp (by simpa using hPi)⟩
  · intro i hi
    have hQi := (Finset.mem_filter.mp hi).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      (hagrees i).mpr hQi⟩
  · intro i hi
    have hPi := (Finset.mem_filter.mp hi).2
    have hlt : i.val < 2 * m - 1 := by
      by_contra h
      exact hlast i (by omega) hPi
    ext
    simp [hlt]
  · intro i _
    ext
    simp [i.isLt]

/-- The virtual maximum preserves the restricted initial-cohort guarantee,
with no extra error term. This is the one-sided odd-block lemma used on the
left side of Paterson's separator. -/
theorem oddInitialHalver_injective {m n : ℕ} {ε α : ℚ}
    (hm : 0 < m) {net : ComparatorNetwork (2 * m)}
    (hnet : IsEpsilonAlphaHalver net ε α)
    (u : Fin (2 * m - 1) → Fin n) (hu : Function.Injective u)
    (k : ℕ) (hk_n : k ≤ n)
    (hk : ((Finset.univ.filter (fun i : Fin (2 * m - 1) ↦
        (u i).val < k)).card : ℝ) ≤ (α : ℝ) * m) :
    ((Finset.univ.filter (fun pos : Fin (2 * m - 1) ↦
        m ≤ pos.val ∧ ((oddInitialHalver net hm).exec u pos).val < k)).card : ℝ) ≤
      (ε : ℝ) * ↑(Finset.univ.filter (fun i : Fin (2 * m - 1) ↦
        (u i).val < k)).card := by
  let q : Fin n → Fin (n + 1) := fun x ↦ ⟨x.val, by omega⟩
  have hq_mono : Monotone q := by
    intro x y hxy
    exact hxy
  let uPad : Fin (2 * m) → Fin (n + 1) := fun i ↦
    if hi : i.val < 2 * m - 1 then q (u ⟨i.val, hi⟩)
    else ⟨n, by omega⟩
  have huPad_inj : Function.Injective uPad := by
    intro i j hij
    by_cases hi : i.val < 2 * m - 1
    · by_cases hj : j.val < 2 * m - 1
      · have hval : u ⟨i.val, hi⟩ = u ⟨j.val, hj⟩ := by
          apply Fin.ext
          have hh := congrArg Fin.val hij
          simpa [uPad, hi, hj, q] using hh
        have := congrArg Fin.val (hu hval)
        exact Fin.ext this
      · have hh := congrArg Fin.val hij
        simp [uPad, hi, hj, q] at hh
        have := (u ⟨i.val, hi⟩).isLt
        omega
    · by_cases hj : j.val < 2 * m - 1
      · have hh := congrArg Fin.val hij
        simp [uPad, hi, hj, q] at hh
        have := (u ⟨j.val, hj⟩).isLt
        omega
      · exact Fin.ext (by have := i.isLt; have := j.isLt; omega)
  let v : Fin (2 * m - 1) → Fin (n + 1) := q ∘ u
  have hagree : ∀ i : Fin (2 * m - 1),
      uPad ⟨i.val, by have := i.isLt; omega⟩ = v i := by
    intro i
    simp [uPad, v, i.isLt]
  have hhigh : ∀ i : Fin (2 * m), 2 * m - 1 ≤ i.val →
      ∀ j : Fin (2 * m), j.val < 2 * m - 1 → uPad j ≤ uPad i := by
    intro i hi j hj
    simp [uPad, show ¬ i.val < 2 * m - 1 by omega, hj, q]
  have hexec : ∀ i : Fin (2 * m - 1),
      net.exec uPad ⟨i.val, by have := i.isLt; omega⟩ =
        q ((oddInitialHalver net hm).exec u i) := by
    intro i
    have h := restrictWires_exec_agree (by omega : 2 * m - 1 ≤ 2 * m)
      net uPad v hagree hhigh i
    have hcast : (oddInitialHalver net hm).exec v =
        q ∘ (oddInitialHalver net hm).exec u := by
      exact ComparatorNetwork.exec_comp_mono _ hq_mono u
    change net.exec uPad ⟨i.val, by have := i.isLt; omega⟩ =
      (oddInitialHalver net hm).exec v i at h
    rw [hcast] at h
    exact h
  have hinput : (Finset.univ.filter (fun i : Fin (2 * m) ↦
      (uPad i).val < k)).card =
      (Finset.univ.filter (fun i : Fin (2 * m - 1) ↦
      (u i).val < k)).card := by
    apply filter_card_without_last hm
    · intro i
      simp [uPad, q, i.isLt]
    · intro i hi hval
      have hnot : ¬i.val < 2 * m - 1 := by omega
      simp [uPad, hnot] at hval
      omega
  have houtput : (Finset.univ.filter (fun pos : Fin (2 * m - 1) ↦
      m ≤ pos.val ∧ ((oddInitialHalver net hm).exec u pos).val < k)).card ≤
      (Finset.univ.filter (fun pos : Fin (2 * m) ↦
      m ≤ pos.val ∧ (net.exec uPad pos).val < k)).card := by
    calc
      _ = (Finset.univ.filter (fun pos : Fin (2 * m) ↦
          pos.val < 2 * m - 1 ∧ m ≤ pos.val ∧ (net.exec uPad pos).val < k)).card := by
        symm
        apply filter_card_without_last hm
        · intro i
          simp only [hexec i, q]
          simp [i.isLt]
        · intro i hi hval
          exact (Nat.not_lt.mpr hi) hval.1
      _ ≤ (Finset.univ.filter (fun pos : Fin (2 * m) ↦
          m ≤ pos.val ∧ (net.exec uPad pos).val < k)).card := by
        apply Finset.card_le_card
        intro pos
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact And.right
  have hlocal := restricted_injective_initial hnet uPad huPad_inj k (by
    simpa only [hinput] using hk)
  calc
    _ ≤ ↑(Finset.univ.filter (fun pos : Fin (2 * m) ↦
        m ≤ pos.val ∧ (net.exec uPad pos).val < k)).card := by exact_mod_cast houtput
    _ ≤ (ε : ℝ) * ↑(Finset.univ.filter (fun i : Fin (2 * m) ↦
        (uPad i).val < k)).card := hlocal
    _ = (ε : ℝ) * ↑(Finset.univ.filter (fun i : Fin (2 * m - 1) ↦
        (u i).val < k)).card := by rw [hinput]

/-- The actual selected Paterson stage on an odd block, with a virtual
maximum used on its final wire. -/
noncomputable def oddStageInitial (level m : ℕ) (hm : 0 < m) :
    ComparatorNetwork (2 * m - 1) :=
  oddInitialHalver (stageNetwork level m) hm

theorem oddStageInitial_depth_le (level m : ℕ) (hm : 0 < m) :
    (oddStageInitial level m hm).depth ≤ stageDepth level :=
  (oddInitialHalver_depth_le (stageNetwork level m) hm).trans
    (stageNetwork_depth_le level m)

theorem oddStageInitial_bound (level m n : ℕ) (hm : 0 < m)
    (hle : level < 5)
    (u : Fin (2 * m - 1) → Fin n) (hu : Function.Injective u)
    (k : ℕ) (hk_n : k ≤ n)
    (hk : ((Finset.univ.filter (fun i : Fin (2 * m - 1) ↦
        (u i).val < k)).card : ℝ) ≤ (stageAlpha level : ℝ) * m) :
    ((Finset.univ.filter (fun pos : Fin (2 * m - 1) ↦
        m ≤ pos.val ∧ ((oddStageInitial level m hm).exec u pos).val < k)).card : ℝ) ≤
      (stageErrorQ level : ℝ) *
        ↑(Finset.univ.filter (fun i : Fin (2 * m - 1) ↦
          (u i).val < k)).card :=
  oddInitialHalver_injective hm (stageNetwork_halver level m hle)
    u hu k hk_n hk

end Paterson
