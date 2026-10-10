module

public import AKS.Paterson.RankTransfer
public import AKS.Paterson.GoodRouting
public import AKS.Sort.Shrink

/-! # Arbitrary virtual-maximum padding for partial bags

The partial-level refinement uses an ideal block larger than its real input.
Deleting comparisons with virtual maxima preserves a supported initial-cohort
bound without an additive error. This extends the existing one-wire odd-block
gadget to arbitrarily many virtual wires, including an empty real block.
The symmetric refinement and initial half split must still be assembled into
the partial-bag separator.
Source: Paterson (1990), Sections 5 and 7.
-/

@[expose] public section

namespace Paterson

open Finset

theorem padded_initial_separator {full real ambient f : ℕ}
    {net : ComparatorNetwork full} {support err : ℝ}
    (hnet : IsSupportedSeparator net f support err) (hs : real ≤ full)
    (u : Fin real → Fin ambient) (hu : Function.Injective u)
    (threshold : ℕ) (ht : threshold ≤ ambient)
    (hsupport : ((univ.filter (fun i ↦ (u i).val < threshold)).card : ℝ) ≤ support * full) :
    ((univ.filter (fun i : Fin real ↦ f ≤ i.val ∧
      ((net.restrictWires real hs).exec u i).val < threshold)).card : ℝ) ≤
      err * (univ.filter (fun i ↦ (u i).val < threshold)).card := by
  let q : Fin ambient → Fin (ambient + full) := fun x ↦ ⟨x.val, by omega⟩
  have hq : Monotone q := by intro i j hij; exact hij
  let padded : Fin full → Fin (ambient + full) := fun i ↦
    if hi : i.val < real then q (u ⟨i.val, hi⟩)
    else ⟨ambient + (i.val - real), by have := i.isLt; omega⟩
  have hinj : Function.Injective padded := by
    intro i j hij
    have hval := congrArg Fin.val hij
    by_cases hi : i.val < real <;> by_cases hj : j.val < real
    · have hreal : u ⟨i.val, hi⟩ = u ⟨j.val, hj⟩ := by
        apply Fin.ext
        simpa [padded, hi, hj, q] using hval
      exact Fin.ext (congrArg (fun x : Fin real ↦ x.val) (hu hreal))
    · simp only [padded, dif_pos hi, dif_neg hj, q] at hval
      have hv := (u ⟨i.val, hi⟩).isLt
      omega
    · simp only [padded, dif_neg hi, dif_pos hj, q] at hval
      have hv := (u ⟨j.val, hj⟩).isLt
      omega
    · simp only [padded, dif_neg hi, dif_neg hj] at hval
      exact Fin.ext (by omega)
  let emb : Fin real → Fin full := fun i ↦ ⟨i.val, lt_of_lt_of_le i.isLt hs⟩
  have hemb : Function.Injective emb := by
    intro i j hij
    exact Fin.ext (congrArg (fun x : Fin full ↦ x.val) hij)
  have hexec (i : Fin real) : net.exec padded (emb i) =
      q ((net.restrictWires real hs).exec u i) := by
    have h := restrictWires_exec_agree hs net padded (q ∘ u)
      (fun i ↦ by simp [padded, q, i.isLt])
      (fun i hi j hj ↦ by
        simp only [padded, dif_neg (show ¬i.val < real by omega), dif_pos hj, q, Fin.le_def]
        have hv := (u ⟨j.val, hj⟩).isLt
        omega) i
    rw [ComparatorNetwork.exec_comp_mono _ hq u] at h
    exact h
  have hinput : (univ.filter (fun i ↦ (padded i).val < threshold)).card =
      (univ.filter (fun i ↦ (u i).val < threshold)).card := by
    have heq : univ.filter (fun i ↦ (padded i).val < threshold) =
        (univ.filter (fun i ↦ (u i).val < threshold)).image emb := by
      ext i
      simp only [mem_filter, mem_univ, true_and, mem_image]
      by_cases hi : i.val < real
      · simp only [padded, dif_pos hi, q]
        constructor
        · intro h
          exact ⟨⟨i.val, hi⟩, h, Fin.ext rfl⟩
        · rintro ⟨j, hj, heq⟩
          have heq' : j = ⟨i.val, hi⟩ := Fin.ext (congrArg (fun x : Fin full ↦ x.val) heq)
          simpa only [heq'] using hj
      · simp only [padded, dif_neg hi]
        constructor
        · intro h
          omega
        · rintro ⟨j, _, heq⟩
          have := j.isLt
          have := congrArg Fin.val heq
          dsimp [emb] at this
          omega
    rw [heq, card_image_of_injective _ hemb]
  have houtput :
      (univ.filter (fun i : Fin real ↦ f ≤ i.val ∧
        ((net.restrictWires real hs).exec u i).val < threshold)).card ≤
      (univ.filter (fun i : Fin full ↦ f ≤ i.val ∧ (net.exec padded i).val < threshold)).card := by
    apply card_le_card_of_injOn emb
    · intro i hi
      simp only [mem_coe, mem_filter, mem_univ, true_and] at hi ⊢
      rw [hexec]
      exact hi
    · intro i _ j _ hij
      exact hemb hij
  have h := supported_injective_initial hnet padded hinj threshold (by
    simpa only [hinput] using hsupport)
  rw [hinput] at h
  exact (Nat.cast_le.mpr houtput).trans h

theorem reverseFin_initial_fringe_count {wires values : ℕ}
    (w : Fin wires → Fin values) (f threshold : ℕ) (ht : threshold ≤ values) :
    (univ.filter (fun i ↦ f ≤ i.val ∧ (reverseFin w i).val < threshold)).card =
      (univ.filter (fun i ↦ i.val < wires - f ∧ values - threshold ≤ (w i).val)).card := by
  apply card_nbij' Fin.rev Fin.rev
  · intro i hi
    simp only [mem_coe, mem_filter, mem_univ, true_and, reverseFin, Fin.val_rev] at hi ⊢
    have := i.isLt
    have := (w i.rev).isLt
    omega
  · intro i hi
    simp only [mem_coe, mem_filter, mem_univ, true_and, reverseFin,
      Fin.rev_rev, Fin.val_rev] at hi ⊢
    have := i.isLt
    have := (w i).isLt
    omega
  · intro _ _; simp
  · intro _ _; simp

theorem reverseFin_final_fringe_count {wires values : ℕ}
    (w : Fin wires → Fin values) (f threshold : ℕ) (ht : threshold ≤ values) :
    (univ.filter (fun i ↦ i.val < wires - f ∧
      values - threshold ≤ (reverseFin w i).val)).card =
      (univ.filter (fun i ↦ f ≤ i.val ∧ (w i).val < threshold)).card := by
  symm
  simpa only [reverseFin_reverseFin] using
    reverseFin_initial_fringe_count (reverseFin w) f threshold ht

theorem flip_isSupportedSeparator {n f : ℕ} {net : ComparatorNetwork n}
    {support err : ℝ} (hnet : IsSupportedSeparator net f support err) :
    IsSupportedSeparator net.flip f support err := by
  intro v
  let v' : Equiv.Perm (Fin n) := (Fin.revPerm.trans v).trans Fin.revPerm
  have hv : (v' : Fin n → Fin n) = reverseFin v := by funext i; rfl
  have hexec : net.flip.exec v = reverseFin (net.exec v') := by
    have h := flip_exec_reverseFin net (v' : Fin n → Fin n)
    rw [hv, reverseFin_reverseFin] at h
    exact h
  obtain ⟨hL, hR⟩ := hnet v'
  constructor
  · intro k hk
    by_cases hkn : k ≤ n
    · rw [hexec, reverseFin_initial_fringe_count _ _ _ hkn]
      exact hR k hk
    · have hk' : n ≤ k := by omega
      have hR' := hR k hk
      have hnzero : n - k = 0 := by omega
      -- The supported contract at k > n still transfers by direct reversal;
      -- every rank is below k, and the corresponding final cohort is all ranks.
      rw [hexec]
      have hcard : (univ.filter (fun i : Fin n ↦ f ≤ i.val ∧
          (reverseFin (net.exec v') i).val < k)).card =
          (univ.filter (fun i : Fin n ↦ i.val < n - f ∧ n - k ≤ (net.exec v' i).val)).card := by
        apply card_nbij' Fin.rev Fin.rev
        · intro i hi
          simp only [mem_coe, mem_filter, mem_univ, true_and, reverseFin, Fin.val_rev] at hi ⊢
          have := i.isLt
          omega
        · intro i hi
          simp only [mem_coe, mem_filter, mem_univ, true_and, reverseFin,
            Fin.rev_rev, Fin.val_rev] at hi ⊢
          have := i.isLt
          have := (net.exec v' i).isLt
          omega
        · intro _ _; simp
        · intro _ _; simp
      rw [hcard]
      exact hR'
  · intro k hk
    rw [hexec]
    by_cases hkn : k ≤ n
    · rw [reverseFin_final_fringe_count _ _ _ hkn]
      exact hL k hk
    · have hnzero : n - k = 0 := by omega
      have hcard : (univ.filter (fun i : Fin n ↦ i.val < n - f ∧
          n - k ≤ (reverseFin (net.exec v') i).val)).card =
          (univ.filter (fun i : Fin n ↦ f ≤ i.val ∧ (net.exec v' i).val < k)).card := by
        apply card_nbij' Fin.rev Fin.rev
        · intro i hi
          simp only [mem_coe, mem_filter, mem_univ, true_and, reverseFin, Fin.val_rev] at hi ⊢
          have := i.isLt
          have := (net.exec v' i.rev).isLt
          omega
        · intro i hi
          simp only [mem_coe, mem_filter, mem_univ, true_and, reverseFin,
            Fin.rev_rev, Fin.val_rev] at hi ⊢
          have := i.isLt
          omega
        · intro _ _; simp
        · intro _ _; simp
      rw [hcard]
      exact hL k hk

def paddedFinalNetwork {full : ℕ} (net : ComparatorNetwork full)
    (real : ℕ) (hs : real ≤ full) : ComparatorNetwork real :=
  (net.flip.restrictWires real hs).flip

theorem paddedFinalNetwork_depth_le {full : ℕ} (net : ComparatorNetwork full)
    (real : ℕ) (hs : real ≤ full) : (paddedFinalNetwork net real hs).depth ≤ net.depth :=
  (flip_depth_le _).trans ((restrictWires_depth_le _ _ _).trans (flip_depth_le net))

/-- Arbitrary virtual-minimum padding, with the same error and depth budget. -/
theorem padded_final_separator {full real ambient f : ℕ}
    {net : ComparatorNetwork full} {support err : ℝ}
    (hnet : IsSupportedSeparator net f support err) (hs : real ≤ full)
    (u : Fin real → Fin ambient) (hu : Function.Injective u)
    (threshold : ℕ) (ht : threshold ≤ ambient)
    (hsupport : ((univ.filter (fun i ↦ threshold ≤ (u i).val)).card : ℝ) ≤ support * full) :
    ((univ.filter (fun i : Fin real ↦ i.val < real - f ∧
      threshold ≤ ((paddedFinalNetwork net real hs).exec u i).val)).card : ℝ) ≤
      err * (univ.filter (fun i ↦ threshold ≤ (u i).val)).card := by
  have hu' : Function.Injective (reverseFin u) := by
    intro i j hij
    exact Fin.rev_injective (hu (Fin.rev_injective hij))
  have hinput := reverseFin_prefix_card u ht
  have h := padded_initial_separator (flip_isSupportedSeparator hnet) hs (reverseFin u) hu'
    (ambient - threshold) (by omega) (by simpa only [hinput] using hsupport)
  have hexec : (paddedFinalNetwork net real hs).exec u =
      reverseFin ((net.flip.restrictWires real hs).exec (reverseFin u)) := by
    have hh := flip_exec_reverseFin (net.flip.restrictWires real hs) (reverseFin u)
    rw [reverseFin_reverseFin] at hh
    exact hh
  rw [hexec, ← show ambient - (ambient - threshold) = threshold by omega]
  rw [reverseFin_final_fringe_count _ _ _ (show ambient - threshold ≤ ambient by omega)]
  simpa only [hinput, show ambient - (ambient - threshold) = threshold by omega] using h

end Paterson
