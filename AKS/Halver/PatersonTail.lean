module

public import AKS.Halver.PatersonCollapsedWitnesses
public import Mathlib.Analysis.Real.Pi.Bounds

/-! # The remaining collapsed-witness tail estimate -/

@[expose] public section

open Finset

namespace Paterson

noncomputable def tailTerm (m : ℕ) (rs : ℕ × ℕ) : ℝ :=
  ((rs.2 : ℝ) / m) ^ rs.1 / (Real.pi * rs.1)

noncomputable def indexedTailTerm (m p : ℕ) (e : ℚ) (r : ℕ) : ℝ :=
  tailTerm m (r, maximalTrapTotal p e r - r)

private theorem tailTerm_nonneg (m : ℕ) (rs : ℕ × ℕ) :
    0 ≤ tailTerm m rs := by
  unfold tailTerm
  positivity

private theorem collapsed_index_injective (p : ℕ) (e : ℚ) :
    Function.Injective (fun r : ℕ => (r, maximalTrapTotal p e r - r)) := by
  intro r s h
  exact congrArg Prod.fst h

theorem admissible_tail_le_indexed_tail (m : ℕ) (a e : ℚ) :
    (∑ rs ∈ admissibleCollapsedWitnessSizes m a e,
      ((rs.2 : ℝ) / m) ^ rs.1 / (Real.pi * rs.1)) ≤
      ∑ r ∈ Finset.Icc 1 (roundedTrapSize e (supportedTrapCap m a)),
        indexedTailTerm m (supportedTrapCap m a) e r := by
  change (∑ rs ∈ admissibleCollapsedWitnessSizes m a e, tailTerm m rs) ≤ _
  have hsubset : admissibleCollapsedWitnessSizes m a e ⊆
      collapsedWitnessSizes m a e := Finset.filter_subset _ _
  have hle : (∑ rs ∈ admissibleCollapsedWitnessSizes m a e, tailTerm m rs) ≤
      ∑ rs ∈ collapsedWitnessSizes m a e, tailTerm m rs :=
    Finset.sum_le_sum_of_subset_of_nonneg hsubset
      (fun rs _ _ => tailTerm_nonneg m rs)
  calc
    _ ≤ ∑ rs ∈ collapsedWitnessSizes m a e, tailTerm m rs := hle
    _ = _ := by
      simp only [collapsedWitnessSizes]
      rw [Finset.sum_image (fun r _ s _ h => collapsed_index_injective _ _ h)]
      rfl

theorem indexed_tail_le_one_over_r {m p r : ℕ} {e : ℚ}
    (hm : 0 < m) (hpm : p ≤ m) (hr : 0 < r) :
    indexedTailTerm m p e r ≤ 1 / (Real.pi * r) := by
  let q := maximalTrapTotal p e r
  have hqm : q ≤ m := (maximalTrapTotal_le_cap p e r).trans hpm
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have hratio0 : (0 : ℝ) ≤ (q - r : ℕ) / m := by positivity
  have hratio1 : ((q - r : ℕ) : ℝ) / m ≤ 1 := by
    apply (div_le_one hmR).mpr
    exact_mod_cast (show q - r ≤ m by omega)
  have hpow := pow_le_one₀ hratio0 hratio1 (n := r)
  unfold indexedTailTerm tailTerm
  exact (div_le_div_iff_of_pos_right (mul_pos Real.pi_pos hrR)).mpr hpow

theorem indexed_tail_le_uniform {m p r : ℕ} {e : ℚ}
    (hm : 0 < m) (hpm : p ≤ m) (hr : 0 < r) (he : 0 < e) :
    indexedTailTerm m p e r ≤
      1 / (Real.pi * (e : ℝ) * m) := by
  let q := maximalTrapTotal p e r
  let s := q - r
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have heR : (0 : ℝ) < e := by exact_mod_cast he
  have hqm : q ≤ m := (maximalTrapTotal_le_cap p e r).trans hpm
  have hsq : s ≤ q := Nat.sub_le _ _
  have hsqR : (s : ℝ) ≤ q := by exact_mod_cast hsq
  have herror : (e : ℝ) * q ≤ r := maximalTrapTotal_error_le he
  have hmul : (e : ℝ) * s ≤ r :=
    (mul_le_mul_of_nonneg_left hsqR heR.le).trans herror
  have hratio0 : (0 : ℝ) ≤ (s : ℝ) / m := by positivity
  have hratio1 : (s : ℝ) / m ≤ 1 := by
    apply (div_le_one hmR).mpr
    exact_mod_cast (show s ≤ m by omega)
  have hpow : ((s : ℝ) / m) ^ r ≤ (s : ℝ) / m := by
    obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hr.ne'
    rw [pow_succ]
    exact (mul_le_mul_of_nonneg_right (pow_le_one₀ hratio0 hratio1) hratio0).trans_eq
      (one_mul _)
  have hden1 : 0 < Real.pi * (r : ℝ) := mul_pos Real.pi_pos hrR
  have hden2 : 0 < Real.pi * (e : ℝ) * m :=
    mul_pos (mul_pos Real.pi_pos heR) hmR
  have hgoal : ((s : ℝ) / m) / (Real.pi * r) ≤
      1 / (Real.pi * (e : ℝ) * m) := by
    apply (div_le_div_iff₀ hden1 hden2).mpr
    have hh : ((s : ℝ) / m) * (Real.pi * (e : ℝ) * m) =
        Real.pi * ((e : ℝ) * s) := by field_simp
    rw [hh]
    nlinarith [hmul, Real.pi_pos]
  unfold indexedTailTerm tailTerm
  exact (div_le_div_iff_of_pos_right hden1).mpr hpow |>.trans hgoal

theorem supportedTrapCap_le {m : ℕ} {a : ℚ}
    (ha : 0 ≤ a) (ha1 : a ≤ 1) : supportedTrapCap m a ≤ m := by
  have haR : (0 : ℝ) ≤ a := by exact_mod_cast ha
  have ha1R : (a : ℝ) ≤ 1 := by exact_mod_cast ha1
  have hmR : (0 : ℝ) ≤ m := Nat.cast_nonneg _
  have hpR : (supportedTrapCap m a : ℝ) ≤ (a : ℝ) * m :=
    Nat.floor_le (mul_nonneg haR hmR)
  have hpmR : (supportedTrapCap m a : ℝ) ≤ m := by nlinarith
  exact_mod_cast hpmR

theorem indexed_tail_sum_le_three_halves_over_pi {m : ℕ} {a e : ℚ}
    (hm : 0 < m) (ha : 0 ≤ a) (ha1 : a ≤ 1) (he : 0 < e) :
    (∑ r ∈ Finset.Icc 1 (roundedTrapSize e (supportedTrapCap m a)),
      indexedTailTerm m (supportedTrapCap m a) e r) ≤
      (3 / 2 : ℝ) / Real.pi := by
  let p := supportedTrapCap m a
  let R := roundedTrapSize e p
  have hpm : p ≤ m := supportedTrapCap_le ha ha1
  have hRpos : 1 ≤ R := by simp [R, roundedTrapSize]
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have heR : (0 : ℝ) < e := by exact_mod_cast he
  by_cases hlarge : (2 : ℝ) ≤ (e : ℝ) * m
  · have hpoint : ∀ r ∈ Finset.Icc 1 R,
        indexedTailTerm m p e r ≤ 1 / (Real.pi * (e : ℝ) * m) := by
      intro r hr
      exact indexed_tail_le_uniform hm hpm (Finset.mem_Icc.mp hr).1 he
    have hsum := Finset.sum_le_sum hpoint
    have hRbound : (R : ℝ) ≤ (e : ℝ) * m + 1 := by
      have hpfloor : (⌊(e : ℝ) * p⌋₊ : ℝ) ≤ (e : ℝ) * p :=
        Nat.floor_le (mul_nonneg heR.le (Nat.cast_nonneg _))
      have hpmR : (p : ℝ) ≤ m := by exact_mod_cast hpm
      simp only [R, roundedTrapSize, Nat.cast_add, Nat.cast_one]
      nlinarith
    have hcard : (Finset.Icc 1 R).card = R := by
      simp [Nat.card_Icc]
    have hsum' : (∑ r ∈ Finset.Icc 1 R, indexedTailTerm m p e r) ≤
        (R : ℝ) / (Real.pi * (e : ℝ) * m) := by
      simpa [hcard, div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using hsum
    have hden : 0 < Real.pi * (e : ℝ) * m :=
      mul_pos (mul_pos Real.pi_pos heR) hmR
    have hbound : (R : ℝ) / (Real.pi * (e : ℝ) * m) ≤
        (3 / 2 : ℝ) / Real.pi := by
      apply (div_le_div_iff₀ hden Real.pi_pos).mpr
      nlinarith [hRbound, hlarge, Real.pi_pos]
    exact hsum'.trans hbound
  · have hsmall : R ≤ 2 := by
      have hep : (e : ℝ) * p < 2 := by
        have hpmR : (p : ℝ) ≤ m := by exact_mod_cast hpm
        nlinarith
      have hfloor : ⌊(e : ℝ) * p⌋₊ < 2 :=
        (Nat.floor_lt (mul_nonneg heR.le (Nat.cast_nonneg _))).mpr hep
      dsimp [R, roundedTrapSize]
      omega
    have hsub : Finset.Icc 1 R ⊆ Finset.Icc 1 2 := by
      intro r hr
      simp only [Finset.mem_Icc] at hr ⊢
      omega
    have hpoint : (∑ r ∈ Finset.Icc 1 R, indexedTailTerm m p e r) ≤
        ∑ r ∈ Finset.Icc 1 R, 1 / (Real.pi * r) := by
      apply Finset.sum_le_sum
      intro r hr
      exact indexed_tail_le_one_over_r hm hpm (Finset.mem_Icc.mp hr).1
    have hsubsum : (∑ r ∈ Finset.Icc 1 R, 1 / (Real.pi * (r : ℝ))) ≤
        ∑ r ∈ Finset.Icc (1 : ℕ) 2, 1 / (Real.pi * (r : ℝ)) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hsub
      intro r hr _
      have hrpos : 0 < r := (Finset.mem_Icc.mp hr).1
      positivity
    have heval : (∑ r ∈ Finset.Icc (1 : ℕ) 2, 1 / (Real.pi * (r : ℝ))) =
        (3 / 2 : ℝ) / Real.pi := by
      have hIcc : Finset.Icc (1 : ℕ) 2 = {1, 2} := by decide
      rw [hIcc]
      norm_num
      field_simp [Real.pi_ne_zero]
      exact (show (1 : ℝ) * 2 + 1 = 3 by norm_num)
    exact hpoint.trans (hsubsum.trans heval.le)

theorem collapsed_tail_lt_one {m : ℕ} {a e : ℚ}
    (hm : 0 < m) (ha : 0 ≤ a) (ha1 : a ≤ 1) (he : 0 < e) :
    (2 : ℝ) * (∑ rs ∈ admissibleCollapsedWitnessSizes m a e,
      ((rs.2 : ℝ) / m) ^ rs.1 / (Real.pi * rs.1)) < 1 := by
  have hsum := (admissible_tail_le_indexed_tail m a e).trans
    (indexed_tail_sum_le_three_halves_over_pi hm ha ha1 he)
  have hpi : (3 : ℝ) / Real.pi < 1 :=
    (div_lt_one Real.pi_pos).mpr Real.pi_gt_three
  calc
    (2 : ℝ) * (∑ rs ∈ admissibleCollapsedWitnessSizes m a e,
      ((rs.2 : ℝ) / m) ^ rs.1 / (Real.pi * rs.1)) ≤
        2 * ((3 / 2 : ℝ) / Real.pi) := by gcongr
    _ = 3 / Real.pi := by ring
    _ < 1 := hpi

/-- Paterson's restricted halver exists at the advertised entropy depth for
every positive side arity. The matching sequence is noncomputable because the
probabilistic proof selects it by finite counting. -/
theorem exists_paterson_halver {m c : ℕ} {a e : ℚ}
    (hm : 0 < m) (hcpos : 0 < c)
    (ha : 0 < a) (ha1 : a ≤ 1) (he : 0 < e) (hehalf : e ≤ 1 / 2)
    (hc : patersonHalverDepthBound a e ≤ c) :
    ∃ gs : List (Equiv.Perm (Fin m)), gs.length = c ∧
      IsEpsilonAlphaHalver (patersonMatchingNetwork gs) e a ∧
      (patersonMatchingNetwork gs).depth ≤ c := by
  exact exists_halver_of_collapsed_tail_bound hm hcpos ha ha1 he hehalf hc
    (collapsed_tail_lt_one hm ha.le ha1 he)

theorem paterson_depth_bound_pos {a e : ℚ}
    (ha : 0 < a) (ha1 : a ≤ 1) (he : 0 < e) (hehalf : e ≤ 1 / 2) :
    0 < patersonHalverDepthBound a e := by
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have ha1R : (a : ℝ) ≤ 1 := by exact_mod_cast ha1
  have heR : (0 : ℝ) < e := by exact_mod_cast he
  have hehalfR : (e : ℝ) ≤ 1 / 2 := by
    have h : (e : ℝ) ≤ ((1 / 2 : ℚ) : ℝ) := Rat.cast_le.mpr hehalf
    norm_num at h ⊢
    exact h
  have he1R : (e : ℝ) < 1 := by linarith
  have hp0 : (0 : ℝ) < (e : ℝ) * a := mul_pos heR haR
  have hp1 : (e : ℝ) * a < 1 := by nlinarith
  have hq0 : (0 : ℝ) < (1 - (e : ℝ)) * a :=
    mul_pos (by linarith) haR
  have hq1 : (1 - (e : ℝ)) * a < 1 := by nlinarith
  have hnum : 0 ≤ Real.binEntropy ((e : ℝ) * a) +
      Real.binEntropy ((1 - (e : ℝ)) * a) :=
    add_nonneg (Real.binEntropy_nonneg hp0.le hp1.le)
      (Real.binEntropy_nonneg hq0.le hq1.le)
  have hden : 0 < -((e : ℝ) * a) *
      Real.log ((1 - (e : ℝ)) * a) :=
    mul_pos_of_neg_of_neg (neg_neg_of_pos hp0) (Real.log_neg hq0 hq1)
  have hratio : 0 ≤ depthRatio (a : ℝ) (e : ℝ) :=
    div_nonneg hnum hden.le
  rw [depthBound_eq_ratio]
  linarith

/-- Exact ceiling form, including the zero-wire case. -/
theorem exists_paterson_halver_all_arities {m : ℕ} {a e : ℚ}
    (ha : 0 < a) (ha1 : a ≤ 1) (he : 0 < e) (hehalf : e ≤ 1 / 2) :
    ∃ net : ComparatorNetwork (2 * m),
      IsEpsilonAlphaHalver net e a ∧
      net.depth ≤ ⌈patersonHalverDepthBound a e⌉₊ := by
  by_cases hm : 0 < m
  · let c := ⌈patersonHalverDepthBound a e⌉₊
    have hcpos : 0 < c := by
      exact (Nat.one_le_ceil_iff).mpr (paterson_depth_bound_pos ha ha1 he hehalf)
    have hc : patersonHalverDepthBound a e ≤ c := Nat.le_ceil _
    obtain ⟨gs, _, hhalver, hdepth⟩ :=
      exists_paterson_halver hm hcpos ha ha1 he hehalf hc
    exact ⟨patersonMatchingNetwork gs, hhalver, hdepth⟩
  · have hm0 : m = 0 := by omega
    subst m
    refine ⟨patersonMatchingNetwork ([] : List (Equiv.Perm (Fin 0))),
      patersonZeroHalver e a, ?_⟩
    have hzero := patersonMatchingNetwork_depth_le
      ([] : List (Equiv.Perm (Fin 0)))
    exact hzero.trans (Nat.zero_le _)

end Paterson
