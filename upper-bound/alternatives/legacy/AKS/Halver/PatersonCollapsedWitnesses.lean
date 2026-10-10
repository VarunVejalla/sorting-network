module

public import AKS.Halver.PatersonWitnesses

/-! # One maximal witness per rounded error count -/

@[expose] public section

namespace Paterson

/-- Largest allowed total size under the supported fraction. -/
noncomputable def supportedTrapCap (m : ℕ) (a : ℚ) : ℕ :=
  ⌊(a : ℝ) * m⌋₊

/-- Largest total size compatible with a rounded error count, capped at the
supported size. -/
noncomputable def maximalTrapTotal (p : ℕ) (e : ℚ) (r : ℕ) : ℕ :=
  min p ⌊(r : ℝ) / (e : ℝ)⌋₊

noncomputable def collapsedWitnessSizes (m : ℕ) (a e : ℚ) : Finset (ℕ × ℕ) :=
  let p := supportedTrapCap m a
  (Finset.Icc 1 (roundedTrapSize e p)).image fun r =>
    (r, maximalTrapTotal p e r - r)

theorem le_supportedTrapCap {m k : ℕ} {a : ℚ}
    (hk : (k : ℝ) ≤ (a : ℝ) * m) : k ≤ supportedTrapCap m a := by
  exact Nat.le_floor hk

theorem roundedTrapSize_mono {e : ℚ} (he : 0 ≤ e) :
    Monotone (roundedTrapSize e) := by
  intro k l hkl
  simp only [roundedTrapSize]
  apply Nat.add_le_add_right
  apply Nat.floor_mono
  have heR : (0 : ℝ) ≤ e := by exact_mod_cast he
  exact mul_le_mul_of_nonneg_left (by exact_mod_cast hkl) heR

theorem le_maximalTrapTotal {e : ℚ} {p k r : ℕ}
    (he : 0 < e) (hkp : k ≤ p)
    (hkr : (e : ℝ) * k < r) : k ≤ maximalTrapTotal p e r := by
  apply le_min hkp
  have heR : (0 : ℝ) < e := by exact_mod_cast he
  apply Nat.le_floor
  apply (le_div_iff₀ heR).mpr
  simpa [mul_comm] using hkr.le

theorem maximalTrapTotal_le_cap (p : ℕ) (e : ℚ) (r : ℕ) :
    maximalTrapTotal p e r ≤ p := min_le_left _ _

theorem maximalTrapTotal_error_le {e : ℚ} {p r : ℕ}
    (he : 0 < e) :
    (e : ℝ) * maximalTrapTotal p e r ≤ r := by
  have heR : (0 : ℝ) < e := by exact_mod_cast he
  have hfloor : (⌊(r : ℝ) / (e : ℝ)⌋₊ : ℝ) ≤ (r : ℝ) / e :=
    Nat.floor_le (div_nonneg (Nat.cast_nonneg _) heR.le)
  have htotal : maximalTrapTotal p e r ≤ ⌊(r : ℝ) / (e : ℝ)⌋₊ :=
    min_le_right _ _
  have htotalR : (maximalTrapTotal p e r : ℝ) ≤
      ⌊(r : ℝ) / (e : ℝ)⌋₊ := by exact_mod_cast htotal
  have hh := mul_le_mul_of_nonneg_left (htotalR.trans hfloor) heR.le
  field_simp at hh
  nlinarith

/-- A failing trap contains the maximal-total representative for its rounded
error count. This is the combinatorial reduction used by Paterson's appendix. -/
theorem collapsedWitnessSizes_cover {m k t : ℕ} {a e : ℚ}
    (ha : a ≤ 1) (he : 0 < e) (hk : (k : ℝ) ≤ (a : ℝ) * m)
    (ht : (e : ℝ) * k < t) (htk : 2 * t ≤ k) :
    ∃ rs ∈ collapsedWitnessSizes m a e,
      rs.1 ≤ t ∧ k - t ≤ rs.2 ∧ rs.2 ≤ m := by
  let p := supportedTrapCap m a
  let r := roundedTrapSize e k
  let q := maximalTrapTotal p e r
  have hkp : k ≤ p := le_supportedTrapCap hk
  have hrp : r ≤ roundedTrapSize e p :=
    roundedTrapSize_mono he.le hkp
  have hrpos : 1 ≤ r := by simp [r, roundedTrapSize]
  have hrt : r ≤ t := roundedTrapSize_le_of_lt he.le ht
  have hkr : (e : ℝ) * k < r := roundedTrapSize_gt e k
  have hkq : k ≤ q := le_maximalTrapTotal he hkp hkr
  have hrq : r ≤ q := by omega
  have hqm : q ≤ m := by
    have hpmR : (p : ℝ) ≤ m := by
      have ha : (a : ℝ) * m ≤ m := by
        have ham : (a : ℝ) ≤ 1 := by exact_mod_cast ha
        have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg _
        nlinarith
      have hnonneg : (0 : ℝ) ≤ (a : ℝ) * m := (Nat.cast_nonneg k).trans hk
      exact (Nat.floor_le hnonneg).trans ha
    have hpm : p ≤ m := by exact_mod_cast hpmR
    exact (maximalTrapTotal_le_cap p e r).trans hpm
  refine ⟨(r, q - r), Finset.mem_image.mpr ?_, hrt, ?_, ?_⟩
  · exact ⟨r, Finset.mem_Icc.mpr ⟨hrpos, hrp⟩, rfl⟩
  · omega
  · omega

noncomputable def admissibleCollapsedWitnessSizes (m : ℕ) (a e : ℚ) :
    Finset (ℕ × ℕ) :=
  (collapsedWitnessSizes m a e).filter fun rs =>
    rs.1 ≤ rs.2 ∧ ((rs.1 + rs.2 : ℕ) : ℝ) ≤ (a : ℝ) * m

theorem admissibleCollapsedWitnessSizes_cover {m k t : ℕ} {a e : ℚ}
    (ha : a ≤ 1) (he : 0 < e)
    (hk : (k : ℝ) ≤ (a : ℝ) * m)
    (ht : (e : ℝ) * k < t) (htk : 2 * t ≤ k) :
    ∃ rs ∈ admissibleCollapsedWitnessSizes m a e,
      rs.1 ≤ t ∧ k - t ≤ rs.2 ∧ rs.2 ≤ m := by
  let p := supportedTrapCap m a
  let r := roundedTrapSize e k
  let q := maximalTrapTotal p e r
  have hkp : k ≤ p := le_supportedTrapCap hk
  have hrp : r ≤ roundedTrapSize e p := roundedTrapSize_mono he.le hkp
  have hrpos : 1 ≤ r := by simp [r, roundedTrapSize]
  have hrt : r ≤ t := roundedTrapSize_le_of_lt he.le ht
  have hkq : k ≤ q := le_maximalTrapTotal he hkp (roundedTrapSize_gt e k)
  have hrq : r ≤ q := by omega
  have hrs : r ≤ q - r := by omega
  have hpNonneg : (0 : ℝ) ≤ (a : ℝ) * m := (Nat.cast_nonneg k).trans hk
  have hpBound : (p : ℝ) ≤ (a : ℝ) * m := Nat.floor_le hpNonneg
  have hqBound : (q : ℝ) ≤ (a : ℝ) * m := by
    have hqp : q ≤ p := maximalTrapTotal_le_cap p e r
    exact (by exact_mod_cast hqp : (q : ℝ) ≤ p).trans hpBound
  have hqm : q ≤ m := by
    have haR : (a : ℝ) ≤ 1 := by exact_mod_cast ha
    have hmR : (0 : ℝ) ≤ m := Nat.cast_nonneg _
    have hqRm : (q : ℝ) ≤ m := by nlinarith
    exact_mod_cast hqRm
  refine ⟨(r, q - r), Finset.mem_filter.mpr ?_, hrt, ?_, ?_⟩
  · constructor
    · exact Finset.mem_image.mpr ⟨r, Finset.mem_Icc.mpr ⟨hrpos, hrp⟩, rfl⟩
    · constructor
      · exact hrs
      · simpa [Nat.add_sub_of_le hrq] using hqBound
  · omega
  · omega

theorem exists_halver_of_collapsed_size_bound {m c : ℕ} {a e : ℚ}
    (hm : 0 < m) (hcpos : 0 < c) (ha : a ≤ 1) (he : 0 < e)
    (hsmall : 2 * (∑ rs ∈ admissibleCollapsedWitnessSizes m a e,
      (m.choose rs.1 : ℚ) * m.choose rs.2 *
        ((rs.2 : ℚ) / m) ^ (rs.1 * c)) < 1) :
    ∃ gs : List (Equiv.Perm (Fin m)), gs.length = c ∧
      IsEpsilonAlphaHalver (patersonMatchingNetwork gs) e a ∧
      (patersonMatchingNetwork gs).depth ≤ c := by
  apply exists_halver_of_size_bound hm hcpos ha
    (admissibleCollapsedWitnessSizes m a e)
  · intro k hk t ht htk
    exact admissibleCollapsedWitnessSizes_cover ha he hk ht htk
  · exact hsmall

theorem admissible_collapsed_failure_term_le {m c : ℕ} {a e : ℚ}
    (ha : 0 < a) (ha1 : a ≤ 1) (he : 0 < e) (hehalf : e ≤ 1 / 2)
    (hc : patersonHalverDepthBound a e ≤ c)
    {rs : ℕ × ℕ} (hrs : rs ∈ admissibleCollapsedWitnessSizes m a e) :
    (m.choose rs.1 : ℝ) * m.choose rs.2 *
        ((rs.2 : ℝ) / m) ^ (rs.1 * c) ≤
      ((rs.2 : ℝ) / m) ^ rs.1 / (Real.pi * rs.1) := by
  obtain ⟨himage, hle, hcovered⟩ := Finset.mem_filter.mp hrs
  obtain ⟨r, hrange, hpair⟩ := Finset.mem_image.mp himage
  have hrpos : 0 < r := (Finset.mem_Icc.mp hrange).1
  let p := supportedTrapCap m a
  let q := maximalTrapTotal p e r
  have hpair' : rs = (r, q - r) := hpair.symm
  subst rs
  have hrs' : r ≤ q - r := by simpa [q] using hle
  have hrq : r ≤ q := by omega
  have hcov : ((r + (q - r) : ℕ) : ℝ) ≤ (a : ℝ) * m := by
    simpa [q] using hcovered
  have hsm : r + (q - r) ≤ m := by
    have haR : (a : ℝ) ≤ 1 := by exact_mod_cast ha1
    have hmR : (0 : ℝ) ≤ m := Nat.cast_nonneg _
    have hqmR : (q : ℝ) ≤ m := by
      rw [Nat.add_sub_of_le hrq] at hcov
      nlinarith
    have hqm : q ≤ m := by exact_mod_cast hqmR
    omega
  have herr : (e : ℝ) * (r + (q - r) : ℕ) ≤ r := by
    rw [Nat.add_sub_of_le hrq]
    exact maximalTrapTotal_error_le he
  exact witness_failure_term_le ha ha1 he hehalf hrpos hrs' hsm hcov herr hc

/-- The exact remaining analytic obligation for Paterson's all-arity
restricted halver: a finite sum with one term per rounded error count. -/
theorem exists_halver_of_collapsed_tail_bound {m c : ℕ} {a e : ℚ}
    (hm : 0 < m) (hcpos : 0 < c)
    (ha : 0 < a) (ha1 : a ≤ 1) (he : 0 < e) (hehalf : e ≤ 1 / 2)
    (hc : patersonHalverDepthBound a e ≤ c)
    (htail : (2 : ℝ) * (∑ rs ∈ admissibleCollapsedWitnessSizes m a e,
      ((rs.2 : ℝ) / m) ^ rs.1 / (Real.pi * rs.1)) < 1) :
    ∃ gs : List (Equiv.Perm (Fin m)), gs.length = c ∧
      IsEpsilonAlphaHalver (patersonMatchingNetwork gs) e a ∧
      (patersonMatchingNetwork gs).depth ≤ c := by
  apply exists_halver_of_collapsed_size_bound hm hcpos ha1 he
  have hsum : (∑ rs ∈ admissibleCollapsedWitnessSizes m a e,
      (m.choose rs.1 : ℝ) * m.choose rs.2 *
        ((rs.2 : ℝ) / m) ^ (rs.1 * c)) ≤
      ∑ rs ∈ admissibleCollapsedWitnessSizes m a e,
        ((rs.2 : ℝ) / m) ^ rs.1 / (Real.pi * rs.1) := by
    apply Finset.sum_le_sum
    intro rs hrs
    exact admissible_collapsed_failure_term_le ha ha1 he hehalf hc hrs
  have hreal : (2 : ℝ) * (∑ rs ∈ admissibleCollapsedWitnessSizes m a e,
      (m.choose rs.1 : ℝ) * m.choose rs.2 *
        ((rs.2 : ℝ) / m) ^ (rs.1 * c)) < 1 :=
    (mul_le_mul_of_nonneg_left hsum (by norm_num)).trans_lt htail
  apply (Rat.cast_lt (K := ℝ)).mp
  convert hreal using 1 <;> push_cast <;> ring

end Paterson
