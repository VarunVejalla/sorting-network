module

public import AKS.Halver.PatersonExistence
public import AKS.Halver.PatersonDepthBridge

/-! # Rounded size witnesses for Paterson's union bound -/

@[expose] public section

namespace Paterson

/-- The first integer strictly above `ε k`. -/
noncomputable def roundedTrapSize (e : ℚ) (k : ℕ) : ℕ :=
  ⌊(e : ℝ) * k⌋₊ + 1

/-- One minimal cardinality pair per possible sum. -/
noncomputable def roundedWitnessSizes (m : ℕ) (e : ℚ) : Finset (ℕ × ℕ) :=
  (Finset.range (m + 1)).image fun k =>
    (roundedTrapSize e k, k - roundedTrapSize e k)

theorem roundedTrapSize_le_of_lt {e : ℚ} {k t : ℕ}
    (he : 0 ≤ e) (h : (e : ℝ) * k < t) : roundedTrapSize e k ≤ t := by
  have heR : (0 : ℝ) ≤ e := by exact_mod_cast he
  have hx : (0 : ℝ) ≤ (e : ℝ) * k := mul_nonneg heR (Nat.cast_nonneg _)
  have hf : ⌊(e : ℝ) * k⌋₊ < t := (Nat.floor_lt hx).mpr h
  exact Nat.succ_le_iff.mpr hf

theorem roundedTrapSize_gt (e : ℚ) (k : ℕ) :
    (e : ℝ) * k < roundedTrapSize e k := by
  simpa [roundedTrapSize] using Nat.lt_floor_add_one ((e : ℝ) * k)

/-- Every possible trap with `t ≤ k/2` contains the minimal rounded-size
witness at the same total size. -/
theorem roundedWitnessSizes_cover {m k t : ℕ} {e : ℚ}
    (he : 0 ≤ e) (hkm : k ≤ m) (ht : (e : ℝ) * k < t)
    (htk : 2 * t ≤ k) :
    ∃ rs ∈ roundedWitnessSizes m e,
      rs.1 ≤ t ∧ k - t ≤ rs.2 ∧ rs.2 ≤ m := by
  let r := roundedTrapSize e k
  have hrt : r ≤ t := roundedTrapSize_le_of_lt he ht
  refine ⟨(r, k - r), Finset.mem_image.mpr ?_, hrt, ?_, ?_⟩
  · exact ⟨k, Finset.mem_range.mpr (by omega), rfl⟩
  · omega
  · omega

/-- The rounded witnesses that can actually be used in the sharp entropy
estimate have positive first size, first size no larger than second, and
both parts fit inside the supported fraction. -/
noncomputable def admissibleRoundedWitnessSizes (m : ℕ) (a e : ℚ) : Finset (ℕ × ℕ) :=
  (roundedWitnessSizes m e).filter fun rs =>
    rs.1 ≤ rs.2 ∧ ((rs.1 + rs.2 : ℕ) : ℝ) ≤ (a : ℝ) * m

theorem admissibleRoundedWitnessSizes_cover {m k t : ℕ} {a e : ℚ}
    (he : 0 ≤ e) (hkm : k ≤ m) (hk : (k : ℝ) ≤ (a : ℝ) * m)
    (ht : (e : ℝ) * k < t) (htk : 2 * t ≤ k) :
    ∃ rs ∈ admissibleRoundedWitnessSizes m a e,
      rs.1 ≤ t ∧ k - t ≤ rs.2 ∧ rs.2 ≤ m := by
  let r := roundedTrapSize e k
  have hrt : r ≤ t := roundedTrapSize_le_of_lt he ht
  have hrk : r ≤ k := by omega
  refine ⟨(r, k - r), Finset.mem_filter.mpr ?_, hrt, ?_, ?_⟩
  · constructor
    · exact Finset.mem_image.mpr ⟨k, Finset.mem_range.mpr (by omega), rfl⟩
    · constructor
      · omega
      · simpa [Nat.add_sub_of_le hrk] using hk
  · omega
  · omega

/-- The scalar union bound now has just one rounded candidate per supported
total size. The probability estimate itself remains an explicit hypothesis. -/
theorem exists_halver_of_rounded_size_bound {m c : ℕ} {a e : ℚ}
    (hm : 0 < m) (hcpos : 0 < c) (ha : a ≤ 1) (he : 0 ≤ e)
    (hsmall : 2 * (∑ rs ∈ admissibleRoundedWitnessSizes m a e,
      (m.choose rs.1 : ℚ) * m.choose rs.2 *
        ((rs.2 : ℚ) / m) ^ (rs.1 * c)) < 1) :
    ∃ gs : List (Equiv.Perm (Fin m)), gs.length = c ∧
      IsEpsilonAlphaHalver (patersonMatchingNetwork gs) e a ∧
      (patersonMatchingNetwork gs).depth ≤ c := by
  apply exists_halver_of_size_bound hm hcpos ha
    (admissibleRoundedWitnessSizes m a e)
  · intro k hk t ht htk
    have haR : (a : ℝ) ≤ 1 := by exact_mod_cast ha
    have hkmR : (k : ℝ) ≤ m := by
      have hmR : (0 : ℝ) ≤ m := Nat.cast_nonneg _
      nlinarith
    have hkm : k ≤ m := by exact_mod_cast hkmR
    exact admissibleRoundedWitnessSizes_cover he hkm hk ht htk
  · exact hsmall

/-- Every retained rounded witness automatically meets the hypotheses of
the entropy-depth estimate. -/
theorem admissible_witness_failure_term_le {m c : ℕ} {a e : ℚ}
    (ha : 0 < a) (ha1 : a ≤ 1) (he : 0 < e) (hehalf : e ≤ 1 / 2)
    (hc : patersonHalverDepthBound a e ≤ c)
    {rs : ℕ × ℕ} (hrs : rs ∈ admissibleRoundedWitnessSizes m a e) :
    (m.choose rs.1 : ℝ) * m.choose rs.2 *
        ((rs.2 : ℝ) / m) ^ (rs.1 * c) ≤
      ((rs.2 : ℝ) / m) ^ rs.1 / (Real.pi * rs.1) := by
  obtain ⟨himage, hle, hcovered⟩ := Finset.mem_filter.mp hrs
  obtain ⟨k, hk, hpair⟩ := Finset.mem_image.mp himage
  have hrpos : 0 < roundedTrapSize e k := by simp [roundedTrapSize]
  have hkm : k ≤ m := by simpa using (Finset.mem_range.mp hk)
  have hpair' : rs = (roundedTrapSize e k, k - roundedTrapSize e k) := hpair.symm
  subst rs
  have hs : roundedTrapSize e k ≤ k - roundedTrapSize e k := by simpa using hle
  have hrk : roundedTrapSize e k ≤ k := by omega
  have hsm : roundedTrapSize e k + (k - roundedTrapSize e k) ≤ m := by omega
  have hcov : ((roundedTrapSize e k + (k - roundedTrapSize e k) : ℕ) : ℝ) ≤
      (a : ℝ) * m := by simpa using hcovered
  have herr : (e : ℝ) *
      (roundedTrapSize e k + (k - roundedTrapSize e k) : ℕ) ≤
      roundedTrapSize e k := by
    rw [Nat.add_sub_of_le hrk]
    exact (roundedTrapSize_gt e k).le
  exact witness_failure_term_le ha ha1 he hehalf hrpos hs hsm hcov herr hc

/-- Reduces uniform halver existence to a single explicit sum of rounded
Stirling tails. No probability or entropy bound remains in this premise. -/
theorem exists_halver_of_rounded_tail_bound {m c : ℕ} {a e : ℚ}
    (hm : 0 < m) (hcpos : 0 < c)
    (ha : 0 < a) (ha1 : a ≤ 1) (he : 0 < e) (hehalf : e ≤ 1 / 2)
    (hc : patersonHalverDepthBound a e ≤ c)
    (htail : (2 : ℝ) * (∑ rs ∈ admissibleRoundedWitnessSizes m a e,
      ((rs.2 : ℝ) / m) ^ rs.1 / (Real.pi * rs.1)) < 1) :
    ∃ gs : List (Equiv.Perm (Fin m)), gs.length = c ∧
      IsEpsilonAlphaHalver (patersonMatchingNetwork gs) e a ∧
      (patersonMatchingNetwork gs).depth ≤ c := by
  apply exists_halver_of_rounded_size_bound hm hcpos ha1 he.le
  have hsum : (∑ rs ∈ admissibleRoundedWitnessSizes m a e,
      (m.choose rs.1 : ℝ) * m.choose rs.2 *
        ((rs.2 : ℝ) / m) ^ (rs.1 * c)) ≤
      ∑ rs ∈ admissibleRoundedWitnessSizes m a e,
        ((rs.2 : ℝ) / m) ^ rs.1 / (Real.pi * rs.1) := by
    apply Finset.sum_le_sum
    intro rs hrs
    exact admissible_witness_failure_term_le ha ha1 he hehalf hc hrs
  have hreal : (2 : ℝ) * (∑ rs ∈ admissibleRoundedWitnessSizes m a e,
      (m.choose rs.1 : ℝ) * m.choose rs.2 *
        ((rs.2 : ℝ) / m) ^ (rs.1 * c)) < 1 :=
    (mul_le_mul_of_nonneg_left hsum (by norm_num)).trans_lt htail
  apply (Rat.cast_lt (K := ℝ)).mp
  convert hreal using 1 <;> push_cast <;> ring

end Paterson
