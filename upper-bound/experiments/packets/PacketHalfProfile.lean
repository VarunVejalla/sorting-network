import PacketProfile

/-! The actual repair atoms are 32-wire rank intervals. This file carries the
sorted-profile scale transfer down to that fragment size. -/

namespace Chvatal.PacketAlignment

open Finset BigOperators

def profileHalf (K X i : Nat) : Nat :=
  profileTail (32 * K) X (32 * (i + 1)) - profileTail (32 * K) X (32 * i)

private theorem profileTail_interval_count32 (m X a b : Nat)
    (hab : a ≤ b) (hb : b ≤ m) :
    profileTail m X b - profileTail m X a = min (b - a) (X - (m - b)) := by
  by_cases h0 : X ≤ m - b
  · simp [profileTail, h0]
  · by_cases h1 : X ≤ m - a
    · simp only [profileTail, Nat.min_def]
      split_ifs <;> omega
    · simp only [profileTail, Nat.min_def]
      split_ifs <;> omega

private theorem sum_profileTail32_differences (m K X : Nat) (hK : 32 * K ≤ m) :
    (∑ i ∈ range K,
      (profileTail m X (32 * (i + 1)) - profileTail m X (32 * i))) =
      profileTail m X (32 * K) - profileTail m X 0 := by
  induction K with
  | zero => simp
  | succ K ih =>
      rw [sum_range_succ, ih (by omega)]
      simp only [profileTail]
      omega

theorem profileHalf_formula (K X i : Nat) (hi : i < K) :
    profileHalf K X i = min 32 (X - (32 * K - 32 * (i + 1))) := by
  have hab : 32 * i ≤ 32 * (i + 1) := by omega
  have hb : 32 * (i + 1) ≤ 32 * K := by omega
  unfold profileHalf
  rw [profileTail_interval_count32 (32 * K) X (32 * i) (32 * (i + 1)) hab hb]
  simp [Nat.mul_add]

private theorem profileHalf_mono_X (K X Y i : Nat) (hXY : Y ≤ X)
    (hi : i < K) : profileHalf K Y i ≤ profileHalf K X i := by
  rw [profileHalf_formula K Y i hi, profileHalf_formula K X i hi]
  exact min_le_min le_rfl (Nat.sub_le_sub_right hXY _)

theorem sum_profileHalf_eq_total (K X : Nat) (hX : X ≤ 32 * K) :
    (∑ i ∈ range K, profileHalf K X i) = X := by
  simp only [profileHalf]
  rw [sum_profileTail32_differences (32 * K) K X (by omega)]
  simp only [profileTail]
  omega

def profileHalfMean (K q : Nat) (frac : Real) (i : Nat) : Real :=
  (1 - frac) * profileHalf K q i + frac * profileHalf K (q + 1) i

theorem profileHalfMean_sum (K q : Nat) (frac : Real) (hq : q < 32 * K) :
    (∑ i ∈ range K, profileHalfMean K q frac i) = q + frac := by
  have hqsum : (∑ i ∈ range K, (profileHalf K q i : Real)) = q := by
    exact_mod_cast sum_profileHalf_eq_total K q (by omega)
  have hq1sum : (∑ i ∈ range K, (profileHalf K (q + 1) i : Real)) = q + 1 := by
    exact_mod_cast sum_profileHalf_eq_total K (q + 1) (by omega)
  unfold profileHalfMean
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hqsum, hq1sum]
  ring

theorem profileHalfMean_L1_exact (K X q : Nat) (frac : Real) (hq : q < 32 * K)
    (hXbound : X ≤ 32 * K) (hfrac0 : 0 ≤ frac) (hfrac1 : frac ≤ 1) :
    (∑ i ∈ range K,
      |(profileHalf K X i : Real) - profileHalfMean K q frac i|) =
        |(X : Real) - (q + frac)| := by
  have hmean := profileHalfMean_sum K q frac hq
  have hxsum : (∑ i ∈ range K, (profileHalf K X i : Real)) = X := by
    exact_mod_cast sum_profileHalf_eq_total K X hXbound
  by_cases hX : X ≤ q
  · have hpoint : ∀ i ∈ range K,
        (profileHalf K X i : Real) ≤ profileHalfMean K q frac i := by
      intro i hi
      have hbase := profileHalf_mono_X K q X i (by omega) (mem_range.mp hi)
      have hnext := profileHalf_mono_X K (q + 1) q i (by omega) (mem_range.mp hi)
      unfold profileHalfMean
      have hn : (profileHalf K q i : Real) ≤ profileHalf K (q + 1) i := by exact_mod_cast hnext
      have hb : (profileHalf K X i : Real) ≤ profileHalf K q i := by exact_mod_cast hbase
      nlinarith [hfrac0, hfrac1]
    calc
      (∑ i ∈ range K,
          |(profileHalf K X i : Real) - profileHalfMean K q frac i|) =
          ∑ i ∈ range K, (profileHalfMean K q frac i - (profileHalf K X i : Real)) := by
        apply sum_congr rfl
        intro i hi
        rw [abs_of_nonpos (by linarith [hpoint i hi])]
        ring
      _ = (∑ i ∈ range K, profileHalfMean K q frac i) -
          (∑ i ∈ range K, (profileHalf K X i : Real)) := by rw [Finset.sum_sub_distrib]
      _ = |(X : Real) - (q + frac)| := by
        rw [hmean, hxsum]
        have hXR : (X : Real) ≤ (q : Real) := by exact_mod_cast hX
        rw [abs_of_nonpos (by linarith [hfrac0])]
        ring
  · have hX' : q + 1 ≤ X := by omega
    have hpoint : ∀ i ∈ range K,
        profileHalfMean K q frac i ≤ (profileHalf K X i : Real) := by
      intro i hi
      have hbase := profileHalf_mono_X K X (q + 1) i (by omega) (mem_range.mp hi)
      have hnext := profileHalf_mono_X K (q + 1) q i (by omega) (mem_range.mp hi)
      unfold profileHalfMean
      have hn : (profileHalf K q i : Real) ≤ profileHalf K (q + 1) i := by exact_mod_cast hnext
      have hb : (profileHalf K (q + 1) i : Real) ≤ profileHalf K X i := by exact_mod_cast hbase
      nlinarith [hfrac0, hfrac1]
    calc
      (∑ i ∈ range K,
          |(profileHalf K X i : Real) - profileHalfMean K q frac i|) =
          ∑ i ∈ range K, ((profileHalf K X i : Real) - profileHalfMean K q frac i) := by
        apply sum_congr rfl
        intro i hi
        rw [abs_of_nonneg (by linarith [hpoint i hi])]
      _ = (∑ i ∈ range K, (profileHalf K X i : Real)) -
          (∑ i ∈ range K, profileHalfMean K q frac i) := by rw [Finset.sum_sub_distrib]
      _ = |(X : Real) - (q + frac)| := by
        rw [hxsum, hmean]
        have hXR : (q : Real) + 1 ≤ (X : Real) := by exact_mod_cast hX'
        rw [abs_of_nonneg (by linarith [hfrac1])]

theorem sortedBool_profileHalf_trueCount {K : Nat} (v : Fin (32 * K) → Bool)
    (hv : Monotone v) (X : Nat) (hX : boolTrueCount v = X) (i : Nat) (hi : i < K) :
    boolTrueCount (fun j : Fin 32 => v ⟨32 * i + j,
      by have hj := j.isLt; omega⟩) = profileHalf K X i := by
  let m := 32 * K
  let a := 32 * i
  let b := 32 * (i + 1)
  have ha : a ≤ m := by dsimp [a, m]; omega
  have hb : b ≤ m := by dsimp [b, m]; omega
  have hab : a + 32 = b := by dsimp [a, b]; omega
  let Plo : Fin a → Bool := fun j =>
    v (Fin.cast (Nat.add_sub_of_le ha) (Fin.castAdd (m - a) j))
  let Phi : Fin b → Bool := fun j =>
    v (Fin.cast (Nat.add_sub_of_le hb) (Fin.castAdd (m - b) j))
  let C : Fin 32 → Bool := fun j => v ⟨a + j, by dsimp [a, m]; have hj := j.isLt; omega⟩
  have he : Fin.append Plo C = Phi ∘ Fin.cast hab := by
    funext k
    refine Fin.addCases (fun j => ?_) (fun j => ?_) k
    · simp only [Fin.append_left, Function.comp_apply]
      apply congrArg v
      apply Fin.ext
      simp only [Plo, Phi, Fin.val_cast, Fin.val_castAdd, Fin.val_mk]
    · simp only [Fin.append_right, Function.comp_apply]
      apply congrArg v
      apply Fin.ext
      simp only [C, Phi, Fin.val_cast, Fin.val_castAdd, Fin.val_natAdd, Fin.val_mk]
  have hcounts : boolTrueCount Phi = boolTrueCount Plo + boolTrueCount C := by
    calc
      boolTrueCount Phi = boolTrueCount (Phi ∘ Fin.cast hab) :=
        (boolTrueCount_finCast hab Phi).symm
      _ = boolTrueCount (Fin.append Plo C) := congrArg boolTrueCount he.symm
      _ = boolTrueCount Plo + boolTrueCount C := boolTrueCount_append_general Plo C
  have hlo := sortedBool_prefix_trueCount v hv ha
  have hhi := sortedBool_prefix_trueCount v hv hb
  rw [hX] at hlo hhi
  change boolTrueCount C = profileHalf K X i
  have hC : boolTrueCount C = boolTrueCount Phi - boolTrueCount Plo := by omega
  unfold profileHalf profileTail
  rw [hC, hhi, hlo]

theorem sortedPackets_halfProfile_L1_exact {c K : Nat}
    (V : Fin c → Fin (32 * K) → Bool) (hV : ∀ i, Monotone (V i))
    (q : Nat) (frac : Real) (hq : q < 32 * K)
    (hfrac0 : 0 ≤ frac) (hfrac1 : frac ≤ 1) :
    (∑ i : Fin c, ∑ j : Fin K,
      |(boolTrueCount (fun k : Fin 32 => V i ⟨32 * j.val + k,
        by have hj := j.isLt; have hk := k.isLt; omega⟩) : Real) -
          profileHalfMean K q frac j.val|) =
      ∑ i : Fin c, |(boolTrueCount (V i) : Real) - (q + frac)| := by
  let X : Fin c → Nat := fun i => boolTrueCount (V i)
  have hcell (i : Fin c) (j : Fin K) :
      boolTrueCount (fun k : Fin 32 => V i ⟨32 * j.val + k,
        by have hk := k.isLt; omega⟩) = profileHalf K (X i) j.val := by
    exact sortedBool_profileHalf_trueCount (V i) (hV i) (X i) rfl j.val j.isLt
  have hprofiles : (∑ i : Fin c, ∑ j : Fin K,
      |(boolTrueCount (fun k : Fin 32 => V i ⟨32 * j.val + k,
        by have hj := j.isLt; have hk := k.isLt; omega⟩) : Real) -
          profileHalfMean K q frac j.val|) =
      ∑ i : Fin c, ∑ j : Fin K,
        |(profileHalf K (X i) j.val : Real) - profileHalfMean K q frac j.val| := by
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [hcell i j]
  calc
    _ = ∑ i : Fin c, ∑ j : Fin K,
        |(profileHalf K (X i) j.val : Real) - profileHalfMean K q frac j.val| := hprofiles
    _ = ∑ i : Fin c, |(X i : Real) - (q + frac)| := by
      apply Finset.sum_congr rfl
      intro i _
      calc
        (∑ j : Fin K,
            |(profileHalf K (X i) j.val : Real) - profileHalfMean K q frac j.val|) =
            ∑ j ∈ range K,
              |(profileHalf K (X i) j : Real) - profileHalfMean K q frac j| :=
          Fin.sum_univ_eq_sum_range (fun j : Nat =>
            |(profileHalf K (X i) j : Real) - profileHalfMean K q frac j|) K
        _ = |(X i : Real) - (q + frac)| :=
          profileHalfMean_L1_exact K (X i) q frac hq (by
            dsimp [X]
            unfold boolTrueCount
            simpa using Fintype.card_subtype_le (fun k : Fin (32 * K) => V i k = true)) hfrac0 hfrac1

theorem sortedPackets_halfProfile_L1_sq {c K : Nat}
    (V : Fin c → Fin (32 * K) → Bool) (hV : ∀ i, Monotone (V i))
    (q : Nat) (frac : Real) (hq : q < 32 * K)
    (hfrac0 : 0 ≤ frac) (hfrac1 : frac ≤ 1) :
    ((∑ i : Fin c, ∑ j : Fin K,
      |(boolTrueCount (fun k : Fin 32 => V i ⟨32 * j.val + k,
        by have hj := j.isLt; have hk := k.isLt; omega⟩) : Real) -
          profileHalfMean K q frac j.val|)^2) ≤
      (c : Real) * ∑ i : Fin c,
        ((boolTrueCount (V i) : Real) - (q + frac))^2 := by
  rw [sortedPackets_halfProfile_L1_exact V hV q frac hq hfrac0 hfrac1]
  simpa [sq_abs, mul_comm] using
    (Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
      (fun i : Fin c => |(boolTrueCount (V i) : Real) - (q + frac)|)
      (fun _ => (1 : Real)))
