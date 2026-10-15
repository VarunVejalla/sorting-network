import PacketCountBridge
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-! A scale-transfer fact for sorted Boolean packets. It compares the counts
in fixed 64-wire rank cells to the ideal sorted profile at the same total
count, avoiding the incorrect assumption that these cells are individually
close to the packet mean. -/

namespace Chvatal.PacketAlignment

open Finset BigOperators

/-- Number of ones in the first `r` ranks of a sorted `m`-wire Boolean packet
with `X` ones. -/
def profileTail (m X r : Nat) : Nat := X - (m - r)

/-- Ideal number of ones in cell `i` of a sorted packet split into 64-wire
cells. This is the difference between two consecutive suffix counts. -/
def profileCell (K X i : Nat) : Nat :=
  profileTail (64 * K) X (64 * (i + 1)) - profileTail (64 * K) X (64 * i)

theorem boolTrueCount_append_general {m n : Nat} (A : Fin m → Bool) (B : Fin n → Bool) :
    boolTrueCount (Fin.append A B) = boolTrueCount A + boolTrueCount B := by
  let p : Fin m ⊕ Fin n → Prop
    | Sum.inl i => A i = true
    | Sum.inr j => B j = true
  have hp (s : Fin m ⊕ Fin n) : p s ↔ Fin.append A B (finSumFinEquiv s) = true := by
    cases s with
    | inl i => simp [p]
    | inr j =>
        change B j = true ↔ Fin.addCases A B (Fin.natAdd m j) = true
        rw [Fin.addCases_right]
  let e : {i : Fin (m + n) // Fin.append A B i = true} ≃
      Sum ({i : Fin m // A i = true}) ({j : Fin n // B j = true}) :=
    (finSumFinEquiv.subtypeEquiv hp).symm.trans Equiv.subtypeSum
  unfold boolTrueCount
  rw [← Fintype.card_sum]
  exact Fintype.card_congr e

/-- In an increasing Boolean sequence, the suffix of length `r` contains
exactly `min r X` ones, where `X` is the total number of ones. -/
theorem sortedBool_suffix_trueCount {m r : Nat} (v : Fin m → Bool)
    (hv : Monotone v) (hr : r ≤ m) :
    boolTrueCount (fun j : Fin r => v
      (Fin.cast (Nat.sub_add_cancel hr) (Fin.natAdd (m - r) j))) =
      min r (boolTrueCount v) := by
  by_cases hr0 : r = 0
  · subst r
    simp [boolTrueCount]
  let a := m - r
  let hsum : a + r = m := Nat.sub_add_cancel hr
  let A : Fin a → Bool := fun i => v (Fin.cast hsum (Fin.castAdd r i))
  let B : Fin r → Bool := fun j => v (Fin.cast hsum (Fin.natAdd a j))
  have hsplit : boolTrueCount v = boolTrueCount A + boolTrueCount B := by
    have he : Fin.append A B = fun i => v (Fin.cast hsum i) := by
      funext i
      refine Fin.addCases (fun j => ?_) (fun j => ?_) i
      · simp [A]
      · simp [B]
    have hc := boolTrueCount_append_general A B
    rw [he, boolTrueCount_finCast] at hc
    exact hc
  have hBbound : boolTrueCount B ≤ r := by
    simpa [B, boolTrueCount] using Fintype.card_subtype_le (fun j : Fin r => B j = true)
  by_cases ha0 : a = 0
  · have hAzero : boolTrueCount A = 0 := by
      change Fintype.card {i : Fin a // A i = true} = 0
      apply Fintype.card_eq_zero_iff.mpr
      exact ⟨fun z => Fin.elim0 (Fin.cast ha0 z.val)⟩
    have htotal := hsplit
    rw [hAzero] at htotal
    change boolTrueCount B = min r (boolTrueCount v)
    rw [htotal, Nat.zero_add, Nat.min_eq_right hBbound]
  · have haPos : 0 < a := Nat.pos_of_ne_zero ha0
    let mid : Fin m := ⟨a - 1, by dsimp [a]; omega⟩
    cases hmid : v mid with
    | false =>
        have hAfalse : A = fun _ => false := by
          funext i
          have hvle : Fin.cast hsum (Fin.castAdd r i) ≤ mid := by
            apply Fin.le_iff_val_le_val.mpr
            simp only [mid, Fin.val_mk, Fin.val_cast, Fin.val_castAdd]
            dsimp [a]
            omega
          have hmono := hv hvle
          rw [hmid] at hmono
          exact le_antisymm hmono (Bool.false_le _)
        have hAzero : boolTrueCount A = 0 := by simp [hAfalse, boolTrueCount]
        have htotal := hsplit
        rw [hAzero] at htotal
        change boolTrueCount B = min r (boolTrueCount v)
        rw [htotal, Nat.zero_add, Nat.min_eq_right hBbound]
    | true =>
        have hBtrue : B = fun _ => true := by
          funext j
          have hvmid : mid ≤ Fin.cast hsum (Fin.natAdd a j) := by
            apply Fin.le_iff_val_le_val.mpr
            simp only [mid, Fin.val_mk, Fin.val_cast, Fin.val_natAdd]
            omega
          have hmono := hv hvmid
          rw [hmid] at hmono
          exact le_antisymm (Bool.le_true _) hmono
        have hBfull : boolTrueCount B = r := by simp [hBtrue, boolTrueCount]
        have htotal := hsplit
        rw [hBfull] at htotal
        have hle : r ≤ boolTrueCount v := by omega
        change boolTrueCount B = min r (boolTrueCount v)
        rw [Nat.min_eq_left hle]
        exact hBfull

/-- A sorted Boolean packet has exactly `max(0, X-(m-r))` ones in its first
`r` ranks. -/
theorem sortedBool_prefix_trueCount {m r : Nat} (v : Fin m → Bool)
    (hv : Monotone v) (hr : r ≤ m) :
    boolTrueCount (fun i : Fin r => v
      (Fin.cast (Nat.add_sub_of_le hr) (Fin.castAdd (m - r) i))) =
      boolTrueCount v - (m - r) := by
  let hsum : r + (m - r) = m := Nat.add_sub_of_le hr
  let P : Fin r → Bool := fun i => v (Fin.cast hsum (Fin.castAdd (m - r) i))
  let S : Fin (m - r) → Bool := fun j => v (Fin.cast hsum (Fin.natAdd r j))
  have hsplit : boolTrueCount v = boolTrueCount P + boolTrueCount S := by
    have he : Fin.append P S = fun i => v (Fin.cast hsum i) := by
      funext i
      refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp [P, S]
    have hc := boolTrueCount_append_general P S
    rw [he, boolTrueCount_finCast] at hc
    exact hc
  have hS : boolTrueCount S = min (m - r) (boolTrueCount v) := by
    have hsuf := sortedBool_suffix_trueCount (r := m - r) v hv (Nat.sub_le m r)
    have hlen : m - (m - r) = r := by omega
    have heq : S = fun j : Fin (m - r) => v
        (Fin.cast (Nat.sub_add_cancel (Nat.sub_le m r)) (Fin.natAdd (m - (m - r)) j)) := by
      funext j
      apply congrArg v
      apply Fin.ext
      simp only [S, Fin.val_cast, Fin.val_natAdd]
      omega
    rw [heq]
    exact hsuf
  change boolTrueCount P = boolTrueCount v - (m - r)
  by_cases hX : boolTrueCount v ≤ m - r
  · rw [hS, Nat.min_eq_right hX] at hsplit
    omega
  · have hX' : m - r ≤ boolTrueCount v := by omega
    rw [hS, Nat.min_eq_left hX'] at hsplit
    omega

private theorem profileTail_mono_X (m r X Y : Nat) (h : Y ≤ X) :
    profileTail m Y r ≤ profileTail m X r := by
  simp only [profileTail]
  omega

private theorem profileTail_mono_r (m X a b : Nat) (h : a ≤ b) :
    profileTail m X a ≤ profileTail m X b := by
  simp only [profileTail]
  omega

private theorem profileTail_interval_count (m X a b : Nat) (hab : a ≤ b) (hb : b ≤ m) :
    profileTail m X b - profileTail m X a =
      min (b - a) (X - (m - b)) := by
  by_cases h0 : X ≤ m - b
  · simp [profileTail, h0]
  · by_cases h1 : X ≤ m - a
    · simp only [profileTail, Nat.min_def]
      split_ifs <;> omega
    · simp only [profileTail, Nat.min_def]
      split_ifs <;> omega

private theorem profileCell_mono_X (K X Y i : Nat) (hXY : Y ≤ X)
    (hi : i < K) : profileCell K Y i ≤ profileCell K X i := by
  have hab : 64 * i ≤ 64 * (i + 1) := by omega
  have hb : 64 * (i + 1) ≤ 64 * K := by omega
  rw [show profileCell K Y i = min 64 (Y - (64 * K - 64 * (i + 1))) from ?_]
  rw [show profileCell K X i = min 64 (X - (64 * K - 64 * (i + 1))) from ?_]
  · exact min_le_min le_rfl (Nat.sub_le_sub_right hXY _)
  · unfold profileCell
    rw [profileTail_interval_count (64 * K) X (64 * i) (64 * (i + 1)) hab hb]
    simp [Nat.mul_add]
  · unfold profileCell
    rw [profileTail_interval_count (64 * K) Y (64 * i) (64 * (i + 1)) hab hb]
    simp [Nat.mul_add]

private theorem sum_profileTail_differences (m K X : Nat) (hK : 64 * K ≤ m) :
    (∑ i ∈ range K,
      (profileTail m X (64 * (i + 1)) - profileTail m X (64 * i))) =
      profileTail m X (64 * K) - profileTail m X 0 := by
  induction K with
  | zero => simp
  | succ K ih =>
      rw [sum_range_succ]
      rw [ih (by omega)]
      simp only [profileTail]
      omega

theorem sum_profileCell_eq_total (K X : Nat) (hX : X ≤ 64 * K) :
    (∑ i ∈ range K, profileCell K X i) = X := by
  simp only [profileCell]
  rw [sum_profileTail_differences (64 * K) K X (by omega)]
  simp only [profileTail]
  omega

theorem profileCell_formula (K X i : Nat) (hi : i < K) :
    profileCell K X i = min 64 (X - (64 * K - 64 * (i + 1))) := by
  have hab : 64 * i ≤ 64 * (i + 1) := by omega
  have hb : 64 * (i + 1) ≤ 64 * K := by omega
  unfold profileCell
  rw [profileTail_interval_count (64 * K) X (64 * i) (64 * (i + 1)) hab hb]
  simp [Nat.mul_add]

theorem profileCell_mono (K X Y i : Nat) (hXY : Y ≤ X)
    (hi : i < K) : profileCell K Y i ≤ profileCell K X i := by
  exact profileCell_mono_X K X Y i hXY hi

/-- If one ideal sorted packet has at least as many ones as another, every
fixed rank cell receives at least as many. Across a partition, the absolute
cell-count differences add to exactly the total-count difference. -/
theorem profileCell_L1_exact (K X Y : Nat) (hXY : Y ≤ X) (hX : X ≤ 64 * K) :
    (∑ i ∈ range K,
      ((profileCell K X i - profileCell K Y i) +
        (profileCell K Y i - profileCell K X i))) = X - Y := by
  have hmono : ∀ i ∈ range K, profileCell K Y i ≤ profileCell K X i := by
    intro i hi
    exact profileCell_mono K X Y i hXY (mem_range.mp hi)
  have hzero : ∀ i ∈ range K, profileCell K Y i - profileCell K X i = 0 := by
    intro i hi
    exact Nat.sub_eq_zero_of_le (hmono i hi)
  have hsumX := sum_profileCell_eq_total K X hX
  have hsumY := sum_profileCell_eq_total K Y (by omega)
  have hsumDiff : (∑ i ∈ range K,
      (profileCell K X i - profileCell K Y i)) = X - Y := by
    have hcastSum : ((∑ i ∈ range K,
        (profileCell K X i - profileCell K Y i) : Nat) : Int) =
        ∑ i ∈ range K, ((profileCell K X i : Int) - (profileCell K Y i : Int)) := by
      simp only [Nat.cast_sum]
      apply sum_congr rfl
      intro i hi
      rw [Nat.cast_sub (hmono i hi)]
    have hcast : ((∑ i ∈ range K,
        (profileCell K X i - profileCell K Y i) : Nat) : Int) = ((X - Y : Nat) : Int) := by
      have hxInt : (∑ i ∈ range K, (profileCell K X i : Int)) = (X : Int) := by
        exact_mod_cast hsumX
      have hyInt : (∑ i ∈ range K, (profileCell K Y i : Int)) = (Y : Int) := by
        exact_mod_cast hsumY
      calc
        _ = (∑ i ∈ range K, (profileCell K X i : Int)) -
              (∑ i ∈ range K, (profileCell K Y i : Int)) := by
                rw [hcastSum, Finset.sum_sub_distrib]
        _ = (X : Int) - (Y : Int) := by rw [hxInt, hyInt]
        _ = ((X - Y : Nat) : Int) := by rw [Nat.cast_sub hXY]
    exact_mod_cast hcast
  have hsum : (∑ i ∈ range K,
      ((profileCell K X i - profileCell K Y i) +
        (profileCell K Y i - profileCell K X i))) =
      ∑ i ∈ range K, (profileCell K X i - profileCell K Y i) := by
    apply sum_congr rfl
    intro i hi
    rw [hzero i hi]
    omega
  rw [hsum]
  rw [hsumDiff]

/-- Fractional ideal profile for the common packet count `q + λ`. It is the
convex interpolation of the two neighboring sorted Boolean profiles. -/
def profileCellMean (K q : Nat) (frac : Real) (i : Nat) : Real :=
  (1 - frac) * profileCell K q i + frac * profileCell K (q + 1) i

theorem profileCellMean_sum (K q : Nat) (frac : Real) (hq : q < 64 * K) :
    (∑ i ∈ range K, profileCellMean K q frac i) = q + frac := by
  have hqsum : (∑ i ∈ range K, (profileCell K q i : Real)) = q := by
    exact_mod_cast sum_profileCell_eq_total K q (by omega)
  have hq1sum : (∑ i ∈ range K, (profileCell K (q + 1) i : Real)) = q + 1 := by
    exact_mod_cast sum_profileCell_eq_total K (q + 1) (by omega)
  unfold profileCellMean
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hqsum, hq1sum]
  ring

/-- The aggregate absolute error of a sorted packet's 64-cell counts from
its fractional ideal profile is exactly its whole-packet count error. Thus
the 64-cell baseline variation does not get charged to the mixing error. -/
theorem profileCellMean_L1_exact (K X q : Nat) (frac : Real) (hq : q < 64 * K)
    (hXbound : X ≤ 64 * K) (hfrac0 : 0 ≤ frac) (hfrac1 : frac ≤ 1) :
    (∑ i ∈ range K,
      |(profileCell K X i : Real) - profileCellMean K q frac i|) =
        |(X : Real) - (q + frac)| := by
  have hmean := profileCellMean_sum K q frac hq
  have hxsum : (∑ i ∈ range K, (profileCell K X i : Real)) = X := by
    exact_mod_cast sum_profileCell_eq_total K X hXbound
  by_cases hX : X ≤ q
  · have hpoint : ∀ i ∈ range K,
        (profileCell K X i : Real) ≤ profileCellMean K q frac i := by
      intro i hi
      have hbase := profileCell_mono K q X i (by omega) (mem_range.mp hi)
      have hnext := profileCell_mono K (q + 1) q i (by omega) (mem_range.mp hi)
      unfold profileCellMean
      have hn : (profileCell K q i : Real) ≤ profileCell K (q + 1) i := by exact_mod_cast hnext
      have hb : (profileCell K X i : Real) ≤ profileCell K q i := by exact_mod_cast hbase
      nlinarith [hfrac0, hfrac1]
    calc
      (∑ i ∈ range K,
          |(profileCell K X i : Real) - profileCellMean K q frac i|) =
          ∑ i ∈ range K, (profileCellMean K q frac i - (profileCell K X i : Real)) := by
        apply sum_congr rfl
        intro i hi
        rw [abs_of_nonpos (by linarith [hpoint i hi])]
        ring
      _ = (∑ i ∈ range K, profileCellMean K q frac i) -
          (∑ i ∈ range K, (profileCell K X i : Real)) := by
        rw [Finset.sum_sub_distrib]
      _ = |(X : Real) - (q + frac)| := by
        rw [hmean, hxsum]
        have hXR : (X : Real) ≤ (q : Real) := by exact_mod_cast hX
        rw [abs_of_nonpos (by linarith [hfrac0])]
        ring
  · have hX' : q + 1 ≤ X := by omega
    have hpoint : ∀ i ∈ range K,
        profileCellMean K q frac i ≤ (profileCell K X i : Real) := by
      intro i hi
      have hbase := profileCell_mono K X (q + 1) i (by omega) (mem_range.mp hi)
      have hnext := profileCell_mono K (q + 1) q i (by omega) (mem_range.mp hi)
      unfold profileCellMean
      have hn : (profileCell K q i : Real) ≤ profileCell K (q + 1) i := by exact_mod_cast hnext
      have hb : (profileCell K (q + 1) i : Real) ≤ profileCell K X i := by exact_mod_cast hbase
      nlinarith [hfrac0, hfrac1]
    calc
      (∑ i ∈ range K,
          |(profileCell K X i : Real) - profileCellMean K q frac i|) =
          ∑ i ∈ range K, ((profileCell K X i : Real) - profileCellMean K q frac i) := by
        apply sum_congr rfl
        intro i hi
        rw [abs_of_nonneg (by linarith [hpoint i hi])]
      _ = (∑ i ∈ range K, (profileCell K X i : Real)) -
          (∑ i ∈ range K, profileCellMean K q frac i) := by
        rw [Finset.sum_sub_distrib]
      _ = |(X : Real) - (q + frac)| := by
        rw [hxsum, hmean]
        have hXR : (q : Real) + 1 ≤ (X : Real) := by exact_mod_cast hX'
        rw [abs_of_nonneg (by linarith [hfrac1])]

theorem profileCellMean_cohort_L1_exact {c K : Nat} (X : Fin c → Nat)
    (q : Nat) (frac : Real) (hq : q < 64 * K) (hfrac0 : 0 ≤ frac)
    (hfrac1 : frac ≤ 1) (hX : ∀ i, X i ≤ 64 * K) :
    (∑ i : Fin c, ∑ j ∈ range K,
      |(profileCell K (X i) j : Real) - profileCellMean K q frac j|) =
        ∑ i : Fin c, |(X i : Real) - (q + frac)| := by
  apply Finset.sum_congr rfl
  intro i _
  exact profileCellMean_L1_exact K (X i) q frac hq (hX i) hfrac0 hfrac1

/-- The fine-profile error of a cohort is bounded in square by cohort size
times the coarse packet-count energy. -/
theorem profileCellMean_cohort_L1_sq {c K : Nat} (X : Fin c → Nat)
    (q : Nat) (frac : Real) (hq : q < 64 * K) (hfrac0 : 0 ≤ frac)
    (hfrac1 : frac ≤ 1) (hX : ∀ i, X i ≤ 64 * K) :
    ((∑ i : Fin c, ∑ j ∈ range K,
      |(profileCell K (X i) j : Real) - profileCellMean K q frac j|)^2) ≤
      (c : Real) * ∑ i : Fin c, ((X i : Real) - (q + frac))^2 := by
  rw [profileCellMean_cohort_L1_exact X q frac hq hfrac0 hfrac1 hX]
  simpa [sq_abs, mul_comm] using
    (Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
      (fun i : Fin c => |(X i : Real) - (q + frac)|) (fun _ => (1 : Real)))

/-- Each consecutive 64-wire cell of a sorted 4096-style packet has exactly
the ideal profile count determined by the packet's total count. -/
theorem sortedBool_profileCell_trueCount {K : Nat} (v : Fin (64 * K) → Bool)
    (hv : Monotone v) (X : Nat) (hX : boolTrueCount v = X) (i : Nat) (hi : i < K) :
    boolTrueCount (fun j : Fin 64 => v ⟨64 * i + j,
      by have hj := j.isLt; omega⟩) = profileCell K X i := by
  let m := 64 * K
  let a := 64 * i
  let b := 64 * (i + 1)
  have ha : a ≤ m := by dsimp [a, m]; omega
  have hb : b ≤ m := by dsimp [b, m]; omega
  have hab : a + 64 = b := by dsimp [a, b]; omega
  let Plo : Fin a → Bool := fun j =>
    v (Fin.cast (Nat.add_sub_of_le ha) (Fin.castAdd (m - a) j))
  let Phi : Fin b → Bool := fun j =>
    v (Fin.cast (Nat.add_sub_of_le hb) (Fin.castAdd (m - b) j))
  let C : Fin 64 → Bool := fun j => v ⟨a + j, by dsimp [a, m]; have hj := j.isLt; omega⟩
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
  change boolTrueCount C = profileCell K X i
  have hC : boolTrueCount C = boolTrueCount Phi - boolTrueCount Plo := by omega
  unfold profileCell profileTail
  rw [hC, hhi, hlo]

/-- For any cohort of sorted 4096-style Boolean packets, the aggregate
absolute error of their actual 64-wire cells from a common fractional ideal
profile equals the coarse packet-count error exactly. -/
theorem sortedPackets_cellProfile_L1_exact {c K : Nat}
    (V : Fin c → Fin (64 * K) → Bool) (hV : ∀ i, Monotone (V i))
    (q : Nat) (frac : Real) (hq : q < 64 * K)
    (hfrac0 : 0 ≤ frac) (hfrac1 : frac ≤ 1) :
    (∑ i : Fin c, ∑ j : Fin K,
      |(boolTrueCount (fun k : Fin 64 => V i ⟨64 * j.val + k,
        by have hj := j.isLt; have hk := k.isLt; omega⟩) : Real) -
          profileCellMean K q frac j.val|) =
      ∑ i : Fin c, |(boolTrueCount (V i) : Real) - (q + frac)| := by
  let X : Fin c → Nat := fun i => boolTrueCount (V i)
  have hcell (i : Fin c) (j : Fin K) :
      boolTrueCount (fun k : Fin 64 => V i ⟨64 * j.val + k,
        by have hk := k.isLt; omega⟩) = profileCell K (X i) j := by
    exact sortedBool_profileCell_trueCount (V i) (hV i) (X i) rfl j.val j.isLt
  have hprofiles : (∑ i : Fin c, ∑ j : Fin K,
      |(boolTrueCount (fun k : Fin 64 => V i ⟨64 * j.val + k,
        by have hj := j.isLt; have hk := k.isLt; omega⟩) : Real) -
          profileCellMean K q frac j.val|) =
      ∑ i : Fin c, ∑ j : Fin K,
        |(profileCell K (X i) j.val : Real) - profileCellMean K q frac j.val| := by
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [hcell i j]
  calc
    _ = ∑ i : Fin c, ∑ j : Fin K,
        |(profileCell K (X i) j.val : Real) - profileCellMean K q frac j.val| := hprofiles
    _ = ∑ i : Fin c, |(X i : Real) - (q + frac)| := by
      apply Finset.sum_congr rfl
      intro i _
      calc
        (∑ j : Fin K,
            |(profileCell K (X i) j.val : Real) - profileCellMean K q frac j.val|) =
            ∑ j ∈ range K,
              |(profileCell K (X i) j : Real) - profileCellMean K q frac j| :=
          Fin.sum_univ_eq_sum_range (fun j : Nat =>
            |(profileCell K (X i) j : Real) - profileCellMean K q frac j|) K
        _ = |(X i : Real) - (q + frac)| :=
          profileCellMean_L1_exact K (X i) q frac hq (by
            dsimp [X]
            unfold boolTrueCount
            simpa using Fintype.card_subtype_le (fun k : Fin (64 * K) => V i k = true)) hfrac0 hfrac1

/-- Squared form of the same scale transfer, ready to consume a mixing
energy estimate on the large-packet counts. -/
theorem sortedPackets_cellProfile_L1_sq {c K : Nat}
    (V : Fin c → Fin (64 * K) → Bool) (hV : ∀ i, Monotone (V i))
    (q : Nat) (frac : Real) (hq : q < 64 * K)
    (hfrac0 : 0 ≤ frac) (hfrac1 : frac ≤ 1) :
    ((∑ i : Fin c, ∑ j : Fin K,
      |(boolTrueCount (fun k : Fin 64 => V i ⟨64 * j.val + k,
        by have hj := j.isLt; have hk := k.isLt; omega⟩) : Real) -
          profileCellMean K q frac j.val|)^2) ≤
      (c : Real) * ∑ i : Fin c,
        ((boolTrueCount (V i) : Real) - (q + frac))^2 := by
  rw [sortedPackets_cellProfile_L1_exact V hV q frac hq hfrac0 hfrac1]
  simpa [sq_abs, mul_comm] using
    (Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
      (fun i : Fin c => |(boolTrueCount (V i) : Real) - (q + frac)|)
      (fun _ => (1 : Real)))

