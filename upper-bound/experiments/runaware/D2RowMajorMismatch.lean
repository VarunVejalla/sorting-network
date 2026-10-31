import D2RankAlignment

open Chvatal.D2RankAlignment

set_option maxHeartbeats 1000000
set_option maxRecDepth 4096

namespace Chvatal.D2RowMajorMismatch

lemma ratPrefixMass_fullRows (h k : Rat) (hk0 : 0 <= k) (hk : k <= h) :
    ratPrefixIntervalMass h 0 k = k := by
  have h0 : 0 <= h := le_trans hk0 hk
  rw [ratPrefixIntervalMass_eq_cumulative_diff h 0 k (by linarith)]
  rw [min_eq_right (show k <= h by linarith), min_eq_right (show 0 <= h by linarith)]
  ring

lemma ratPrefixMass_nextFullRow (h k : Rat) (hk0 : 0 <= k) (hk : k + 1 <= h) :
    ratPrefixIntervalMass h k (k + 1) = 1 := by
  have h0 : 0 <= h := by linarith
  rw [ratPrefixIntervalMass_eq_cumulative_diff h k (k + 1) (by linarith)]
  rw [min_eq_right (show k + 1 <= h by linarith),
      min_eq_right (show k <= h by linarith)]
  ring

lemma ratPrefixMass_afterHeight (h k : Rat) (h0 : 0 <= h) (hk : h <= k) :
    ratPrefixIntervalMass h 0 k = h := by
  rw [ratPrefixIntervalMass_eq_cumulative_diff h 0 k (by linarith)]
  rw [min_eq_left hk, min_eq_right (show 0 <= h by linarith)]
  ring

lemma ratPrefixMass_zeroNextRow (h k : Rat) (hk : h <= k) :
    ratPrefixIntervalMass h k (k + 1) = 0 := by
  rw [ratPrefixIntervalMass_eq_cumulative_diff h k (k + 1) (by linarith)]
  rw [min_eq_left (show h <= k + 1 by linarith), min_eq_left hk]
  ring

lemma ratPrefixMass_fractionalNextRow (q r : Rat)
    (hr0 : 0 <= r) (hr1 : r <= 1) :
    ratPrefixIntervalMass (q + r) q (q + 1) = r := by
  rw [ratPrefixIntervalMass_eq_cumulative_diff (q + r) q (q + 1) (by linarith)]
  rw [min_eq_left (show q + r <= q + 1 by linarith),
      min_eq_right (show q <= q + r by linarith)]
  ring

def rowMajorUniformPrefix (H b : Nat) : Rat :=
  (64 : Rat) * ratPrefixIntervalMass ((H : Rat) / 64) 0 (((b / 64 : Nat) : Rat)) +
    ((b % 64 : Nat) : Rat) * ratPrefixIntervalMass ((H : Rat) / 64)
      (((b / 64 : Nat) : Rat)) (((b / 64 : Nat) : Rat) + 1)

def rowMajorBoundaryDiscrepancy (H b : Nat) : Rat :=
  min (H : Rat) (b : Rat) - rowMajorUniformPrefix H b

private theorem flatBoundaryColumnCut_formula
    (rows b c : Nat) (hc : c < 64) (hb : b <= 64 * rows) :
    flatBoundaryColumnCut rows 64 b c =
      min rows (b / 64) + if c < b % 64 then 1 else 0 := by
  let q := b / 64
  let s := b % 64
  have hq : q <= rows := by dsimp [q]; omega
  have hs : s < 64 := by dsimp [s]; exact Nat.mod_lt _ (by decide)
  have hdiv : b = 64 * q + s := by dsimp [q, s]; omega
  have hfilter :
      (Finset.range rows).filter (fun r => r * 64 + c < b) =
        Finset.range (min rows (q + if c < s then 1 else 0)) := by
    ext r
    simp only [Finset.mem_filter, Finset.mem_range]
    rw [hdiv]
    by_cases hcs : c < s <;> simp [hcs] <;> omega
  unfold flatBoundaryColumnCut
  rw [hfilter, Finset.card_range]
  by_cases hcs : c < s
  · have hq' : q + 1 <= rows := by omega
    simp [q, s, hcs, Nat.min_eq_right hq, Nat.min_eq_right hq']
  · simp [q, s, hcs, Nat.min_eq_right hq]

private theorem sum_fin64_if_lt (s : Nat) (hs : s <= 64) (a b : Rat) :
    (Finset.univ.sum fun c : Fin 64 => if c.val < s then b else a) =
      (s : Rat) * b + ((64 - s : Nat) : Rat) * a := by
  rw [Fin.sum_univ_eq_sum_range (fun i : Nat => if i < s then b else a) 64]
  rw [← Finset.sum_range_add_sum_Ico (fun i : Nat => if i < s then b else a) hs]
  have hleft :
      (Finset.range s).sum (fun i => if i < s then b else a) = (s : Rat) * b := by
    calc
      _ = (Finset.range s).sum (fun _ => b) := by
        apply Finset.sum_congr rfl
        intro i hi
        simp [Finset.mem_range.mp hi]
      _ = (s : Rat) * b := by simp
  have hright :
      (Finset.Ico s 64).sum (fun i => if i < s then b else a) =
        ((64 - s : Nat) : Rat) * a := by
    calc
      _ = (Finset.Ico s 64).sum (fun _ => a) := by
        apply Finset.sum_congr rfl
        intro i hi
        simp [Finset.mem_Ico.mp hi]
      _ = ((64 - s : Nat) : Rat) * a := by simp
  rw [hleft, hright]

/-- The cumulative column-uniform reference at a flattened row-major cut is
exactly the piecewise-linear row-major prefix used by the discrepancy bound. -/
theorem rowMajorUniformPrefix_eq_flat_column_sum
    (H rows b : Nat) (hb : b <= 64 * rows) :
    (Finset.univ.sum fun c : Fin 64 =>
      ratPrefixIntervalMass ((H : Rat) / 64) 0
        (flatBoundaryColumnCut rows 64 b c.val : Rat)) =
      rowMajorUniformPrefix H b := by
  let q := b / 64
  let s := b % 64
  let h := (H : Rat) / 64
  have hq : q <= rows := by dsimp [q]; omega
  have hs : s <= 64 := Nat.le_of_lt (Nat.mod_lt _ (by decide))
  have hdiv : b = 64 * q + s := by dsimp [q, s]; omega
  have hheight : 0 <= h := by
    dsimp [h]
    exact div_nonneg (Nat.cast_nonneg H) (by norm_num)
  have hstep : ratPrefixIntervalMass h 0 ((q + 1 : Nat) : Rat) =
      ratPrefixIntervalMass h 0 (q : Rat) +
        ratPrefixIntervalMass h (q : Rat) ((q + 1 : Nat) : Rat) := by
    have hqpos : 0 <= (q : Rat) := Nat.cast_nonneg q
    have hq1pos : 0 <= ((q + 1 : Nat) : Rat) := Nat.cast_nonneg _
    rw [ratPrefixIntervalMass_eq_cumulative_diff h 0 (q : Rat) hqpos,
      ratPrefixIntervalMass_eq_cumulative_diff h (q : Rat)
        ((q + 1 : Nat) : Rat) (by exact_mod_cast Nat.le_succ q),
      ratPrefixIntervalMass_eq_cumulative_diff h 0 ((q + 1 : Nat) : Rat) hq1pos]
    ring
  dsimp [h] at hstep
  have hcut (c : Fin 64) :
      flatBoundaryColumnCut rows 64 b c.val = q + if c.val < s then 1 else 0 := by
    rw [flatBoundaryColumnCut_formula rows b c.val c.isLt hb]
    by_cases hcs : c.val < s
    · have hq' : q + 1 <= rows := by omega
      simp [q, s, hcs, Nat.min_eq_right (Nat.le_trans (Nat.le_of_lt (Nat.lt_succ_self q)) hq')]
    · simp [q, s, hcs, Nat.min_eq_right hq]
  have hterm (c : Fin 64) :
      ratPrefixIntervalMass h 0
          (flatBoundaryColumnCut rows 64 b c.val : Rat) =
        if c.val < s then
          ratPrefixIntervalMass h 0 ((q + 1 : Nat) : Rat)
        else ratPrefixIntervalMass h 0 (q : Rat) := by
    rw [hcut c]
    by_cases hcs : c.val < s <;> simp [hcs, q, s]
  calc
    _ = Finset.univ.sum (fun c : Fin 64 =>
          if c.val < s then ratPrefixIntervalMass h 0 ((q + 1 : Nat) : Rat)
          else ratPrefixIntervalMass h 0 (q : Rat)) := by
        apply Finset.sum_congr rfl
        intro c hc
        exact hterm c
    _ = (s : Rat) * ratPrefixIntervalMass h 0 ((q + 1 : Nat) : Rat) +
          ((64 - s : Nat) : Rat) * ratPrefixIntervalMass h 0 (q : Rat) :=
        sum_fin64_if_lt s hs _ _
    _ = rowMajorUniformPrefix H b := by
      dsimp [rowMajorUniformPrefix, h]
      rw [hstep]
      rw [hdiv]
      have hqdiv : (64 * q + s) / 64 = q := by omega
      have hsmod : (64 * q + s) % 64 = s := by omega
      rw [hqdiv, hsmod]
      simp only [Nat.cast_add, Nat.cast_one]
      change (s : Rat) * (ratPrefixIntervalMass ((H : Rat) / 64) 0 (q : Rat) +
          ratPrefixIntervalMass ((H : Rat) / 64) (q : Rat) ((q : Rat) + 1)) +
          ((64 - s : Nat) : Rat) * ratPrefixIntervalMass ((H : Rat) / 64) 0 (q : Rat) =
        64 * ratPrefixIntervalMass ((H : Rat) / 64) 0 (q : Rat) +
          (s : Rat) * ratPrefixIntervalMass ((H : Rat) / 64) (q : Rat) ((q : Rat) + 1)
      rw [Nat.cast_sub hs]
      ring

theorem rowMajorBoundaryDiscrepancy_formula (H b : Nat) :
    rowMajorBoundaryDiscrepancy H b =
      if b / 64 = H / 64 then
        min ((H % 64 : Nat) : Rat) ((b % 64 : Nat) : Rat) -
          ((b % 64 : Nat) : Rat) * ((H % 64 : Nat) : Rat) / 64
      else 0 := by
  let q := H / 64
  let r := H % 64
  let k := b / 64
  let s := b % 64
  have hHdiv : H = 64 * q + r := by dsimp [q, r]; omega
  have hbdiv : b = 64 * k + s := by dsimp [k, s]; omega
  have hHdivR : (H : Rat) = 64 * (q : Rat) + (r : Rat) := by exact_mod_cast hHdiv
  have hbdivR : (b : Rat) = 64 * (k : Rat) + (s : Rat) := by exact_mod_cast hbdiv
  have hr : r < 64 := by dsimp [r]; exact Nat.mod_lt H (by decide)
  have hs : s < 64 := by dsimp [s]; exact Nat.mod_lt b (by decide)
  have havg : (H : Rat) / 64 = (q : Rat) + (r : Rat) / 64 := by
    rw [hHdiv]
    push_cast
    field_simp
  by_cases hkq : k < q
  · have hkle : (k : Rat) + 1 <= (H : Rat) / 64 := by
      rw [havg]
      have hkqNat : k + 1 <= q := Nat.succ_le_of_lt hkq
      have hkqRat : (k : Rat) + 1 <= (q : Rat) := by exact_mod_cast hkqNat
      have hr0 : 0 <= (r : Rat) / 64 := by
        apply div_nonneg
        · exact_mod_cast Nat.zero_le r
        · norm_num
      linarith
    have hk0 : (0 : Rat) <= (k : Rat) := by positivity
    have hfull := ratPrefixMass_fullRows ((H : Rat) / 64) k hk0 (by linarith)
    have hpart := ratPrefixMass_nextFullRow ((H : Rat) / 64) k hk0 hkle
    have hbH : b <= H := by omega
    have hbHR : (b : Rat) <= (H : Rat) := by exact_mod_cast hbH
    change min (H : Rat) (b : Rat) - rowMajorUniformPrefix H b = _
    rw [rowMajorUniformPrefix]
    rw [min_eq_right hbHR, hfull, hpart]
    have hne : b / 64 ≠ H / 64 := by dsimp [k, q] at hkq ⊢; omega
    rw [if_neg hne]
    dsimp [k, s] at hbdivR
    nlinarith [hbdivR]
  · by_cases hqk : q < k
    · have havgle : (H : Rat) / 64 <= (k : Rat) := by
        rw [havg]
        have hqkNat : q + 1 <= k := Nat.succ_le_of_lt hqk
        have hqkRat : (q : Rat) + 1 <= (k : Rat) := by exact_mod_cast hqkNat
        have hrle : (r : Rat) / 64 <= 1 := by
          have hr' : (r : Rat) < 64 := by exact_mod_cast hr
          linarith
        linarith
      have h0 : (0 : Rat) <= (H : Rat) / 64 := by
        apply div_nonneg
        · exact_mod_cast Nat.zero_le H
        · norm_num
      have hfull := ratPrefixMass_afterHeight ((H : Rat) / 64) k h0 havgle
      have hpart := ratPrefixMass_zeroNextRow ((H : Rat) / 64) k havgle
      have hHb : H <= b := by omega
      have hHbR : (H : Rat) <= (b : Rat) := by exact_mod_cast hHb
      change min (H : Rat) (b : Rat) - rowMajorUniformPrefix H b = _
      rw [rowMajorUniformPrefix]
      rw [min_eq_left hHbR, hfull, hpart, havg]
      have hne : b / 64 ≠ H / 64 := by dsimp [k, q] at hqk ⊢; omega
      rw [if_neg hne]
      dsimp [q, r] at hHdivR
      nlinarith [hHdivR]
    · have hkqeq : k = q := by omega
      subst k
      have hminNat : min H b = 64 * q + min r s := by
        rw [hHdiv, hbdiv]
        omega
      have hmin : min (H : Rat) (b : Rat) =
          64 * (q : Rat) + min (r : Rat) (s : Rat) := by
        exact_mod_cast hminNat
      have hq0 : (0 : Rat) <= (q : Rat) := by positivity
      have hqle : (q : Rat) <= (H : Rat) / 64 := by
        rw [havg]
        have hr0 : (0 : Rat) <= (r : Rat) := by exact_mod_cast Nat.zero_le r
        linarith
      have hfull := ratPrefixMass_fullRows ((H : Rat) / 64) q hq0 hqle
      have hfrac : (r : Rat) / 64 <= 1 := by
        have hr' : (r : Rat) < 64 := by exact_mod_cast hr
        linarith
      have hr0 : (0 : Rat) <= (r : Rat) / 64 := by
        apply div_nonneg
        · exact_mod_cast Nat.zero_le r
        · norm_num
      have hpart := ratPrefixMass_fractionalNextRow
        (q : Rat) ((r : Rat) / 64) hr0 hfrac
      have hpart' : ratPrefixIntervalMass ((H : Rat) / 64) (q : Rat) ((q : Rat) + 1) =
          (r : Rat) / 64 := by rw [havg]; exact hpart
      have hEqQ : b / 64 = q := hkqeq
      change min (H : Rat) (b : Rat) - rowMajorUniformPrefix H b = _
      rw [rowMajorUniformPrefix]
      rw [hmin, hEqQ, hfull, hpart']
      simp [q]
      ring

theorem rowMajorBoundaryDiscrepancy_nonneg_le_16 (H b : Nat) :
    0 <= rowMajorBoundaryDiscrepancy H b ∧
      rowMajorBoundaryDiscrepancy H b <= 16 := by
  rw [rowMajorBoundaryDiscrepancy_formula]
  by_cases hsame : b / 64 = H / 64
  · simp only [if_pos hsame]
    let r : Rat := (H % 64 : Nat)
    let s : Rat := (b % 64 : Nat)
    have hr0 : 0 <= r := by dsimp [r]; positivity
    have hs0 : 0 <= s := by dsimp [s]; positivity
    have hr64 : r <= 64 := by
      dsimp [r]
      exact_mod_cast Nat.le_of_lt (Nat.mod_lt H (by decide))
    have hs64 : s <= 64 := by
      dsimp [s]
      exact_mod_cast Nat.le_of_lt (Nat.mod_lt b (by decide))
    by_cases hrsNat : H % 64 <= b % 64
    · have hrs : r <= s := by dsimp [r, s]; exact_mod_cast hrsNat
      rw [min_eq_left hrs]
      have hlow : 0 <= r * (64 - s) :=
        mul_nonneg hr0 (by linarith)
      have hquad : r * (64 - s) / 64 = r - s * r / 64 := by ring
      rw [← hquad]
      constructor
      · exact div_nonneg hlow (by norm_num)
      · have hcross : 0 <= (s - r) * r := mul_nonneg (by linarith) hr0
        have hsquare : 0 <= (r - 32) ^ 2 := sq_nonneg (r - 32)
        nlinarith [hlow, hcross, hsquare]
    · have hsrNat : b % 64 <= H % 64 := by omega
      have hsr : s <= r := by dsimp [r, s]; exact_mod_cast hsrNat
      rw [min_eq_right hsr]
      have hlow : 0 <= s * (64 - r) :=
        mul_nonneg hs0 (by linarith)
      have hquad : s * (64 - r) / 64 = s - s * r / 64 := by ring
      rw [← hquad]
      constructor
      · exact div_nonneg hlow (by norm_num)
      · have hcross : 0 <= (r - s) * s := mul_nonneg (by linarith) hs0
        have hsquare : 0 <= (s - 32) ^ 2 := sq_nonneg (s - 32)
        nlinarith [hlow, hcross, hsquare]
  · simp [hsame]

def rowMajorBump (r s : Nat) : Rat :=
  min (r : Rat) (s : Rat) - (s : Rat) * (r : Rat) / 64

theorem rowMajorBoundaryDiscrepancy_on_bump (H s : Nat) (hs : s <= 64) :
    rowMajorBoundaryDiscrepancy H (64 * (H / 64) + s) =
      rowMajorBump (H % 64) s := by
  have hr : H % 64 < 64 := Nat.mod_lt H (by decide)
  by_cases hs64 : s < 64
  · have hq : (64 * (H / 64) + s) / 64 = H / 64 := by omega
    have hsmod : (64 * (H / 64) + s) % 64 = s := by omega
    rw [rowMajorBoundaryDiscrepancy_formula]
    simp [hq, hsmod, rowMajorBump]
  · have hsEq : s = 64 := by omega
    subst s
    have hqnext : (64 * (H / 64) + 64) / 64 ≠ H / 64 := by omega
    rw [rowMajorBoundaryDiscrepancy_formula]
    rw [if_neg hqnext]
    change 0 = rowMajorBump (H % 64) 64
    have hrRat : ((H % 64 : Nat) : Rat) <= 64 := by exact_mod_cast Nat.le_of_lt hr
    change 0 = min ((H % 64 : Nat) : Rat) (64 : Rat) -
      (64 : Rat) * ((H % 64 : Nat) : Rat) / 64
    rw [min_eq_left hrRat]
    field_simp
    ring

lemma rowMajorBump_abs_step (r s : Nat) (hr : r <= 64) :
    |rowMajorBump r (s + 1) - rowMajorBump r s| =
      if s < r then 1 - (r : Rat) / 64 else (r : Rat) / 64 := by
  by_cases hsr : s < r
  · have hsr1 : s + 1 <= r := Nat.succ_le_of_lt hsr
    have hsrR : (s : Rat) < (r : Rat) := by exact_mod_cast hsr
    have hsr1R : (s : Rat) + 1 <= (r : Rat) := by exact_mod_cast hsr1
    have hrR : (r : Rat) <= 64 := by exact_mod_cast hr
    have hnonneg : 0 <= 1 - (r : Rat) / 64 := by linarith
    simp only [if_pos hsr]
    unfold rowMajorBump
    push_cast
    rw [min_eq_right hsr1R, min_eq_right (le_of_lt hsrR)]
    calc
      _ = |1 - (r : Rat) / 64| := by congr 1; ring
      _ = 1 - (r : Rat) / 64 := abs_of_nonneg hnonneg
  · have hrs : r <= s := Nat.le_of_not_lt hsr
    have hrsR : (r : Rat) <= (s : Rat) := by exact_mod_cast hrs
    have hrs1R : (r : Rat) <= (s : Rat) + 1 := by linarith
    have hr0 : 0 <= (r : Rat) / 64 := by
      apply div_nonneg
      · positivity
      · norm_num
    simp only [if_neg hsr]
    unfold rowMajorBump
    push_cast
    rw [min_eq_left hrs1R, min_eq_left hrsR]
    calc
      _ = |-(r : Rat) / 64| := by congr 1; ring
      _ = (r : Rat) / 64 := by
        rw [abs_of_nonpos (show -(r : Rat) / 64 <= 0 by nlinarith [hr0])]
        ring

/-- The triangular discrepancy has exact variation `2r(1-r/64)` within
its single nonzero 64-boundary row. -/
theorem rowMajorBump_total_variation (r : Nat) (hr : r < 64) :
    (∑ s ∈ Finset.range 64,
      |rowMajorBump r (s + 1) - rowMajorBump r s|) =
      2 * (r : Rat) * (64 - (r : Rat)) / 64 := by
  have hrle : r <= 64 := Nat.le_of_lt hr
  rw [← Finset.sum_range_add_sum_Ico _ hrle]
  have hfirst :
      (∑ s ∈ Finset.range r,
        |rowMajorBump r (s + 1) - rowMajorBump r s|) =
        (r : Rat) * (1 - (r : Rat) / 64) := by
    calc
      _ = ∑ s ∈ Finset.range r, (1 - (r : Rat) / 64) := by
        apply Finset.sum_congr rfl
        intro s hs
        have hstep := rowMajorBump_abs_step r s hrle
        rw [hstep, if_pos (Finset.mem_range.mp hs)]
      _ = (r : Rat) * (1 - (r : Rat) / 64) := by
        simp
        field_simp
  have hsecond :
      (∑ s ∈ Finset.Ico r 64,
        |rowMajorBump r (s + 1) - rowMajorBump r s|) =
        (64 - r : Nat) * ((r : Rat) / 64) := by
    calc
      _ = ∑ s ∈ Finset.Ico r 64, ((r : Rat) / 64) := by
        apply Finset.sum_congr rfl
        intro s hs
        have hsge : r <= s := (Finset.mem_Ico.mp hs).1
        have hstep := rowMajorBump_abs_step r s hrle
        rw [hstep, if_neg (Nat.not_lt.mpr hsge)]
      _ = (64 - r : Nat) * ((r : Rat) / 64) := by simp
  rw [hfirst, hsecond]
  rw [Nat.cast_sub hrle]
  push_cast
  field_simp
  ring

theorem rowMajorBump_total_variation_le_32 (r : Nat) (hr : r < 64) :
    (∑ s ∈ Finset.range 64,
      |rowMajorBump r (s + 1) - rowMajorBump r s|) <= 32 := by
  rw [rowMajorBump_total_variation r hr]
  have hr64 : (r : Rat) <= 64 := by exact_mod_cast Nat.le_of_lt hr
  have hsquare : 0 <= ((r : Rat) - 32) ^ 2 := sq_nonneg ((r : Rat) - 32)
  have hprod : (r : Rat) * (64 - (r : Rat)) <= 1024 := by nlinarith [hsquare]
  have hden : (0 : Rat) < 64 := by norm_num
  rw [div_le_iff₀ hden]
  nlinarith [hprod]

lemma rowMajorBoundaryDiscrepancy_zero_pair_before_bump (H b : Nat)
    (hb : b < 64 * (H / 64)) :
    rowMajorBoundaryDiscrepancy H b = 0 ∧
      rowMajorBoundaryDiscrepancy H (b + 1) = 0 := by
  have hbq : b / 64 < H / 64 := by omega
  have hzero : rowMajorBoundaryDiscrepancy H b = 0 := by
    rw [rowMajorBoundaryDiscrepancy_formula]
    simp [Nat.ne_of_lt hbq]
  have hnext : rowMajorBoundaryDiscrepancy H (b + 1) = 0 := by
    by_cases hsame : (b + 1) / 64 = H / 64
    · have hrem : (b + 1) % 64 = 0 := by omega
      rw [rowMajorBoundaryDiscrepancy_formula]
      simp [hsame, hrem]
    · have hlt : (b + 1) / 64 < H / 64 := by omega
      rw [rowMajorBoundaryDiscrepancy_formula]
      simp [Nat.ne_of_lt hlt]
  exact ⟨hzero, hnext⟩

/-- All nonzero boundary variation lies in the one 64-boundary row that
contains `H`; its total variation is the triangular-profile value. -/
theorem rowMajorBoundaryDiscrepancy_total_variation (H : Nat) :
    (∑ b ∈ Finset.range (64 * (H / 64 + 1)),
      |rowMajorBoundaryDiscrepancy H (b + 1) -
        rowMajorBoundaryDiscrepancy H b|) =
      2 * ((H % 64 : Nat) : Rat) *
        (64 - ((H % 64 : Nat) : Rat)) / 64 := by
  let start := 64 * (H / 64)
  let finish := 64 * (H / 64 + 1)
  have hfinish : finish = start + 64 := by dsimp [finish, start]; omega
  have hstart_le : start <= finish := by dsimp [finish, start]; omega
  rw [show 64 * (H / 64 + 1) = finish by rfl]
  rw [← Finset.sum_range_add_sum_Ico
    (fun b => |rowMajorBoundaryDiscrepancy H (b + 1) -
      rowMajorBoundaryDiscrepancy H b|) hstart_le]
  have hbefore :
      (∑ b ∈ Finset.range start,
        |rowMajorBoundaryDiscrepancy H (b + 1) -
          rowMajorBoundaryDiscrepancy H b|) = 0 := by
    apply Finset.sum_eq_zero
    intro b hb
    have hb_lt : b < start := Finset.mem_range.mp hb
    have hpair := rowMajorBoundaryDiscrepancy_zero_pair_before_bump H b (by
      dsimp [start] at hb_lt ⊢
      exact hb_lt)
    rw [hpair.1, hpair.2]
    simp
  have hactive :
      (∑ b ∈ Finset.Ico start finish,
        |rowMajorBoundaryDiscrepancy H (b + 1) -
          rowMajorBoundaryDiscrepancy H b|) =
      (∑ s ∈ Finset.range 64,
        |rowMajorBump (H % 64) (s + 1) - rowMajorBump (H % 64) s|) := by
    have hshift := Finset.sum_Ico_add
      (fun b => |rowMajorBoundaryDiscrepancy H (b + 1) -
        rowMajorBoundaryDiscrepancy H b|) 0 64 start
    rw [hfinish]
    have hshift' :
        (∑ b ∈ Finset.Ico start (start + 64),
          |rowMajorBoundaryDiscrepancy H (b + 1) -
            rowMajorBoundaryDiscrepancy H b|) =
        (∑ s ∈ Finset.Ico 0 64,
          |rowMajorBoundaryDiscrepancy H (start + s + 1) -
            rowMajorBoundaryDiscrepancy H (start + s)|) := by
      simpa [Nat.add_comm] using hshift.symm
    rw [hshift']
    simp only [Nat.Ico_zero_eq_range]
    apply Finset.sum_congr rfl
    intro s hs
    have hslt : s < 64 := Finset.mem_range.mp hs
    have hsle : s <= 64 := hslt.le
    have hs1le : s + 1 <= 64 := by omega
    have hleft := rowMajorBoundaryDiscrepancy_on_bump H s hsle
    have hright := rowMajorBoundaryDiscrepancy_on_bump H (s + 1) hs1le
    have hleft' : rowMajorBoundaryDiscrepancy H (start + s) =
        rowMajorBump (H % 64) s := by simpa [start] using hleft
    have hright' : rowMajorBoundaryDiscrepancy H (start + s + 1) =
        rowMajorBump (H % 64) (s + 1) := by
      simpa [start, Nat.add_assoc] using hright
    rw [hleft', hright']
  rw [hbefore, hactive, zero_add]
  exact rowMajorBump_total_variation (H % 64)
    (Nat.mod_lt H (by decide))

theorem rowMajorBoundaryDiscrepancy_total_variation_le_32 (H : Nat) :
    (∑ b ∈ Finset.range (64 * (H / 64 + 1)),
      |rowMajorBoundaryDiscrepancy H (b + 1) -
        rowMajorBoundaryDiscrepancy H b|) <= 32 := by
  rw [rowMajorBoundaryDiscrepancy_total_variation]
  rw [← rowMajorBump_total_variation (H % 64)
    (Nat.mod_lt H (by decide))]
  exact rowMajorBump_total_variation_le_32 (H % 64)
    (Nat.mod_lt H (by decide))

lemma rowMajorBoundaryDiscrepancy_zero_pair_after_bump (H b : Nat)
    (hb : 64 * (H / 64 + 1) <= b) :
    rowMajorBoundaryDiscrepancy H b = 0 ∧
      rowMajorBoundaryDiscrepancy H (b + 1) = 0 := by
  have hbq : H / 64 < b / 64 := by omega
  have hnextq : H / 64 < (b + 1) / 64 := by omega
  constructor
  · rw [rowMajorBoundaryDiscrepancy_formula]
    rw [if_neg (by omega : b / 64 ≠ H / 64)]
  · rw [rowMajorBoundaryDiscrepancy_formula]
    rw [if_neg (by omega : (b + 1) / 64 ≠ H / 64)]

/-- A full row-major sender with 64 columns has total exact-rank correction
variation at most32, whenever the marked mass fits in its capacity. -/
theorem rowMajorBoundaryDiscrepancy_sender_variation_le_32
    (H rows : Nat) (hH : H <= 64 * rows) :
    (∑ b ∈ Finset.range (64 * rows),
      |rowMajorBoundaryDiscrepancy H (b + 1) -
        rowMajorBoundaryDiscrepancy H b|) <= 32 := by
  by_cases hfull : H = 64 * rows
  · subst H
    apply le_trans ?_ (by norm_num : (0 : Rat) <= 32)
    apply le_of_eq
    apply Finset.sum_eq_zero
    intro b hb
    have hb_lt : b < 64 * rows := Finset.mem_range.mp hb
    have hpair := rowMajorBoundaryDiscrepancy_zero_pair_before_bump
      (64 * rows) b (by simpa using hb_lt)
    rw [hpair.1, hpair.2]
    simp
  · have hHlt : H < 64 * rows := Nat.lt_of_le_of_ne hH hfull
    have hqrows : H / 64 + 1 <= rows := by omega
    let finish := 64 * (H / 64 + 1)
    have hfinish : finish <= 64 * rows := by dsimp [finish]; omega
    rw [← Finset.sum_range_add_sum_Ico
      (fun b => |rowMajorBoundaryDiscrepancy H (b + 1) -
        rowMajorBoundaryDiscrepancy H b|) hfinish]
    have htail :
        (∑ b ∈ Finset.Ico finish (64 * rows),
          |rowMajorBoundaryDiscrepancy H (b + 1) -
            rowMajorBoundaryDiscrepancy H b|) = 0 := by
      apply Finset.sum_eq_zero
      intro b hb
      have hbge : finish <= b := (Finset.mem_Ico.mp hb).1
      have hpair := rowMajorBoundaryDiscrepancy_zero_pair_after_bump H b (by
        dsimp [finish] at hbge ⊢
        exact hbge)
      rw [hpair.1, hpair.2]
      simp
    rw [htail, add_zero]
    have hprefix :
        (∑ b ∈ Finset.range finish,
          |rowMajorBoundaryDiscrepancy H (b + 1) -
            rowMajorBoundaryDiscrepancy H b|) <= 32 := by
      simpa [finish] using rowMajorBoundaryDiscrepancy_total_variation_le_32 H
    exact hprefix

lemma rat_abs_endpoint_diff_le_interval_variation (f : Nat → Rat)
    (a b : Nat) (hab : a <= b) :
    |f b - f a| <=
      (∑ i ∈ Finset.Ico a b, |f (i + 1) - f i|) := by
  have htel :
      (∑ i ∈ Finset.Ico a b, (f (i + 1) - f i)) = f b - f a := by
    by_cases habEq : a = b
    · subst b
      simp
    · have habLt : a < b := lt_of_le_of_ne hab habEq
      have hshift :
          (∑ i ∈ Finset.Ico a b, f (i + 1)) =
            ∑ i ∈ Finset.Ico (a + 1) (b + 1), f i := by
        simpa [Nat.add_comm] using Finset.sum_Ico_add f a b 1
      have htop :
          (∑ i ∈ Finset.Ico (a + 1) (b + 1), f i) =
            (∑ i ∈ Finset.Ico (a + 1) b, f i) + f b := by
        have h := Finset.sum_Ico_succ_sub_top f (by omega : a + 1 <= b)
        linarith
      have hbot :
          (∑ i ∈ Finset.Ico a b, f i) =
            f a + (∑ i ∈ Finset.Ico (a + 1) b, f i) := by
        have h := Finset.sum_Ico_sub_bot f habLt
        linarith
      rw [Finset.sum_sub_distrib, hshift, htop, hbot]
      ring
  rw [← htel]
  exact Finset.abs_sum_le_sum_abs _ _

lemma sum_cut_intervals_eq_range (f : Nat → Rat) (cuts : Nat → Nat)
    (n : Nat) (hzero : cuts 0 = 0)
    (hmono : ∀ i, cuts i <= cuts (i + 1)) :
    (∑ i ∈ Finset.range n,
      ∑ b ∈ Finset.Ico (cuts i) (cuts (i + 1)), f b) =
      (∑ b ∈ Finset.range (cuts n), f b) := by
  induction n with
  | zero => simp [hzero]
  | succ n ih =>
      rw [Finset.sum_range_succ, ih, ← Finset.sum_range_add_sum_Ico _ (hmono n)]

/-- For any complete partition of a 64-column row-major sender, the sum of
the exact-rank versus uniform-reference port errors is at most32. -/
theorem rowMajor_complete_port_rank_correction_le_32
    (H rows ports : Nat) (cuts : Nat → Nat)
    (hH : H <= 64 * rows)
    (hzero : cuts 0 = 0)
    (hend : cuts ports = 64 * rows)
    (hmono : ∀ i, cuts i <= cuts (i + 1)) :
    (∑ i ∈ Finset.range ports,
      |rowMajorBoundaryDiscrepancy H (cuts (i + 1)) -
        rowMajorBoundaryDiscrepancy H (cuts i)|) <= 32 := by
  calc
    _ <= ∑ i ∈ Finset.range ports,
        (∑ b ∈ Finset.Ico (cuts i) (cuts (i + 1)),
          |rowMajorBoundaryDiscrepancy H (b + 1) -
            rowMajorBoundaryDiscrepancy H b|) := by
      apply Finset.sum_le_sum
      intro i hi
      exact rat_abs_endpoint_diff_le_interval_variation
        (rowMajorBoundaryDiscrepancy H) (cuts i) (cuts (i + 1)) (hmono i)
    _ = ∑ b ∈ Finset.range (64 * rows),
        |rowMajorBoundaryDiscrepancy H (b + 1) -
          rowMajorBoundaryDiscrepancy H b| := by
      rw [sum_cut_intervals_eq_range _ cuts ports hzero hmono, hend]
    _ <= 32 := rowMajorBoundaryDiscrepancy_sender_variation_le_32 H rows hH

end Chvatal.D2RowMajorMismatch
