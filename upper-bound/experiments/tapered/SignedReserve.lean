import Mathlib.Tactic

namespace Tapered945

/-! Exact rational bounds for the signed two-tail reserve in the 945.006
candidate. This file isolates the local arithmetic used after the variable
window theorem; it does not assert the schedule-specific outsider invariant. -/

def cap : Rat := 64 ^ 2 * 64 ^ 2
def eAbs : Rat := 31 / 268369920
def ePos : Rat := 1 / 268369920
def reserveInterior : Rat := 1 / cap + ePos / 64
def reserveEndpoint : Rat := 1 / (2 * cap) + 31 * eAbs / 64
def reserve : Rat := reserveEndpoint

def qEnd : Rat := -31 / 2 ^ 22
def qMid : Rat := 1 / 2 ^ 22
def rBar : Rat := 65535 / 2 ^ 22
def rEnd : Rat := 2047 / 131072
def rMid : Rat := 1 / 64
def upFlow : Rat := 255 / 2 ^ 24
def epsB : Rat := 1 / 2 ^ 21
def delta : Rat := 1 / 2 ^ 25
def epsFTail : Rat := 128 / 4095
def mu : Rat := 17 / 71565312
def siblingFactor : Rat := delta * 64 * 64 ^ 2 / (1 - (delta * 64 * 64) ^ 2)
def activeRounding : Rat := 69 / 2 ^ 34
def screenedMargin : Rat :=
  mu * (64 * (1 / 16 : Rat) - 1) - epsB -
    mu * (64 * siblingFactor + delta * 64 ^ 2 * 64) - reserve - activeRounding

/-- One normalized signed-debt update along an address edge. -/
def debtStep (q e : Rat) : Rat := q / 64 + e / 4096

/-- Debt produced by a finite address path; order is immaterial to the bound. -/
def debtPath : List Rat → Rat
  | [] => 0
  | q :: qs => debtStep q (debtPath qs)

theorem debtStep_preserves_bounds (q e : Rat)
    (hqLo : qEnd ≤ q) (hqHi : q ≤ qMid)
    (heLo : -eAbs ≤ e) (heHi : e ≤ ePos) :
    -eAbs ≤ debtStep q e ∧ debtStep q e ≤ ePos := by
  constructor
  · unfold debtStep qEnd eAbs at *
    nlinarith
  · unfold debtStep qMid ePos at *
    nlinarith

theorem debtPath_bounds (qs : List Rat)
    (hq : ∀ q ∈ qs, qEnd ≤ q ∧ q ≤ qMid) :
    -eAbs ≤ debtPath qs ∧ debtPath qs ≤ ePos := by
  induction qs with
  | nil => norm_num [debtPath, eAbs, ePos]
  | cons q qs ih =>
    have hqhead := hq q (by simp)
    have hqtail : ∀ x ∈ qs, qEnd ≤ x ∧ x ≤ qMid := by
      intro x hx
      exact hq x (by simp [hx])
    have he := ih hqtail
    simpa [debtPath] using debtStep_preserves_bounds q (debtPath qs)
      hqhead.1 hqhead.2 he.1 he.2

theorem debt_bounds_mul_capacity (C : Rat) (hC : 0 ≤ C) (qs : List Rat)
    (hq : ∀ q ∈ qs, qEnd ≤ q ∧ q ≤ qMid) :
    -eAbs * C ≤ debtPath qs * C ∧ debtPath qs * C ≤ ePos * C := by
  have h := debtPath_bounds qs hq
  constructor <;> nlinarith [mul_le_mul_of_nonneg_right h.1 hC,
    mul_le_mul_of_nonneg_right h.2 hC]

theorem candidate_centered_flows :
    rEnd - rBar = qEnd ∧ rMid - rBar = qMid ∧
      2 * rEnd + 62 * rMid = 64 * rBar := by
  unfold rEnd rMid rBar qEnd qMid
  norm_num

theorem candidate_flow_mass_identity :
    rBar + 64 * upFlow * 64 ^ 2 = 64 * (1 - 1 / cap) * (1 / 16 : Rat) := by
  unfold rBar upFlow cap
  norm_num

theorem candidate_signed_flow_nonnegative (qs : List Rat)
    (hq : ∀ q ∈ qs, qEnd ≤ q ∧ q ≤ qMid) :
    0 < upFlow - debtPath qs ∧ 0 < rEnd + debtPath qs / 64 ∧
      0 < rMid + debtPath qs / 64 := by
  have hd := debtPath_bounds qs hq
  unfold upFlow rEnd rMid eAbs ePos at *
  constructor
  · nlinarith
  constructor <;> nlinarith

/-- The signed correction restores uniform occupancy over all 64 addresses.
The two occurrences of the current debt cancel against the sum of child debts;
the centered address terms vanish because they sum to zero. -/
theorem signed_child_debt_sum (q : Fin 64 → Rat) (C e : Rat)
    (hq : ∑ j : Fin 64, q j = 0) :
    (∑ j : Fin 64, (q j * C + e / 64)) = e := by
  rw [Finset.sum_add_distrib, ← Finset.sum_mul, hq]
  simp
  field_simp

theorem signed_occupancy_identity
    (q : Fin 64 → Rat) (parentCap A rbar s rj qj e : Rat)
    (hq : ∑ l : Fin 64, q l = 0)
    (hr : rj - qj = rbar) :
    (rj * parentCap + e / 64) +
      (∑ l : Fin 64,
        (s * A ^ 2 * parentCap -
          (q l * (A * parentCap) + (qj * parentCap + e / 64) / 64))) =
      (rbar + 64 * s * A ^ 2) * parentCap := by
  have hdebt := signed_child_debt_sum q (A * parentCap) (qj * parentCap + e / 64) hq
  have hconst : (∑ _l : Fin 64, (s * A ^ 2 * parentCap : Rat)) =
      64 * (s * A ^ 2 * parentCap) := by simp
  rw [Finset.sum_sub_distrib, hconst, hdebt]
  calc
    (rj * parentCap + e / 64) +
        (64 * (s * A ^ 2 * parentCap) - (qj * parentCap + e / 64)) =
        (rj - qj + 64 * s * A ^ 2) * parentCap := by ring
    _ = (rbar + 64 * s * A ^ 2) * parentCap := by rw [hr]

theorem endpoint_dominates_interior : reserveInterior ≤ reserve := by
  unfold reserve reserveEndpoint reserveInterior cap eAbs ePos
  norm_num

theorem candidate_mu_formula :
    mu = (1 / 2 : Rat) * epsFTail * (64 * (1 / 16 : Rat) * 64 - 1) /
      (64 ^ 2 * 64 ^ 2) := by
  unfold mu epsFTail
  norm_num

theorem candidate_screened_margin_positive : 0 < screenedMargin := by
  unfold screenedMargin siblingFactor delta mu epsB activeRounding reserve
    reserveEndpoint cap eAbs
  norm_num

theorem candidate_screened_margin_value :
    screenedMargin = 4441485454561 / 174859758926424965120 := by
  unfold screenedMargin siblingFactor delta mu epsB activeRounding reserve
    reserveEndpoint cap eAbs
  norm_num

/-- If the current integer occupancy discrepancy is at most 69 wires, then
one parent block error of `1 + (|eta|+1)/64`, together with at most one wire
of rounding error from each of the 64 child up-flows, stays within the same
69-wire budget. This is the scalar inequality needed by the local balanced
rounding construction; it does not assert that the integer allocation exists. -/
theorem integer_discrepancy_step_budget (eta : Rat) (hη : |eta| ≤ 69) :
    64 + 1 + (|eta| + 1) / 64 ≤ 69 := by
  rw [abs_le] at hη
  have hηabs : |eta| ≤ 69 := abs_le.mpr hη
  nlinarith

/-- At the proposed `2^34` active cutoff, every adjusted ideal child block
remains positive even after the largest total rounding correction permitted
by a 69-wire occupancy discrepancy and one wire of up-flow rounding. -/
theorem candidate_adjusted_child_targets_positive (C debt correction : Rat)
    (hC : 2 ^ 34 ≤ C)
    (hdebtLo : -eAbs * C ≤ debt) (hdebtHi : debt ≤ ePos * C)
    (hcorrection : |correction| ≤ 70) :
    0 < rEnd * C + debt / 64 + correction / 64 ∧
      0 < rMid * C + debt / 64 + correction / 64 := by
  have hcorLo : -70 ≤ correction := (abs_le.mp hcorrection).1
  unfold rEnd rMid eAbs ePos at *
  constructor <;> nlinarith

theorem debt_bounds_scale (C e : Rat) (hC : 0 ≤ C)
    (heLo : -eAbs * C ≤ e) (heHi : e ≤ ePos * C) :
    -eAbs * C ≤ e ∧ e ≤ ePos * C := ⟨heLo, heHi⟩

theorem endpoint_reserve_bound (C e : Rat) (hC : 0 ≤ C)
    (heLo : -eAbs * C ≤ e) :
    max 0 (C / (2 * cap) - 31 * e / 64) ≤ reserveEndpoint * C := by
  have hbase : 0 ≤ reserveEndpoint * C := by
    unfold reserveEndpoint cap eAbs
    positivity
  apply max_le
  · exact hbase
  · unfold reserveEndpoint eAbs
    unfold eAbs at heLo
    have hscaled : -31 * e / 64 ≤ 31 * (31 / 268369920) * C / 64 := by
      nlinarith [heLo]
    unfold cap at *
    linarith

theorem internal_reserve_bound (j : Nat) (C e : Rat) (hC : 0 ≤ C)
    (hj1 : 1 ≤ j) (hj62 : j ≤ 62)
    (heLo : -eAbs * C ≤ e) (heHi : e ≤ ePos * C) :
    max 0 (C / (2 * cap) + ((32 : Rat) - j) * e / 64) +
      max 0 (C / (2 * cap) + ((j : Rat) - 31) * e / 64) ≤
        reserve * C := by
  have hj1R : (1 : Rat) ≤ j := by exact_mod_cast hj1
  have hj62R : (j : Rat) ≤ 62 := by exact_mod_cast hj62
  have hcoef1lo : -30 ≤ (32 : Rat) - j := by linarith
  have hcoef1hi : (32 : Rat) - j ≤ 31 := by linarith
  have hcoef2lo : -30 ≤ (j : Rat) - 31 := by linarith
  have hcoef2hi : (j : Rat) - 31 ≤ 31 := by linarith
  have hcoef1 : |(32 : Rat) - j| ≤ 31 := by
    rw [abs_le]
    constructor <;> linarith
  have hcoef2 : |(j : Rat) - 31| ≤ 31 := by
    rw [abs_le]
    constructor <;> linarith
  have hsum : ((32 : Rat) - j) + ((j : Rat) - 31) = 1 := by ring
  have hbase : 0 ≤ reserveInterior * C := by
    unfold reserveInterior cap ePos
    positivity
  have hbaseEnd : 0 ≤ reserveEndpoint * C := by
    unfold reserveEndpoint cap eAbs
    positivity
  by_cases hleft : 0 < C / (2 * cap) + ((32 : Rat) - j) * e / 64
  · by_cases hright : 0 < C / (2 * cap) + ((j : Rat) - 31) * e / 64
    · rw [max_eq_right (le_of_lt hleft), max_eq_right (le_of_lt hright)]
      have hsumExpr :
          C / (2 * cap) + ((32 : Rat) - j) * e / 64 +
            (C / (2 * cap) + ((j : Rat) - 31) * e / 64) = C / cap + e / 64 := by
        calc
          _ = C / cap + (((32 : Rat) - j) + ((j : Rat) - 31)) * e / 64 := by ring
          _ = C / cap + e / 64 := by rw [hsum]; ring
      have hresCompare : reserveInterior ≤ reserve := by
        unfold reserve reserveEndpoint reserveInterior cap eAbs ePos
        norm_num
      calc
        _ = C / cap + e / 64 := hsumExpr
        _ ≤ (1 / cap + ePos / 64) * C := by
          unfold cap ePos at *
          nlinarith [heHi]
        _ ≤ reserve * C := by
          unfold reserve reserveEndpoint reserveInterior cap eAbs ePos at *
          nlinarith [hresCompare, hC]
    · rw [max_eq_right (le_of_lt hleft), max_eq_left (le_of_not_gt hright)]
      have hmul : ((32 : Rat) - j) * e ≤ 31 * eAbs * C := by
        by_cases he : 0 ≤ e
        · calc
            ((32 : Rat) - j) * e ≤ 31 * e := mul_le_mul_of_nonneg_right hcoef1hi he
            _ ≤ 31 * eAbs * C := by norm_num [eAbs, ePos] at * <;> nlinarith
        · have he' : e ≤ 0 := le_of_not_ge he
          calc
            ((32 : Rat) - j) * e ≤ 31 * (-e) := by nlinarith [hcoef1]
            _ ≤ 31 * eAbs * C := by nlinarith [heLo]
      have hmulScaled : ((32 : Rat) - j) * e / 64 ≤ 31 * eAbs * C / 64 := by
        nlinarith [hmul]
      unfold eAbs cap at *
      unfold reserve reserveEndpoint cap eAbs
      nlinarith [hmulScaled]
  · by_cases hright : 0 < C / (2 * cap) + ((j : Rat) - 31) * e / 64
    · rw [max_eq_left (le_of_not_gt hleft), max_eq_right (le_of_lt hright)]
      have hmul : ((j : Rat) - 31) * e ≤ 31 * eAbs * C := by
        by_cases he : 0 ≤ e
        · calc
            ((j : Rat) - 31) * e ≤ 31 * e := mul_le_mul_of_nonneg_right hcoef2hi he
            _ ≤ 31 * eAbs * C := by norm_num [eAbs, ePos] at * <;> nlinarith
        · have he' : e ≤ 0 := le_of_not_ge he
          calc
            ((j : Rat) - 31) * e ≤ 31 * (-e) := by nlinarith [hcoef2]
            _ ≤ 31 * eAbs * C := by nlinarith [heLo]
      have hmulScaled : ((j : Rat) - 31) * e / 64 ≤ 31 * eAbs * C / 64 := by
        nlinarith [hmul]
      unfold eAbs cap at *
      unfold reserve reserveEndpoint cap eAbs
      nlinarith [hmulScaled]
    · rw [max_eq_left (le_of_not_gt hleft), max_eq_left (le_of_not_gt hright)]
      simpa [reserve] using hbaseEnd

theorem signed_path_endpoint_reserve (C : Rat) (hC : 0 ≤ C) (qs : List Rat)
    (hq : ∀ q ∈ qs, qEnd ≤ q ∧ q ≤ qMid) :
    max 0 (C / (2 * cap) - 31 * debtPath qs * C / 64) ≤ reserve * C := by
  have hd := debt_bounds_mul_capacity C hC qs hq
  have hend := endpoint_reserve_bound C (debtPath qs * C) hC hd.1
  convert hend using 1 <;> ring

theorem signed_path_internal_reserve (j : Nat) (C : Rat) (hC : 0 ≤ C)
    (hj1 : 1 ≤ j) (hj62 : j ≤ 62) (qs : List Rat)
    (hq : ∀ q ∈ qs, qEnd ≤ q ∧ q ≤ qMid) :
    max 0 (C / (2 * cap) + ((32 : Rat) - j) * debtPath qs * C / 64) +
      max 0 (C / (2 * cap) + ((j : Rat) - 31) * debtPath qs * C / 64) ≤
        reserve * C := by
  have hd := debt_bounds_mul_capacity C hC qs hq
  convert internal_reserve_bound j C (debtPath qs * C) hC hj1 hj62 hd.1 hd.2 using 1 <;> ring

theorem corrected_reserve_le_screened_margin :
    reserve < 1 / 10000000 := by
  unfold reserve reserveEndpoint cap eAbs
  norm_num

end Tapered945
