import AKS.Chvatal.F2R1Fail
import AKS.Chvatal.F2Det
import SignedReserve
import Mathlib.Tactic

namespace Tapered945
open Chvatal

set_option maxHeartbeats 0

/-- Width-16 tuned F2 parameters. The smaller `f` fits the scheduled up-port;
the larger `J` keeps the recursive fringe coefficient small. At width 16 the
R2n range is empty. -/
noncomputable def cyclicSmall16Params : F2Params where
  f := 16000
  g1 := 6400
  g2 := 12800
  J := 9000000
  c := 1 / 3
  b := 1410
  hg1 := by norm_num
  hg12 := by norm_num
  hg2f := by norm_num
  hJ := by norm_num
  hc0 := by norm_num
  hb0 := by norm_num
  hc_half := by norm_num
  hD1 := by norm_num
  hD2 := by norm_num
  hD3 := by norm_num
  hcΔ := by norm_num
  hbJ := by norm_num
  hΦ := by norm_num
  hκ := by norm_num

/-- At width 16 the admissible rank is at most 8,001. -/
theorem cyclicSmall16_jmax_le : cyclicSmall16Params.jmax 16 ≤ 8001 := by
  change ⌊(128 / 4095 : Real) * (16000 * 16)⌋₊ ≤ 8001
  have hfloor : (⌊(128 / 4095 : Real) * (16000 * 16)⌋₊ : Real) ≤
      (128 / 4095 : Real) * (16000 * 16) := Nat.floor_le (by positivity)
  have htop : (128 / 4095 : Real) * (16000 * 16) < 8002 := by norm_num
  have hnat : ⌊(128 / 4095 : Real) * (16000 * 16)⌋₊ < 8002 := by
    exact_mod_cast lt_of_le_of_lt hfloor htop
  omega

/-- All width-16 scrambles satisfy the small-rank condition by total-mass
domination. -/
theorem any_scramble_small16_SR {m : Nat} (σ : Scramble m 16) :
    F2SmallRank cyclicSmall16Params σ := by
  intro c htotal S hS
  have hmass : totalColumnOnes c ≤ 8001 := by
    have h := (le_min_iff.mp htotal).2
    exact h.trans cyclicSmall16_jmax_le
  have hrows := onesInRows_le_total c σ
    (topRows m cyclicSmall16Params.g1) S
  have hthreshold : cyclicSmall16Params.f - cyclicSmall16Params.g1 + 1 = 9601 := by
    norm_num [cyclicSmall16Params]
  rw [hthreshold]
  omega

/-- R1(a) is deterministic at width 16 for the tuned parameters. -/
theorem any_scramble_small16_R1a {m : Nat} (σ : Scramble m 16) :
    F2R1a cyclicSmall16Params σ := by
  intro E hE c htotal S hS
  have hmass : totalColumnOnes c ≤ 8001 := by
    have hj : cyclicSmall16Params.jE 16 E ≤ 8001 := by
      rw [F2Params.jE]
      exact (min_le_right _ _).trans cyclicSmall16_jmax_le
    exact htotal.trans hj
  have hrows := onesInRows_le_total c σ
    (topRows m cyclicSmall16Params.g1) S
  have hκ : 1 ≤ cyclicSmall16Params.κ E := by
    unfold F2Params.κ cyclicSmall16Params
    apply Nat.ceil_pos.mpr
    positivity
  have hthreshold : 12802 ≤
      (cyclicSmall16Params.Δ + 1) * (cyclicSmall16Params.κ E + 1) := by
    have hdelta : 6401 ≤ cyclicSmall16Params.Δ + 1 := by
      norm_num [F2Params.Δ, cyclicSmall16Params]
    have hsize : 2 ≤ cyclicSmall16Params.κ E + 1 := by omega
    calc
      12802 = 6401 * 2 := by norm_num
      _ ≤ _ := Nat.mul_le_mul hdelta hsize
  omega

/-- R1(b)'s smallest threshold exceeds the entire admissible mass. -/
theorem any_scramble_small16_R1b {m : Nat} (σ : Scramble m 16) :
    F2R1b cyclicSmall16Params σ := by
  intro E hE c htotal S hS hSκ
  have hmass : totalColumnOnes c ≤ 8001 := by
    have hj : cyclicSmall16Params.jE 16 E ≤ 8001 := by
      rw [F2Params.jE]
      exact (min_le_right _ _).trans cyclicSmall16_jmax_le
    exact htotal.trans hj
  have hrows := onesInRows_le_total c σ
    (topRows m cyclicSmall16Params.g1) S
  have hB : 2820 ≤ cyclicSmall16Params.B E := by
    have hEreal : (2 : Real) ≤ E := by exact_mod_cast hE
    have hreal : (2820 : Real) ≤ cyclicSmall16Params.b * E := by
      change (2820 : Real) ≤ 1410 * E
      nlinarith
    have hceil : cyclicSmall16Params.b * E ≤
        (cyclicSmall16Params.B E : Real) := Nat.le_ceil _
    exact_mod_cast le_trans hreal hceil
  have hdelta : 6400 ≤ cyclicSmall16Params.Δ := by
    norm_num [F2Params.Δ, cyclicSmall16Params]
  have hthreshold : 9220 ≤
      cyclicSmall16Params.Δ * S.card + cyclicSmall16Params.B E := by
    have hprod : 6400 ≤ cyclicSmall16Params.Δ * S.card := by
      calc
        6400 = 6400 * 1 := by norm_num
        _ ≤ _ := Nat.mul_le_mul hdelta hS
    omega
  omega

/-- At width 16, `R2n` has no admissible rank parameter; it holds for every
second scramble. -/
theorem any_scramble_small16_R2n {m : Nat} (σ : Scramble m 16) :
    F2R2n cyclicSmall16Params σ := by
  intro E hE hEn c hc1 hc2 S hS
  have hj := cyclicSmall16_jmax_le
  have hJ : 9000000 ≤ cyclicSmall16Params.J := by
    norm_num [cyclicSmall16Params]
  have hEJ : 9000000 ≤ (E - 1) * cyclicSmall16Params.J := by
    have hmul := Nat.mul_le_mul_right cyclicSmall16Params.J
      (show 1 ≤ E - 1 by omega)
    norm_num [cyclicSmall16Params] at hmul ⊢
    exact hmul
  omega

/-- Full deterministic F2 input conditions at width 16. -/
theorem any_scramble_small16_F2Inputs {m : Nat} (σ : Scramble m 16) :
    F2SmallRank cyclicSmall16Params σ ∧ F2R1 cyclicSmall16Params σ ∧
      F2R2n cyclicSmall16Params σ := by
  exact ⟨any_scramble_small16_SR σ,
    ⟨⟨any_scramble_small16_R1a σ, any_scramble_small16_R1b σ⟩,
      any_scramble_small16_R2n σ⟩⟩

/-- The tuned rare-rank coefficient still fits the ordinary-kernel scalar
budget. -/
theorem cyclicSmall16_fringe_scalar :
    (1 / (cyclicSmall16Params.J : Rat)) +
        (64 : Rat)^3 * delta^2 ≤ 4 * delta := by
  norm_num [cyclicSmall16Params, delta]

end Tapered945
