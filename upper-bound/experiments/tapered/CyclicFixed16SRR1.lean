import AKS.Chvatal.F2R1Fail
import AKS.Chvatal.FlipSpec
import Mathlib.Tactic

namespace Tapered945
open Chvatal

set_option maxHeartbeats 0

/-- At sixteen columns the standard admissible rank is exactly 65,536. -/
theorem std_jmax_16 : F2Params.std.jmax 16 = 65536 := by
  unfold F2Params.jmax
  change Nat.floor ((128 / 4095 : Real) * (131040 * 16 : Real)) = 65536
  have h : (128 / 4095 : Real) * (131040 * 16) = 65536 := by norm_num
  rw [h]
  exact Nat.floor_natCast 65536

/-- Any scramble at sixteen columns satisfies SR: the total mass permitted by
`jmax` is already below the SR threshold. -/
theorem any_scramble_F2SmallRank16 {m : Nat}
    (σ : Scramble m 16) : F2SmallRank F2Params.std σ := by
  intro c htotal S hS
  have hmass : totalColumnOnes c ≤ 65536 := by
    rw [std_jmax_16] at htotal
    exact (le_min_iff.mp htotal).2
  have hrows := onesInRows_le_total c σ (topRows m F2Params.std.g1) S
  have hthreshold : F2Params.std.f - F2Params.std.g1 + 1 = 78625 := by
    norm_num [F2Params.std]
  rw [hthreshold]
  omega

/-- The R1(a) event threshold exceeds all admissible sixteen-column mass,
uniformly in the rank parameter `E`. -/
theorem any_scramble_F2R1a16 {m : Nat}
    (σ : Scramble m 16) : F2R1a F2Params.std σ := by
  intro E hE c htotal S hS
  have hmass : totalColumnOnes c ≤ 65536 := by
    have hj : F2Params.std.jE 16 E ≤ 65536 := by
      rw [F2Params.jE, std_jmax_16]
      exact min_le_right _ _
    exact htotal.trans hj
  have hrows := onesInRows_le_total c σ (topRows m F2Params.std.g1) S
  have hκ : 1 ≤ F2Params.std.κ E := by
    unfold F2Params.κ
    apply Nat.ceil_pos.mpr
    have : (0 : Real) < (1 / 3 : Real) * E := by positivity
    exact this
  have hΔ : 52417 ≤ F2Params.std.Δ + 1 := by
    norm_num [F2Params.Δ, F2Params.std]
  have hsize : 2 ≤ F2Params.std.κ E + 1 := by omega
  have hthreshold : 104834 ≤ (F2Params.std.Δ + 1) * (F2Params.std.κ E + 1) := by
    calc
      104834 = 52417 * 2 := by norm_num
      _ ≤ (F2Params.std.Δ + 1) * (F2Params.std.κ E + 1) := Nat.mul_le_mul hΔ hsize
  omega

/-- The R1(b) threshold is at least 86,416, again exceeding all admissible
mass at sixteen columns. -/
theorem any_scramble_F2R1b16 {m : Nat}
    (σ : Scramble m 16) : F2R1b F2Params.std σ := by
  intro E hE c htotal S hS hSκ
  have hmass : totalColumnOnes c ≤ 65536 := by
    have hj : F2Params.std.jE 16 E ≤ 65536 := by
      rw [F2Params.jE, std_jmax_16]
      exact min_le_right _ _
    exact htotal.trans hj
  have hrows := onesInRows_le_total c σ (topRows m F2Params.std.g1) S
  have hB : 34000 ≤ F2Params.std.B E := by
    have hEreal : (2 : Real) ≤ E := by exact_mod_cast hE
    have hreal : (34000 : Real) ≤ (17000 : Real) * E := by nlinarith
    have hceil : F2Params.std.b * E ≤ (F2Params.std.B E : Real) := Nat.le_ceil _
    exact_mod_cast (le_trans hreal hceil)
  have hΔ : 52416 ≤ F2Params.std.Δ := by
    norm_num [F2Params.Δ, F2Params.std]
  have hthreshold : 86416 ≤ F2Params.std.Δ * S.card + F2Params.std.B E := by
    have hprod : 52416 ≤ F2Params.std.Δ * S.card := by
      calc
        52416 = 52416 * 1 := by norm_num
        _ ≤ F2Params.std.Δ * S.card := Nat.mul_le_mul hΔ hS
    omega
  omega

/-- The two deterministic first-round predicates hold for every scramble at
the fixed width 16; consequently they hold for the cyclic scramble and its
flip. -/
theorem any_scramble_SR_R1_16 {m : Nat}
    (σ : Scramble m 16) :
    F2SmallRank F2Params.std σ ∧ F2R1 F2Params.std σ := by
  exact ⟨any_scramble_F2SmallRank16 σ,
    ⟨any_scramble_F2R1a16 σ, any_scramble_F2R1b16 σ⟩⟩

end Tapered945
