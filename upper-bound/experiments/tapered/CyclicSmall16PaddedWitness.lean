import CyclicSmall16Provider
import PaddedSeparator
import BaselineFringe
import AKS.Chvatal.PackNodeSpec2
import SignedReserve
import RaggedIntegerSchedule
import Mathlib.Tactic

namespace Tapered945

open Chvatal

/-- A width-16 padded pack for the scheduled scale below `2^38`.  Its
small-fringe parameters are tuned to the minimum ordinary up-flow. -/
structure CyclicSmall16PaddedWitness (a : Nat) where
  retainedRows : Nat
  rows_lo : 2^30 ≤ retainedRows + 1
  rows_hi : retainedRows + 1 ≤ 2^35
  live_ge : retainedRows * 16 ≤ a
  live_le : a ≤ (retainedRows + 1) * 16
  padding_lt : (retainedRows + 1) * 16 - a < 16
  scramble₁ : Scramble (retainedRows + 1) 16
  scramble₂ : Scramble (retainedRows + 1) 16
  network : ComparatorNetwork a
  network_eq : network = paddedPack2Net (by omega) live_le scramble₁ scramble₂
  depth_le : network.depth ≤ 1890
  crossing : ∀ (p : Equiv.Perm (Fin a)) r, r ≤ a →
    ((Finset.univ.filter fun c : Fin a =>
      r ≤ (network.exec p c).val ∧ c.val < r).card : Real) ≤
      ((1/2^21 : Real) / 2) * ((retainedRows+1) * 16) + 16 ∧
    ((Finset.univ.filter fun c : Fin a =>
      (network.exec p c).val < r ∧ r ≤ c.val).card : Real) ≤
      ((1/2^21 : Real) / 2) * ((retainedRows+1) * 16) + 16
  smallRank₁ : F2SmallRank cyclicSmall16Params
    (truncateBottomScramble scramble₁)
  firstFringe₁ : F2R1 cyclicSmall16Params
    (truncateBottomScramble scramble₁)
  secondFringe₂ : F2R2n cyclicSmall16Params
    (truncateBottomScramble scramble₂)
  flipSmallRank₁ : F2SmallRank cyclicSmall16Params
    (truncateBottomScramble (flipScramble scramble₁))
  flipFirstFringe₁ : F2R1 cyclicSmall16Params
    (truncateBottomScramble (flipScramble scramble₁))
  flipSecondFringe₂ : F2R2n cyclicSmall16Params
    (truncateBottomScramble (flipScramble scramble₂))

/-- Construct a small-scale witness whenever the live size is between the
ordinary capacity floor and `2^38`. -/
theorem cyclicSmall16_padded_witness_exists {a : Nat}
    (haLo : 2^34 ≤ a) (haHi : a < 2^38) :
    Nonempty (CyclicSmall16PaddedWitness a) := by
  let m := (a - 1) / 16
  have hmod : (a - 1) % 16 < 16 := Nat.mod_lt _ (by norm_num)
  have hdiv : (a - 1) % 16 + 16 * m = a - 1 := by
    simpa [m, Nat.mul_comm] using (Nat.mod_add_div (a - 1) 16)
  have hmLo : 2^30 ≤ m + 1 := by
    dsimp [m]
    have hquot : 2^30 - 1 ≤ (a - 1) / 16 := by
      apply (Nat.le_div_iff_mul_le (by norm_num : 0 < 16)).2
      omega
    omega
  have hmHi : m + 1 ≤ 2^35 := by
    dsimp [m]
    have hquot : (a - 1) / 16 < 2^34 :=
      (Nat.div_lt_iff_lt_mul (by norm_num : 0 < 16)).2 (by omega)
    omega
  have hrect : a ≤ (m + 1) * 16 := by
    have hmul : (m + 1) * 16 = 16 * m + 16 := by omega
    rw [hmul]
    have haeq : a = (a - 1) + 1 := by omega
    rw [haeq, ← hdiv]
    omega
  have hlive : m * 16 ≤ a := by
    have haeq : a = (a - 1) + 1 := by omega
    rw [haeq, ← hdiv]
    omega
  have hpad : (m + 1) * 16 - a < 16 := by
    have hmul : (m + 1) * 16 = 16 * m + 16 := by omega
    have haeq : a = (a - 1) + 1 := by omega
    rw [hmul, haeq, ← hdiv]
    omega
  obtain ⟨σ₁, σ₂, hnormal, hflip⟩ :=
    cyclicSmall16_truncated_fringe_pair_exists (m := m) hmLo
  have hn : 0 < 16 := by norm_num
  let net := paddedPack2Net hn hrect σ₁ σ₂
  have hdepth : net.depth ≤ 1890 := by
    have hp := pack2_depth_le (m+1) 16 hn σ₁ σ₂ 35 (by omega)
    have hd := paddedPack2Net_depth_le hn hrect σ₁ σ₂
    have h := hd.trans hp
    norm_num at h
    exact h
  refine ⟨{
    retainedRows := m
    rows_lo := by omega
    rows_hi := hmHi
    live_ge := hlive
    live_le := hrect
    padding_lt := hpad
    scramble₁ := σ₁
    scramble₂ := σ₂
    network := net
    network_eq := rfl
    depth_le := hdepth
    crossing := ?_
    smallRank₁ := hnormal.1
    firstFringe₁ := hnormal.2.1
    secondFringe₂ := hnormal.2.2.1
    flipSmallRank₁ := hflip.1
    flipFirstFringe₁ := hflip.2.1
    flipSecondFringe₂ := hflip.2.2.1
  }⟩
  intro p cut hcut
  simpa [net, Nat.cast_add] using
    paddedPack2Net_all_cut_bounds hn hrect σ₁ σ₂ (1/2^21)
      (by norm_num) hnormal.2.2.2 hflip.2.2.2 p cut hcut

/-- High-side rare-rank transfer for the small-scale witness. -/
theorem CyclicSmall16PaddedWitness.fHigh {a : Nat}
    (w : CyclicSmall16PaddedWitness a) (p : Equiv.Perm (Fin a))
    (u j : Nat) (hu : u ≤ a)
    (hfringe : (cyclicSmall16Params.f + 1) * 16 ≤
      u + ((w.retainedRows + 1) * 16 - a))
    (hj : 0 < j) (hja : j ≤ a)
    (hjmax : j ≤ cyclicSmall16Params.jmax 16) :
    ((Finset.univ.filter fun c : Fin a =>
      a-j ≤ (w.network.exec p c).val ∧ c.val < a-u).card : Real) <
        (1 / (cyclicSmall16Params.J : Real)) * j := by
  rw [w.network_eq]
  have hfm : cyclicSmall16Params.f ≤ w.retainedRows := by
    have hrows := w.rows_lo
    norm_num at hrows
    have hsmall : 16000 ≤ w.retainedRows := by omega
    have hf : cyclicSmall16Params.f = 16000 := by
      norm_num [cyclicSmall16Params]
    rw [hf]
    exact hsmall
  exact paddedPack2Net_fHigh_baseline cyclicSmall16Params (by norm_num)
    w.live_le w.live_ge hfm
    w.scramble₁ w.scramble₂ w.smallRank₁ w.firstFringe₁ w.secondFringe₂
    p u j hu hfringe hj hja hjmax

/-- Low-side rare-rank transfer for the small-scale witness. -/
theorem CyclicSmall16PaddedWitness.fLow {a : Nat}
    (w : CyclicSmall16PaddedWitness a) (p : Equiv.Perm (Fin a))
    (u j : Nat)
    (hfringe : (cyclicSmall16Params.f + 1) * 16 ≤ u)
    (hj : 0 < j) (hja : j ≤ a)
    (hjmax : j ≤ cyclicSmall16Params.jmax 16) :
    ((Finset.univ.filter fun c : Fin a =>
      (w.network.exec p c).val < j ∧ u ≤ c.val).card : Real) <
        (1 / (cyclicSmall16Params.J : Real)) * j := by
  rw [w.network_eq]
  have hfm : cyclicSmall16Params.f ≤ w.retainedRows := by
    have hrows := w.rows_lo
    norm_num at hrows
    have hsmall : 16000 ≤ w.retainedRows := by omega
    have hf : cyclicSmall16Params.f = 16000 := by
      norm_num [cyclicSmall16Params]
    rw [hf]
    exact hsmall
  exact paddedPack2Net_fLow_baseline cyclicSmall16Params (by norm_num)
    w.live_le hfm
    w.scramble₁ w.scramble₂ w.flipSmallRank₁ w.flipFirstFringe₁
    w.flipSecondFringe₂ p u j hfringe hj hja hjmax

/-- The tuned 256,016-wire low fringe fits the scheduled minimum up-flow. -/
theorem CyclicSmall16PaddedWitness.low_fringe_fits_of_up_lower_bound
    {a : Nat} (_w : CyclicSmall16PaddedWitness a) (C : Rat) (up : Nat)
    (hC : (2^34 : Rat) ≤ C)
    (hup : (up : Rat) ≥ (upFlow - ePos) * C - 1) :
    (cyclicSmall16Params.f + 1) * 16 ≤ up := by
  have hscale : (((cyclicSmall16Params.f + 1) * 16 : Nat) : Rat) ≤
      (upFlow - ePos) * C - 1 := by
    norm_num [cyclicSmall16Params, upFlow, ePos] at *
    nlinarith [hC]
  have hreal : (((cyclicSmall16Params.f + 1) * 16 : Nat) : Rat) ≤ up :=
    hscale.trans hup
  exact_mod_cast hreal

/-- The ordinary local-flow debt and integer rounding bounds imply the tuned
low-fringe fit at every scheduled interior bag with reference capacity at
least `2^34`. -/
theorem CyclicSmall16PaddedWitness.low_fringe_fits_of_local_flow
    {a d : Nat} (w : CyclicSmall16PaddedWitness a)
    (b : KBag 64 d) (C eta : Rat)
    (flow : LocalIntegerFlow b C eta a)
    (hC : (2^34 : Rat) ≤ C) :
    (cyclicSmall16Params.f + 1) * 16 ≤ flow.up := by
  have hdebt := bagAddressDebt_bounds b
  have hC0 : 0 ≤ C := by positivity
  have hideal : (upFlow - ePos) * C ≤ addressUpAt b C := by
    have hscaled : bagAddressDebt b * C ≤ ePos * C :=
      mul_le_mul_of_nonneg_right hdebt.2 hC0
    calc
      (upFlow - ePos) * C = upFlow * C - ePos * C := sub_mul _ _ _
      _ ≤ upFlow * C - bagAddressDebt b * C := by linarith
      _ = addressUpAt b C := by rfl
  have hrounded : (flow.up : Rat) ≥ (upFlow - ePos) * C - 1 := by
    have herror := flow.upError
    rw [abs_le] at herror
    have hround : (flow.up : Rat) ≥ addressUpAt b C - 1 := by linarith
    linarith
  exact w.low_fringe_fits_of_up_lower_bound C flow.up hC hrounded

end Tapered945
