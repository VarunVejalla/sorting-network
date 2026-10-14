import TruncatedFringeProvider
import PaddedSeparator
import BaselineFringe
import AKS.Chvatal.PackNodeSpec2
import SignedReserve
import RaggedIntegerSchedule

namespace Tapered945

open Chvatal

/-- A padded physical pack with its actual bulk and truncated-fringe
certificates attached to the very same pair of scrambles. -/
structure TruncatedPaddedWitness (a : Nat) where
  retainedRows : Nat
  columns : Nat
  columns_pow : ∃ e, columns = 2^e
  columns_ge : 16 ≤ columns
  rows_lo : 2^34 ≤ retainedRows + 1
  rows_hi : retainedRows + 1 ≤ 2^35
  live_ge : retainedRows * columns ≤ a
  live_le : a ≤ (retainedRows + 1) * columns
  padding_lt : (retainedRows + 1) * columns - a < columns
  scramble₁ : Scramble (retainedRows + 1) columns
  scramble₂ : Scramble (retainedRows + 1) columns
  network : ComparatorNetwork a
  network_eq : network = paddedPack2Net (by omega) live_le scramble₁ scramble₂
  depth_le : network.depth ≤ 1890
  crossing : ∀ (p : Equiv.Perm (Fin a)) r, r ≤ a →
    ((Finset.univ.filter fun c : Fin a =>
      r ≤ (network.exec p c).val ∧ c.val < r).card : Real) ≤
      ((1/2^21 : Real) / 2) * ((retainedRows+1) * columns) + columns ∧
    ((Finset.univ.filter fun c : Fin a =>
      (network.exec p c).val < r ∧ r ≤ c.val).card : Real) ≤
      ((1/2^21 : Real) / 2) * ((retainedRows+1) * columns) + columns
  smallRank₁ : F2SmallRank F2Params.std (truncateBottomScramble scramble₁)
  firstFringe₁ : F2R1 F2Params.std (truncateBottomScramble scramble₁)
  secondFringe₂ : F2R2n F2Params.std (truncateBottomScramble scramble₂)
  flipSmallRank₁ : F2SmallRank F2Params.std
    (truncateBottomScramble (flipScramble scramble₁))
  flipFirstFringe₁ : F2R1 F2Params.std
    (truncateBottomScramble (flipScramble scramble₁))
  flipSecondFringe₂ : F2R2n F2Params.std
    (truncateBottomScramble (flipScramble scramble₂))

theorem large_truncated_padded_witness_exists (a : Nat) (ha : 2^38 ≤ a) :
    Nonempty (TruncatedPaddedWitness a) := by
  obtain ⟨rows, columns, hpow, hcols, hrowLo, hrowHi, hrect, hpad⟩ :=
    nearby_rectangle a ha
  cases rows with
  | zero => omega
  | succ r =>
    have hret : 131040 ≤ r := by omega
    obtain ⟨σ₁, σ₂, hnormal, hflip⟩ := truncated_fringe_bulk_pair_exists
      (m := r) (by simpa using hrowLo) hret hcols
    have hn : 0 < columns := by omega
    let net := paddedPack2Net hn hrect σ₁ σ₂
    have hdepth : net.depth ≤ 1890 := by
      have hp := pack2_depth_le (r+1) columns hn σ₁ σ₂ 35 (by omega)
      have hd := paddedPack2Net_depth_le hn hrect σ₁ σ₂
      have h := hd.trans hp
      norm_num at h
      exact h
    exact ⟨{
      retainedRows := r
      columns := columns
      columns_pow := hpow
      columns_ge := hcols
      rows_lo := by simpa using hrowLo
      rows_hi := by simpa using hrowHi
      live_ge := by
        have hp := hpad
        rw [Nat.succ_mul] at hp
        omega
      live_le := hrect
      padding_lt := hpad
      scramble₁ := σ₁
      scramble₂ := σ₂
      network := net
      network_eq := rfl
      depth_le := hdepth
      crossing := by
        intro p cut hcut
        simpa [net, Nat.cast_add] using
          paddedPack2Net_all_cut_bounds hn hrect σ₁ σ₂ (1/2^21)
            (by norm_num) hnormal.2.2.2 hflip.2.2.2 p cut hcut
      smallRank₁ := hnormal.1
      firstFringe₁ := hnormal.2.1
      secondFringe₂ := hnormal.2.2.1
      flipSmallRank₁ := hflip.1
      flipFirstFringe₁ := hflip.2.1
      flipSecondFringe₂ := hflip.2.2.1
    }⟩

/-- The packed witness supplies a genuine multiplicative high-fringe estimate
for every live cohort whose protected rows fit the caller's selected suffix. -/
theorem TruncatedPaddedWitness.fHigh_baseline {a : Nat}
    (w : TruncatedPaddedWitness a) (p : Equiv.Perm (Fin a))
    (hfm : F2Params.std.f ≤ w.retainedRows) (u j : Nat) (hu : u ≤ a)
    (hfringe : (F2Params.std.f + 1) * w.columns ≤
      u + ((w.retainedRows + 1) * w.columns - a))
    (hj : 0 < j) (hja : j ≤ a) (hjmax : j ≤ F2Params.std.jmax w.columns) :
    ((Finset.univ.filter fun c : Fin a =>
      a - j ≤ (w.network.exec p c).val ∧ c.val < a - u).card : Real) <
        (1 / (F2Params.std.J : Real)) * j := by
  rw [w.network_eq]
  exact paddedPack2Net_fHigh_baseline (m := w.retainedRows) (n := w.columns) (a := a)
    F2Params.std (by have := w.columns_ge; omega) w.live_le w.live_ge hfm
    w.scramble₁ w.scramble₂ w.smallRank₁ w.firstFringe₁ w.secondFringe₂
    p u j hu hfringe hj hja hjmax

/-- Matching multiplicative low-fringe guarantee for the same restricted
network, using the witness's flipped truncated certificates. -/
theorem TruncatedPaddedWitness.fLow_baseline {a : Nat}
    (w : TruncatedPaddedWitness a) (p : Equiv.Perm (Fin a))
    (u j : Nat)
    (hfringe : (F2Params.std.f + 1) * w.columns ≤ u)
    (hj : 0 < j) (hja : j ≤ a) (hjmax : j ≤ F2Params.std.jmax w.columns) :
    ((Finset.univ.filter fun c : Fin a =>
      ((w.network).exec p c).val < j ∧ u ≤ c.val).card : Real) <
        (1 / (F2Params.std.J : Real)) * j := by
  rw [w.network_eq]
  have hn : 0 < w.columns := by have := w.columns_ge; omega
  have hfm : F2Params.std.f ≤ w.retainedRows := by
    have hrows := w.rows_lo
    norm_num [F2Params.std] at hrows ⊢
    omega
  exact paddedPack2Net_fLow_baseline F2Params.std hn w.live_le
    hfm w.scramble₁ w.scramble₂
    w.flipSmallRank₁ w.flipFirstFringe₁ w.flipSecondFringe₂ p u j hfringe hj hja hjmax

/-- The candidate up-flow comfortably fits the low-side protected fringe,
provided the actual node size is within 69 wires of its reference capacity.
This isolates the only numerical geometry premise needed to instantiate
`fLow_baseline` at a scheduled interior node. -/
theorem TruncatedPaddedWitness.low_fringe_fits_of_up_lower_bound {a : Nat}
    (w : TruncatedPaddedWitness a) (C : Rat) (up : Nat)
    (hC : (2 ^ 34 : Rat) ≤ C)
    (ha : (a : Rat) ≤ C + 69)
    (hup : (up : Rat) ≥ (upFlow - ePos) * C - 1) :
    (F2Params.std.f + 1) * w.columns ≤ up := by
  have hrows : (2 ^ 34 - 1 : Nat) ≤ w.retainedRows := by
    have := w.rows_lo
    omega
  have hcap : ((2 ^ 34 - 1 : Nat) : Rat) * w.columns ≤ a := by
    have hmul := Nat.mul_le_mul_right w.columns hrows
    have hnat := hmul.trans w.live_ge
    exact_mod_cast hnat
  have hprod : (2 ^ 34 - 1 : Rat) *
        (((F2Params.std.f + 1) * w.columns : Nat) : Rat) ≤
      ((F2Params.std.f + 1 : Nat) : Rat) * a := by
    calc
      _ = ((F2Params.std.f + 1 : Nat) : Rat) *
          (((2 ^ 34 - 1 : Nat) : Rat) * w.columns) := by push_cast; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hcap (by positivity)
  have hsize : ((F2Params.std.f + 1 : Nat) : Rat) * a ≤
      ((F2Params.std.f + 1 : Nat) : Rat) * (C + 69) :=
    mul_le_mul_of_nonneg_left ha (by positivity)
  have hscale : ((F2Params.std.f + 1 : Nat) : Rat) * (C + 69) ≤
      (2 ^ 34 - 1 : Rat) * ((upFlow - ePos) * C - 1) := by
    norm_num [F2Params.std, upFlow, ePos] at *
    nlinarith [hC]
  have hlow := mul_le_mul_of_nonneg_left hup (by norm_num : (0 : Rat) ≤ 2 ^ 34 - 1)
  have hM : (0 : Rat) < 2 ^ 34 - 1 := by norm_num
  have hreal : (((F2Params.std.f + 1) * w.columns : Nat) : Rat) ≤ up := by
    nlinarith [hprod, hsize, hscale, hlow]
  exact_mod_cast hreal

/-- The scheduled integer-flow invariant supplies the lower bound required by
`low_fringe_fits_of_up_lower_bound`: address debt can reduce ideal up-flow by
at most `ePos * C`, and integer rounding costs at most one wire. -/
theorem TruncatedPaddedWitness.low_fringe_fits_of_local_flow {a d : Nat}
    (w : TruncatedPaddedWitness a) (b : KBag 64 d) (C eta : Rat)
    (flow : LocalIntegerFlow b C eta a)
    (hC : (2 ^ 34 : Rat) ≤ C)
    (ha : (a : Rat) ≤ C + 69) :
    (F2Params.std.f + 1) * w.columns ≤ flow.up := by
  have hdebt := bagAddressDebt_bounds b
  have hC0 : 0 ≤ C := by positivity
  have hideal : (upFlow - ePos) * C ≤ addressUpAt b C := by
    have hscaled : bagAddressDebt b * C ≤ ePos * C :=
      mul_le_mul_of_nonneg_right hdebt.2 hC0
    calc
      (upFlow - ePos) * C = upFlow * C - ePos * C := sub_mul _ _ _
      _ ≤ upFlow * C - bagAddressDebt b * C := by linarith
      _ = addressUpAt b C := by rfl
  have hrounded : ((flow.up : Nat) : Rat) ≥
      (upFlow - ePos) * C - 1 := by
    have herror := flow.upError
    rw [abs_le] at herror
    have hround : (flow.up : Rat) ≥ addressUpAt b C - 1 := by linarith
    linarith
  exact w.low_fringe_fits_of_up_lower_bound C flow.up hC ha hrounded

/-- Package the scheduled count error and local integer flow directly into the
low-fringe fit condition. -/
theorem TruncatedPaddedWitness.low_fringe_fits_of_scheduled_flow {a d : Nat}
    (w : TruncatedPaddedWitness a) (b : KBag 64 d) (C eta : Rat)
    (flow : LocalIntegerFlow b C eta a)
    (hC : (2 ^ 34 : Rat) ≤ C) (heta : |eta| ≤ 69)
    (hcount : (a : Rat) = (1 - 1 / cap) * C + eta) :
    (F2Params.std.f + 1) * w.columns ≤ flow.up := by
  have hetaHi : eta ≤ 69 := abs_le.mp heta |>.2
  have hcap : 0 < cap := by norm_num [cap]
  have hC0 : 0 ≤ C := by positivity
  have hcoefficient : 1 - 1 / cap ≤ 1 := by
    have := one_div_pos.mpr hcap
    linarith
  have ha : (a : Rat) ≤ C + 69 := by
    rw [hcount]
    nlinarith [mul_le_mul_of_nonneg_right hcoefficient hC0]
  exact w.low_fringe_fits_of_local_flow b C eta flow hC ha

end Tapered945
