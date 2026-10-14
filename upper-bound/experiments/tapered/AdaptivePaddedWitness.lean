import CyclicSmall16PaddedWitness
import TruncatedPaddedProvider
import SeparatorKeyBridge
import Mathlib.Tactic

namespace Tapered945

open Chvatal

/-- Common contract for the small tuned and large standard padded separators.
The network, both cut estimates, rare-rank bounds, and low-flow fit are all
attached to the same actual live register. -/
structure AdaptivePaddedWitness (a : Nat) where
  columns : Nat
  retainedRows : Nat
  live_ge : retainedRows * columns ≤ a
  padding : Nat
  padding_eq : padding = (retainedRows + 1) * columns - a
  fringeWires : Nat
  maxRank : Nat
  network : ComparatorNetwork a
  depth_le : network.depth ≤ 1890
  crossing : ∀ (p : Equiv.Perm (Fin a)) r, r ≤ a →
    ((Finset.univ.filter fun c : Fin a =>
      r ≤ (network.exec p c).val ∧ c.val < r).card : Real) ≤
      ((1/2^21 : Real) / 2) * ((retainedRows+1) * columns) + columns ∧
    ((Finset.univ.filter fun c : Fin a =>
      (network.exec p c).val < r ∧ r ≤ c.val).card : Real) ≤
      ((1/2^21 : Real) / 2) * ((retainedRows+1) * columns) + columns
  highRareRank : ∀ (p : Equiv.Perm (Fin a)) u j, u ≤ a →
    fringeWires ≤ u + padding → 0 < j → j ≤ a → j ≤ maxRank →
      ((Finset.univ.filter fun c : Fin a =>
        a-j ≤ (network.exec p c).val ∧ c.val < a-u).card : Real) <
          (1 / (9000000 : Real)) * j
  lowRareRank : ∀ (p : Equiv.Perm (Fin a)) u j,
    fringeWires ≤ u → 0 < j → j ≤ a → j ≤ maxRank →
      ((Finset.univ.filter fun c : Fin a =>
        (network.exec p c).val < j ∧ u ≤ c.val).card : Real) <
          (1 / (9000000 : Real)) * j
  lowFits : ∀ {d : Nat} (b : KBag 64 d) (C eta : Rat)
    (flow : LocalIntegerFlow b C eta a),
    (2^34 : Rat) ≤ C → |eta| ≤ 69 →
    (a : Rat) = (1 - 1 / cap) * C + eta →
      fringeWires ≤ flow.up

/-- Apply the adaptive separator to an actual key enumeration. The witness's
two-sided crossing estimate supplies both normalized output-boundary errors;
only the input rank-window error remains as a premise. -/
theorem AdaptivePaddedWitness.output_slot_wrong_le {a M : Nat}
    (w : AdaptivePaddedWitness a) (xr : Fin a → Fin M)
    (hxr : Function.Injective xr) (L H lo hi : Nat) (hLa : L ≤ a)
    (hHa : H ≤ a) (A : Real)
    (hA : ((((keySet xr).image Fin.val).filter (fun κ =>
      L ≤ BW.rankN ((keySet xr).image Fin.val) κ ∧
      BW.rankN ((keySet xr).image Fin.val) κ < H ∧
      ¬ (lo ≤ κ ∧ κ < hi))).card : Real) ≤ A) :
    ((((Finset.univ.filter (fun c : Fin a => L ≤ c.val ∧ c.val < H)).image
      (fun c => (w.network.exec xr c).val)).filter
      (fun κ => ¬ (lo ≤ κ ∧ κ < hi))).card : Real) ≤
        A + 2 * (((1 / 2^21 : Real) / 2) *
          ((w.retainedRows + 1) * w.columns) + w.columns) := by
  have hL := w.crossing (rankPerm hxr) L hLa
  have hH := w.crossing (rankPerm hxr) H hHa
  have h := separator_output_wrong_keys_le w.network xr hxr L H lo hi A
    (((1 / 2^21 : Real) / 2) * ((w.retainedRows + 1) * w.columns) + w.columns)
    (((1 / 2^21 : Real) / 2) * ((w.retainedRows + 1) * w.columns) + w.columns)
    hA hL.2 hH.1
  calc
    _ ≤ A + (((1 / 2^21 : Real) / 2) * ((w.retainedRows + 1) * w.columns) + w.columns) +
        (((1 / 2^21 : Real) / 2) * ((w.retainedRows + 1) * w.columns) + w.columns) := h
    _ = _ := by ring

/-- Adapt a tuned width-16 witness to the common interface. -/
noncomputable def AdaptivePaddedWitness.ofSmall {a : Nat}
    (w : CyclicSmall16PaddedWitness a) : AdaptivePaddedWitness a where
  columns := 16
  retainedRows := w.retainedRows
  live_ge := w.live_ge
  padding := (w.retainedRows + 1) * 16 - a
  padding_eq := rfl
  fringeWires := (cyclicSmall16Params.f + 1) * 16
  maxRank := cyclicSmall16Params.jmax 16
  network := w.network
  depth_le := w.depth_le
  crossing := w.crossing
  highRareRank := by
    intro p u j hu hfit hj hja hjmax
    change (cyclicSmall16Params.f + 1) * 16 ≤
      u + ((w.retainedRows + 1) * 16 - a) at hfit
    exact w.fHigh p u j hu hfit
      hj hja hjmax
  lowRareRank := by
    intro p u j hfit hj hja hjmax
    exact w.fLow p u j hfit hj hja hjmax
  lowFits := by
    intro d b C eta flow hC heta hcount
    exact w.low_fringe_fits_of_local_flow b C eta flow hC

/-- Adapt the existing standard-parameter witness. Its stronger `1/86M`
rare-rank estimate implies the common `1/9M` interface. -/
noncomputable def AdaptivePaddedWitness.ofLarge {a : Nat}
    (w : TruncatedPaddedWitness a) : AdaptivePaddedWitness a where
  columns := w.columns
  retainedRows := w.retainedRows
  live_ge := w.live_ge
  padding := (w.retainedRows + 1) * w.columns - a
  padding_eq := rfl
  fringeWires := (F2Params.std.f + 1) * w.columns
  maxRank := F2Params.std.jmax w.columns
  network := w.network
  depth_le := w.depth_le
  crossing := w.crossing
  highRareRank := by
    intro p u j hu hfit hj hja hjmax
    change (F2Params.std.f + 1) * w.columns ≤
      u + ((w.retainedRows + 1) * w.columns - a) at hfit
    have hfm : F2Params.std.f ≤ w.retainedRows := by
      have hrows := w.rows_lo
      norm_num [F2Params.std] at hrows ⊢
      omega
    have htail := w.fHigh_baseline p hfm u j hu hfit hj hja hjmax
    have hcoeff : (1 / (F2Params.std.J : Real)) ≤ 1 / (9000000 : Real) := by
      norm_num [F2Params.std]
    have hj0 : (0 : Real) ≤ j := by positivity
    exact htail.trans_le (mul_le_mul_of_nonneg_right hcoeff hj0)
  lowRareRank := by
    intro p u j hfit hj hja hjmax
    change (F2Params.std.f + 1) * w.columns ≤ u at hfit
    have htail := w.fLow_baseline p u j hfit hj hja hjmax
    have hcoeff : (1 / (F2Params.std.J : Real)) ≤ 1 / (9000000 : Real) := by
      norm_num [F2Params.std]
    have hj0 : (0 : Real) ≤ j := by positivity
    exact htail.trans_le (mul_le_mul_of_nonneg_right hcoeff hj0)
  lowFits := by
    intro d b C eta flow hC heta hcount
    exact w.low_fringe_fits_of_scheduled_flow b C eta flow hC heta hcount


/-- Every live size at or above the candidate's minimum capacity has one of
the two scale-specific separator providers. -/
theorem adaptive_padded_witness_exists {a : Nat}
    (ha : 2^34 ≤ a) : Nonempty (AdaptivePaddedWitness a) := by
  by_cases hsmall : a < 2^38
  · exact ⟨AdaptivePaddedWitness.ofSmall
      (Classical.choice (cyclicSmall16_padded_witness_exists ha hsmall))⟩
  · exact ⟨AdaptivePaddedWitness.ofLarge
      (Classical.choice (large_truncated_padded_witness_exists a (by omega)))⟩

end Tapered945
