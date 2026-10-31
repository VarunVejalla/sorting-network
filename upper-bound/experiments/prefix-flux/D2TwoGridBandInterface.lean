import D2Slope25LiftProvider
import Mathlib.Data.Finset.Lattice.Fold

open Chvatal.D2Slope25LiftProvider
open Chvatal.D2Slope25Physical
open Chvatal.D2Slope25Provider

namespace Chvatal.D2TwoGridBandInterface

abbrev Col := Fin 64
abbrev Row := Fin 4096

def outputHeight (h : Col -> Nat) (c : Col) : Nat :=
  fullHeightTwoShuffle h c

def threshold (h : Col -> Nat) (c : Col) : Nat :=
  4096 - outputHeight h c

def lowBoundary (h : Col -> Nat) : Nat :=
  Finset.univ.inf' Finset.univ_nonempty (threshold h)

def highBoundary (h : Col -> Nat) : Nat :=
  Finset.univ.sup' Finset.univ_nonempty (threshold h)

def bottomUnary (h : Col -> Nat) (r : Row) (c : Col) : Bool :=
  decide (threshold h c <= r.val)

def rowScrambledUnary (h : Col -> Nat) (perm : Row -> Equiv.Perm Col)
    (r : Row) (c : Col) : Bool :=
  bottomUnary h r (perm r c)

theorem threshold_le_add_thirteen (h : Col -> Nat)
    (hbound : forall c, h c <= 4096) (c d : Col) :
    threshold h c <= threshold h d + 13 := by
  have hrange := fullHeightTwoShuffle_range_le_thirteen h d c
  have hc := fullHeightTwoShuffle_le_4096 h hbound c
  have hd := fullHeightTwoShuffle_le_4096 h hbound d
  unfold threshold outputHeight
  omega

theorem highBoundary_le_lowBoundary_add_thirteen (h : Col -> Nat)
    (hbound : forall c, h c <= 4096) :
    highBoundary h <= lowBoundary h + 13 := by
  let hex := Finset.exists_mem_eq_inf' Finset.univ_nonempty (threshold h)
  let d := hex.choose
  have hlow : lowBoundary h = threshold h d := hex.choose_spec.2
  apply Finset.sup'_le Finset.univ_nonempty
  intro c hc
  rw [hlow]
  exact threshold_le_add_thirteen h hbound c d

theorem lowBoundary_le_highBoundary (h : Col -> Nat) :
    lowBoundary h <= highBoundary h := by
  let hex := Finset.exists_mem_eq_inf' Finset.univ_nonempty (threshold h)
  let d := hex.choose
  have hlow : lowBoundary h = threshold h d := hex.choose_spec.2
  rw [hlow]
  exact Finset.le_sup' (threshold h) (Finset.mem_univ d)

theorem highBoundary_le_4096 (h : Col -> Nat) : highBoundary h <= 4096 := by
  apply Finset.sup'_le Finset.univ_nonempty
  intro c hc
  exact Nat.sub_le _ _

theorem band_width_le_thirteen (h : Col -> Nat)
    (hbound : forall c, h c <= 4096) :
    highBoundary h - lowBoundary h <= 13 := by
  have hrange := highBoundary_le_lowBoundary_add_thirteen h hbound
  have horder := lowBoundary_le_highBoundary h
  omega

theorem bottomUnary_false_below_band (h : Col -> Nat) (r : Row)
    (hr : r.val < lowBoundary h) (c : Col) :
    bottomUnary h r c = false := by
  have hmin : lowBoundary h <= threshold h c :=
    Finset.inf'_le (threshold h) (Finset.mem_univ c)
  have hlt : r.val < threshold h c := lt_of_lt_of_le hr hmin
  change decide (threshold h c <= r.val) = false
  exact decide_eq_false (Nat.not_le.mpr hlt)

theorem bottomUnary_true_above_band (h : Col -> Nat) (r : Row)
    (hr : highBoundary h <= r.val) (c : Col) :
    bottomUnary h r c = true := by
  have hmax : threshold h c <= highBoundary h :=
    Finset.le_sup' (threshold h) (Finset.mem_univ c)
  simp [bottomUnary, le_trans hmax hr]

theorem rowScramble_false_below_band (h : Col -> Nat)
    (perm : Row -> Equiv.Perm Col) (r : Row)
    (hr : r.val < lowBoundary h) (c : Col) :
    rowScrambledUnary h perm r c = false := by
  exact bottomUnary_false_below_band h r hr (perm r c)

theorem rowScramble_true_above_band (h : Col -> Nat)
    (perm : Row -> Equiv.Perm Col) (r : Row)
    (hr : highBoundary h <= r.val) (c : Col) :
    rowScrambledUnary h perm r c = true := by
  exact bottomUnary_true_above_band h r hr (perm r c)

end Chvatal.D2TwoGridBandInterface
