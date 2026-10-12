import TruncatedFringeProvider
import PaddedSeparator
import BaselineFringe
import AKS.Chvatal.PackNodeSpec2

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

end Tapered945
