import TaperedOrdinaryKernel
import RaggedStageOneRank
import Mathlib.Tactic

namespace Tapered945

open Chvatal

theorem card_filter_injective_image {α : Type*} [DecidableEq α]
    (S : Finset α) (f : α → Nat) (hf : Function.Injective f)
    (P : Nat → Prop) [DecidablePred P] :
    ((S.image f).filter P).card = (S.filter (fun x => P (f x))).card := by
  have hset : (S.image f).filter P = (S.filter (fun x => P (f x))).image f := by
    ext y
    simp only [Finset.mem_filter, Finset.mem_image]
    constructor
    · rintro ⟨⟨x, hx, rfl⟩, hP⟩
      exact ⟨x, ⟨hx, hP⟩, rfl⟩
    · rintro ⟨x, ⟨hx, hP⟩, rfl⟩
      exact ⟨⟨x, hx, rfl⟩, hP⟩
  rw [hset, Finset.card_image_of_injective _ hf]

/-- The all-order outsider invariant supplies the two tails outside an
active bag's own native interval, for the actual key permutation on wires. -/
theorem invariant_native_external_tails {d t : Nat}
    (pl : Placement 64 d) (perm : Fin (64 ^ d) → Fin (64 ^ d))
    (hP : TaperedOutsiderBoundLe d t pl perm)
    (q : KBag 64 d) :
    ((pl.regs q).filter (fun κ => (perm κ).val < q.lo)).card ≤
        mu * delta ^ 0 * candidateReferenceCapacity d q.l t ∧
    ((pl.regs q).filter (fun κ => q.hi ≤ (perm κ).val)).card ≤
        mu * delta ^ 0 * candidateReferenceCapacity d q.l t := by
  have hstrEq : q.strangers 1 perm (pl.regs q) =
      ((pl.regs q).filter (fun κ =>
        ¬ (q.lo ≤ (perm κ).val ∧ (perm κ).val < q.hi))).card := by
    unfold KBag.strangers
    congr 1
    apply Finset.filter_congr
    intro κ _
    simp [KBag.Strange, Chvatal.ancestor_zero_eq, KBag.native_iff]
  have hbound := hP q 0 (by omega)
  rw [hstrEq] at hbound
  have hleft : ((pl.regs q).filter (fun κ => (perm κ).val < q.lo)).card ≤
      q.strangers 1 perm (pl.regs q) := by
    apply Finset.card_le_card
    intro κ hκ
    simp only [Finset.mem_filter] at hκ ⊢
    refine ⟨hκ.1, ?_⟩
    change 1 = 0 ∨ ¬ (q.ancestor (1 - 1) (by norm_num)).Native κ perm
    simp only [Nat.one_ne_zero, false_or, Nat.sub_self]
    rw [Chvatal.ancestor_zero_eq]
    intro hn
    have hrange := (KBag.native_iff q κ perm (by norm_num)).mp hn
    omega
  have hright : ((pl.regs q).filter (fun κ => q.hi ≤ (perm κ).val)).card ≤
      q.strangers 1 perm (pl.regs q) := by
    apply Finset.card_le_card
    intro κ hκ
    simp only [Finset.mem_filter] at hκ ⊢
    refine ⟨hκ.1, ?_⟩
    change 1 = 0 ∨ ¬ (q.ancestor (1 - 1) (by norm_num)).Native κ perm
    simp only [Nat.one_ne_zero, false_or, Nat.sub_self]
    rw [Chvatal.ancestor_zero_eq]
    intro hn
    have hrange := (KBag.native_iff q κ perm (by norm_num)).mp hn
    omega
  constructor
  · have hcast : ((((pl.regs q).filter (fun κ => (perm κ).val < q.lo)).card : Rat)) ≤
        q.strangers 1 perm (pl.regs q) := by exact_mod_cast hleft
    rw [hstrEq] at hcast
    exact hcast.trans hbound
  · have hcast : ((((pl.regs q).filter (fun κ => q.hi ≤ (perm κ).val)).card : Rat)) ≤
        q.strangers 1 perm (pl.regs q) := by exact_mod_cast hright
    rw [hstrEq] at hcast
    exact hcast.trans hbound

/-- Extend the invariant's native-interval tails to arbitrary internal cuts.
The added terms are exactly the numbers of possible key values between the
native boundary and the requested cut. -/
theorem invariant_internal_cut_tails {d t : Nat}
    (pl : Placement 64 d) (perm : Fin (64 ^ d) → Fin (64 ^ d))
    (hperm : Function.Injective perm)
    (hP : TaperedOutsiderBoundLe d t pl perm)
    (q : KBag 64 d) (lo hi : Nat)
    (hlo : q.lo ≤ lo) (hhi : hi ≤ q.hi) :
    ((pl.regs q).filter (fun κ => (perm κ).val < lo)).card ≤
        (mu * delta ^ 0 * candidateReferenceCapacity d q.l t) + (lo - q.lo) ∧
    ((pl.regs q).filter (fun κ => hi ≤ (perm κ).val)).card ≤
        (mu * delta ^ 0 * candidateReferenceCapacity d q.l t) + (q.hi - hi) := by
  let K := (pl.regs q).image (fun κ => (perm κ).val)
  have hleft := (invariant_native_external_tails pl perm hP q).1
  have hright := (invariant_native_external_tails pl perm hP q).2
  have hvalInj : Function.Injective (fun κ : Fin (64 ^ d) => (perm κ).val) :=
    Fin.val_injective.comp hperm
  have hleftCast : ((K.filter (· < q.lo)).card : Rat) ≤
      mu * delta ^ 0 * candidateReferenceCapacity d q.l t := by
    change ((((pl.regs q).image (fun κ => (perm κ).val)).filter (· < q.lo)).card : Rat) ≤ _
    rw [card_filter_injective_image _ _ hvalInj]
    exact hleft
  have hrightCast : ((K.filter (q.hi ≤ ·)).card : Rat) ≤
      mu * delta ^ 0 * candidateReferenceCapacity d q.l t := by
    change ((((pl.regs q).image (fun κ => (perm κ).val)).filter (q.hi ≤ ·)).card : Rat) ≤ _
    rw [card_filter_injective_image _ _ hvalInj]
    exact hright
  have hleftNat := Chvatal.BW.prefix_count_le_of_cut K q.lo lo hlo
  have hrightNat := Chvatal.BW.suffix_count_le_of_cut K hi q.hi hhi
  have hleftCut : ((K.filter (· < lo)).card : Rat) ≤
      (mu * delta ^ 0 * candidateReferenceCapacity d q.l t) + (lo - q.lo) := by
    have hcast : ((K.filter (· < lo)).card : Rat) ≤
        ((K.filter (· < q.lo)).card : Rat) + (lo - q.lo : Nat) := by
      exact_mod_cast hleftNat
    have hnat : ((lo - q.lo : Nat) : Rat) = (lo : Rat) - q.lo := Nat.cast_sub hlo
    rw [hnat] at hcast
    linarith [hleftCast]
  have hrightCut : ((K.filter (hi ≤ ·)).card : Rat) ≤
      (mu * delta ^ 0 * candidateReferenceCapacity d q.l t) + (q.hi - hi) := by
    have hcastNat : (K.filter (hi ≤ ·)).card ≤
        (K.filter (q.hi ≤ ·)).card + (q.hi - hi) := by
      calc
        (K.filter (hi ≤ ·)).card ≤ (q.hi - hi) + (K.filter (q.hi ≤ ·)).card := hrightNat
        _ = (K.filter (q.hi ≤ ·)).card + (q.hi - hi) := Nat.add_comm _ _
    have hcastR : ((K.filter (hi ≤ ·)).card : Rat) ≤
        ((K.filter (q.hi ≤ ·)).card : Rat) + (q.hi - hi : Nat) := by
      exact_mod_cast hcastNat
    have hnat : ((q.hi - hi : Nat) : Rat) = (q.hi : Rat) - hi := Nat.cast_sub hhi
    rw [hnat] at hcastR
    linarith [hrightCast]
  constructor
  · change (((pl.regs q).filter (fun κ => (perm κ).val < lo)).card : Rat) ≤ _
    have himage := card_filter_injective_image (pl.regs q)
      (fun κ => (perm κ).val) hvalInj (· < lo)
    rw [← himage]
    exact hleftCut
  · change (((pl.regs q).filter (fun κ => hi ≤ (perm κ).val)).card : Rat) ≤ _
    have himage := card_filter_injective_image (pl.regs q)
      (fun κ => (perm κ).val) hvalInj (hi ≤ ·)
    rw [← himage]
    exact hrightCut

end Tapered945
