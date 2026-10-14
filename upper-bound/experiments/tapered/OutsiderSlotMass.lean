import TaperedOrdinaryKernel
import RaggedTreeMassInstantiation
import AKS.Chvatal.BadSendReal
import Mathlib.Tactic

namespace Tapered945

open Chvatal

/-- Reindexing by the current key permutation turns order-one strangers into
keys outside the bag's native key set. -/
theorem strangers_one_image_eq {d : Nat} (q : KBag 64 d)
    (perm : Fin (64 ^ d) → Fin (64 ^ d))
    (hperm : Function.Injective perm) (K : Finset (Fin (64 ^ d))) :
    q.strangers 1 perm K =
      ((K.image perm).filter (fun k => ¬ q.Native k id)).card := by
  unfold KBag.strangers
  have hpred (w : Fin (64 ^ d)) :
      q.Strange 1 w perm (by norm_num) ↔ ¬ q.Native (perm w) id := by
    change 1 = 0 ∨ ¬ (q.ancestor 0 (by norm_num)).Native w perm ↔ _
    rw [Chvatal.ancestor_zero_eq q]
    simp only [Nat.one_ne_zero, false_or]
    rfl
  have hset :
      (K.filter (fun w => q.Strange 1 w perm (by norm_num))).image perm =
        (K.image perm).filter (fun k => ¬ q.Native k id) := by
    ext k
    simp only [Finset.mem_image, Finset.mem_filter]
    constructor
    · rintro ⟨w, ⟨hwK, hstr⟩, hEq⟩
      subst k
      exact ⟨⟨w, hwK, rfl⟩, (hpred w).mp hstr⟩
    · rintro ⟨⟨w, hwK, hEq⟩, hnot⟩
      rw [← hEq] at hnot
      exact ⟨w, ⟨hwK, (hpred w).mpr hnot⟩, hEq⟩
  rw [← Finset.card_image_of_injective _ hperm, hset]

/-- The all-order invariant bounds the non-native keys in any subset of a
bag's register. The explicit natural error allowance is useful for summing
these estimates over child slots. -/
theorem outsider_slot_error_bound {d t : Nat}
    (pl : Placement 64 d) (perm : Fin (64 ^ d) → Fin (64 ^ d))
    (hperm : Function.Injective perm)
    (hP : TaperedOutsiderBoundLe d t pl perm)
    (q : KBag 64 d) (K : Finset (Fin (64 ^ d))) (err : Nat)
    (hK : K ⊆ pl.regs q)
    (herr : mu * candidateReferenceCapacity d q.l t ≤ err) :
    ((K.image perm).filter (fun k => ¬ q.Native k id)).card ≤ err := by
  have hmono := q.strangers_mono 1 perm hK
  have hPq := hP q 0 (by omega)
  have hmonoR : ((q.strangers 1 perm K : Nat) : Rat) ≤
      ((q.strangers 1 perm (pl.regs q) : Nat) : Rat) := by
    exact_mod_cast hmono
  have hreal : ((q.strangers 1 perm K : Nat) : Rat) ≤
      mu * delta ^ 0 * candidateReferenceCapacity d q.l t := by
    exact hmonoR.trans hPq
  rw [strangers_one_image_eq q perm hperm K] at hreal
  have hreal' :
      (((K.image perm).filter (fun k => ¬ q.Native k id)).card : Rat) ≤
        mu * candidateReferenceCapacity d q.l t := by
    norm_num [delta] at hreal
    exact hreal
  have herrR : mu * candidateReferenceCapacity d q.l t ≤ (err : Rat) := herr
  have hfinal := hreal'.trans herrR
  exact_mod_cast hfinal

/-- The higher-order version: order `r+1` strangers are exactly the keys
outside the native interval of the `r`-ancestor. -/
theorem strangers_ancestor_image_eq {d : Nat} (q : KBag 64 d)
    (perm : Fin (64 ^ d) → Fin (64 ^ d))
    (hperm : Function.Injective perm) (r : Nat)
    (K : Finset (Fin (64 ^ d))) :
    q.strangers (r + 1) perm K =
      ((K.image perm).filter
        (fun k => ¬ (q.ancestor r).Native k id)).card := by
  unfold KBag.strangers
  have hpred (w : Fin (64 ^ d)) :
      q.Strange (r + 1) w perm (by norm_num) ↔
        ¬ (q.ancestor r).Native (perm w) id := by
    change r + 1 = 0 ∨
      ¬ (q.ancestor ((r + 1) - 1) (by norm_num)).Native w perm ↔ _
    have hr : (r + 1) - 1 = r := by omega
    rw [hr]
    simp only [show r + 1 ≠ 0 by omega, false_or]
    rfl
  have hset :
      (K.filter (fun w => q.Strange (r + 1) w perm (by norm_num))).image perm =
        (K.image perm).filter
          (fun k => ¬ (q.ancestor r).Native k id) := by
    ext k
    simp only [Finset.mem_image, Finset.mem_filter]
    constructor
    · rintro ⟨w, ⟨hwK, hstr⟩, hEq⟩
      subst k
      exact ⟨⟨w, hwK, rfl⟩, (hpred w).mp hstr⟩
    · rintro ⟨⟨w, hwK, hEq⟩, hnot⟩
      rw [← hEq] at hnot
      exact ⟨w, ⟨hwK, (hpred w).mpr hnot⟩, hEq⟩
  rw [← Finset.card_image_of_injective _ hperm, hset]

/-- A subset of a register contributes at most the invariant allowance to any
event contained in its higher-order stranger set. -/
theorem stranger_slot_error_bound {d t : Nat}
    (pl : Placement 64 d) (perm : Fin (64 ^ d) → Fin (64 ^ d))
    (hperm : Function.Injective perm)
    (hP : TaperedOutsiderBoundLe d t pl perm)
    (q : KBag 64 d) (r : Nat) (hr : r ≤ d)
    (K : Finset (Fin (64 ^ d))) (err : Nat)
    (hK : K ⊆ pl.regs q)
    (herr : mu * delta ^ r * candidateReferenceCapacity d q.l t ≤ err)
    (hbad : ∀ w ∈ K, q.Strange (r + 1) w perm (by norm_num)) :
    (K.image perm).card ≤ err := by
  have hmono := q.strangers_mono (r + 1) perm hK
  have hPq := hP q r hr
  have hmonoR : ((q.strangers (r + 1) perm K : Nat) : Rat) ≤
      ((q.strangers (r + 1) perm (pl.regs q) : Nat) : Rat) := by
    exact_mod_cast hmono
  have hreal : ((q.strangers (r + 1) perm K : Nat) : Rat) ≤
      mu * delta ^ r * candidateReferenceCapacity d q.l t := hmonoR.trans hPq
  have hbadSub : K.filter (fun w => q.Strange (r + 1) w perm (by norm_num)) = K := by
    ext w
    simp only [Finset.mem_filter]
    constructor
    · exact And.left
    · intro hw
      exact ⟨hw, hbad w hw⟩
  have hstrK : q.strangers (r + 1) perm K = K.card := by
    unfold KBag.strangers
    rw [hbadSub]
  have hcardReal : (K.card : Rat) ≤
      mu * delta ^ r * candidateReferenceCapacity d q.l t := by
    simpa [hstrK] using hreal
  have herrR : mu * delta ^ r * candidateReferenceCapacity d q.l t ≤ (err : Rat) := herr
  have hfinal := hcardReal.trans herrR
  rw [Finset.card_image_of_injective _ hperm]
  exact_mod_cast hfinal

/-- For any selected family of disjoint native regions, P(t) supplies the
slot-error hypotheses needed to lower-bound the amount of that native mass
already stored in a descendant set. Prefix families are handled by choosing
`J` to be the corresponding initial address segment. -/
theorem outsider_selected_native_mass_lower
    {d t : Nat} (pl : Placement 64 d)
    (perm : Fin (64 ^ d) → Fin (64 ^ d))
    (hperm : Function.Injective perm)
    (hP : TaperedOutsiderBoundLe d t pl perm)
    (J : Finset (Fin 64)) (I S : Finset (Fin (64 ^ d)))
    (bags : Fin 64 → KBag 64 d)
    (slots : Fin 64 → Finset (Fin (64 ^ d)))
    (width err : Fin 64 → Nat)
    (hcover : J.biUnion (fun j => nativeKeys (bags j)) = I)
    (hdisj : ∀ i ∈ J, ∀ j ∈ J, i ≠ j →
      Disjoint (nativeKeys (bags i)) (nativeKeys (bags j)))
    (hslotS : ∀ j, slots j ⊆ S)
    (hslotBag : ∀ j, slots j ⊆ pl.regs (bags j))
    (hwidth : ∀ j, (slots j).card = width j)
    (herr : ∀ j,
      mu * candidateReferenceCapacity d (bags j).l t ≤ err j) :
    (∑ j ∈ J, (width j - err j)) ≤
      ((S.image perm) ∩ I).card := by
  let slots' : Fin 64 → Finset (Fin (64 ^ d)) := fun j => (slots j).image perm
  have hslotS' : ∀ j, slots' j ⊆ S.image perm := by
    intro j
    exact Finset.image_subset_image (hslotS j)
  have hwidth' : ∀ j, (slots' j).card = width j := by
    intro j
    change ((slots j).image perm).card = width j
    rw [Finset.card_image_of_injective _ hperm, hwidth j]
  have hbad' : ∀ j,
      ((slots' j).filter (fun k => k ∉ nativeKeys (bags j))).card ≤ err j := by
    intro j
    simpa [slots', nativeKeys] using outsider_slot_error_bound pl perm hperm hP
      (bags j) (slots j) (err j) (hslotBag j) (herr j)
  exact descendant_native_mass_lower_of_slot_errors J I (S.image perm)
    slots' (fun j => nativeKeys (bags j)) width err hcover hdisj hslotS'
    hwidth' hbad'

/-- Instantiate the child native-mass lower bound directly from the global
all-order outsider invariant. The routed slot/ownership facts and integer
allowances remain explicit schedule premises. -/
theorem outsider_child_native_mass_lower
    {d t : Nat} (pl : Placement 64 d)
    (perm : Fin (64 ^ d) → Fin (64 ^ d))
    (hperm : Function.Injective perm)
    (hP : TaperedOutsiderBoundLe d t pl perm)
    (q : KBag 64 d) (hq : q.l < d)
    (S : Finset (Fin (64 ^ d)))
    (slots : Fin 64 → Finset (Fin (64 ^ d)))
    (width err : Fin 64 → Nat)
    (hslotS : ∀ j, slots j ⊆ S)
    (hslotChild : ∀ j,
      slots j ⊆ pl.regs (q.child j.val j.isLt hq))
    (hwidth : ∀ j, (slots j).card = width j)
    (herr : ∀ j,
      mu * candidateReferenceCapacity d
        (q.child j.val j.isLt hq).l t ≤ err j) :
    (∑ j : Fin 64, (width j - err j)) ≤
      ((S.image perm) ∩ nativeKeys q).card := by
  let slots' : Fin 64 → Finset (Fin (64 ^ d)) := fun j => (slots j).image perm
  have hslotS' : ∀ j, slots' j ⊆ S.image perm := by
    intro j
    exact Finset.image_subset_image (hslotS j)
  have hwidth' : ∀ j, (slots' j).card = width j := by
    intro j
    change ((slots j).image perm).card = width j
    rw [Finset.card_image_of_injective _ hperm, hwidth j]
  have hbad' : ∀ j,
      ((slots' j).filter
        (fun k => k ∉ nativeKeys (q.child j.val j.isLt hq))).card ≤ err j := by
    intro j
    have h := outsider_slot_error_bound pl perm hperm hP
      (q.child j.val j.isLt hq) (slots j) (err j) (hslotChild j) (herr j)
    simpa [slots', nativeKeys, Finset.mem_filter, KBag.Native] using h
  exact native_child_mass_lower_of_slot_errors q hq (S.image perm)
    slots' width err hslotS' hwidth' hbad'

end Tapered945
