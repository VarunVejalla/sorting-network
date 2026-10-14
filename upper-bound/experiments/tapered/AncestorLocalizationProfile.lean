import OutsiderSlotMass
import NativeChildrenPartition
import Mathlib.Tactic

/-!
The all-order stranger invariant controls keys outside an ancestor's native
interval. It says nothing about how keys *inside* that interval are split among
deeper native intervals. This file makes that missing profile explicit.
-/
namespace Tapered945

open Chvatal

/-- A hierarchical localization profile: for every descendant interval `q`,
bound how much of each ancestor register lies in that interval. A useful
instance should make `bound q r` decay with the distance `r`; the current
outsider invariant does not supply this field. -/
def AncestorLocalizationProfile {d : Nat}
    (pl : Placement 64 d) (perm : Fin (64 ^ d) → Fin (64 ^ d))
    (bound : KBag 64 d → Nat → Nat) : Prop :=
  ∀ (q : KBag 64 d) (r : Nat), r ≤ q.l →
    (((pl.regs (q.ancestor r)).image perm) ∩ nativeKeys q).card ≤ bound q r

/-- Once the ancestor profile is proved, it bounds the ancestor's mass in any
prefix or other subregion of the descendant's native interval. -/
theorem ancestor_localized_subregion_bound {d : Nat}
    (pl : Placement 64 d) (perm : Fin (64 ^ d) → Fin (64 ^ d))
    (bound : KBag 64 d → Nat → Nat)
    (hprofile : AncestorLocalizationProfile pl perm bound)
    (q : KBag 64 d) (r : Nat) (hr : r ≤ q.l)
    (I : Finset (Fin (64 ^ d))) (hI : I ⊆ nativeKeys q) :
    (((pl.regs (q.ancestor r)).image perm) ∩ I).card ≤ bound q r := by
  apply le_trans (Finset.card_le_card ?_)
  · exact hprofile q r hr
  · intro x hx
    exact Finset.mem_inter.mpr
      ⟨(Finset.mem_inter.mp hx).1, hI (Finset.mem_inter.mp hx).2⟩

/-- The order-one stranger test is completely blind to concentration inside a
bag's native interval: every subset of that interval has zero strangers.
This is why a localization profile has to be an additional invariant. -/
theorem native_subset_order_one_strangers_zero {d : Nat}
    (q : KBag 64 d) (S : Finset (Fin (64 ^ d)))
    (hS : S ⊆ nativeKeys q) :
    q.strangers 1 id S = 0 := by
  rw [strangers_one_image_eq q id (fun _ _ h => h) S]
  have hempty : S.filter (fun k => ¬ q.Native k id) = ∅ :=
    Finset.filter_eq_empty_iff.mpr (fun k hk hbad =>
      hbad (Finset.mem_filter.mp (hS hk)).2)
  simpa [Finset.image_id, hempty]

end Tapered945
