import SlotOutputBridge
import AKS.Chvatal.NodeKeys

namespace Tapered945
open Chvatal

/-- Executing a comparator network preserves its set of actual natural key labels. -/
theorem exec_nat_keyset {a M : Nat} (net : ComparatorNetwork a) (xr : Fin a → Fin M) :
    Finset.univ.image (fun c => (net.exec xr c).val) = (keySet xr).image Fin.val := by
  obtain ⟨ρ, hρ⟩ := ComparatorNetwork.exec_eq_comp_perm net xr
  rw [hρ]
  simp only [keySet, Finset.image_image]
  ext κ
  simp only [Finset.mem_image, Finset.mem_univ, true_and, Function.comp_apply]
  constructor
  · rintro ⟨c, hc⟩
    exact ⟨ρ c, hc⟩
  · rintro ⟨c, hc⟩
    exact ⟨ρ.symm c, by simpa using hc⟩

/-- Normalized network output ranks are the natural-key ranks of actual output keys. -/
theorem exec_rankPerm_nat {a M : Nat} {xr : Fin a → Fin M}
    (hxr : Function.Injective xr) (net : ComparatorNetwork a) (c : Fin a) :
    (net.exec (rankPerm hxr : Fin a → Fin a) c).val =
      BW.rankN ((keySet xr).image Fin.val) (net.exec xr c).val := by
  rw [rankN_val]
  exact exec_rankPerm hxr net c

/-- Actual execution bridge: ideal-rank input errors plus two normalized
boundary-crossing errors bound the wrong actual keys in an output slot. -/
theorem separator_output_wrong_keys_le {a M : Nat}
    (net : ComparatorNetwork a) (xr : Fin a → Fin M) (hxr : Function.Injective xr)
    (L H lo hi : Nat) (A EL EH : Real)
    (hA : ((((keySet xr).image Fin.val).filter (fun κ =>
      L ≤ BW.rankN ((keySet xr).image Fin.val) κ ∧
      BW.rankN ((keySet xr).image Fin.val) κ < H ∧ ¬ (lo ≤ κ ∧ κ < hi))).card : Real) ≤ A)
    (hL : ((Finset.univ.filter (fun c : Fin a =>
      (net.exec (rankPerm hxr : Fin a → Fin a) c).val < L ∧ L ≤ c.val)).card : Real) ≤ EL)
    (hH : ((Finset.univ.filter (fun c : Fin a =>
      H ≤ (net.exec (rankPerm hxr : Fin a → Fin a) c).val ∧ c.val < H)).card : Real) ≤ EH) :
    ((((Finset.univ.filter (fun c : Fin a => L ≤ c.val ∧ c.val < H)).image
      (fun c => (net.exec xr c).val)).filter (fun κ => ¬ (lo ≤ κ ∧ κ < hi))).card : Real) ≤
      A + EL + EH := by
  let k : Fin a → Nat := fun c => (net.exec xr c).val
  let r : Fin a → Nat := fun c => (net.exec (rankPerm hxr : Fin a → Fin a) c).val
  have hk : Function.Injective k := Fin.val_injective.comp (exec_keySet_injective hxr net)
  have hkeys : Finset.univ.image k = (keySet xr).image Fin.val := exec_nat_keyset net xr
  have hr : ∀ c, r c = BW.rankN (Finset.univ.image k) (k c) := by
    intro c
    rw [hkeys]
    exact exec_rankPerm_nat hxr net c
  have hc := ideal_rank_bad_card_eq_keys a L H lo hi k hk r hr
  rw [hkeys] at hc
  have hideal : ((Finset.univ.filter (fun c : Fin a =>
      L ≤ r c ∧ r c < H ∧ ¬ (lo ≤ k c ∧ k c < hi))).card : Real) ≤ A := by
    rw [hc]
    exact hA
  have hout := output_slot_bad_le_real a L H r (fun c => ¬ (lo ≤ k c ∧ k c < hi))
    A EL EH hideal hL hH
  rw [Finset.filter_image, Finset.card_image_of_injective _ hk, Finset.filter_filter]
  simpa only [k, and_assoc] using hout

end Tapered945
