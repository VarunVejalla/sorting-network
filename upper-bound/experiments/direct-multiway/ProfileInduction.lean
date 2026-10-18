import ProfileInitial
import ProfileRealKernel

/-! Full stage induction for the scratch geometric outsider profile. -/

namespace Chvatal

/-- The proposed rank profile holds at every scheduled placement, assuming the
same local network specifications as the existing Chvátal induction. -/
theorem Profile_P_all {d : Nat} (hd : 7 <= d)
    (nets : Nat -> (b : KBag 64 d) -> (n : Nat) -> ComparatorNetwork n)
    (hspecs : RealSpecs hd nets) (v : Equiv.Perm (Fin (64 ^ d))) :
    ∀ t, 1 <= t -> ∀ (ht : t <= tf7 d),
      ProfileOutsiderBoundLe d t
        (execPlacement (flowSizes7 d hd) nets v t ht) id := by
  intro t ht1
  induction t, ht1 using Nat.le_induction with
  | base =>
      intro ht
      exact Profile_P_one hd nets hspecs v
  | succ t ht1 ih =>
      intro ht
      have ht' : t <= tf7 d := by omega
      exact realProfileOutsiderBound_step hd nets hspecs v t ht1 (by omega) (ih ht')

end Chvatal
