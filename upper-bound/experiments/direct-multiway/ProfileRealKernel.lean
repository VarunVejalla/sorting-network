import AKS.Chvatal.FringeSendField
import AKS.Chvatal.RealKernel
import ProfileBadSendField
import ProfileStageKernel

/-! Instantiation of the profile-aware stage interface for the concrete
execution-defined Chvátal placement, conditional on the profile invariant and
the existing real-network specifications. -/

namespace Chvatal

noncomputable def realProfileStageKernel {d : Nat} (hd : 7 <= d)
    (nets : Nat -> (b : KBag 64 d) -> (n : Nat) -> ComparatorNetwork n)
    (hspecs : RealSpecs hd nets) (v : Equiv.Perm (Fin (64 ^ d)))
    (t : Nat) (ht1 : 1 <= t) (ht : t + 1 <= tf7 d)
    (hP : ProfileOutsiderBoundLe d t
      (execPlacement (flowSizes7 d hd) nets v t (by omega)) id) :
    ProfileStageKernel d t
      (execPlacement (flowSizes7 d hd) nets v t (by omega)) id
      (execPlacement (flowSizes7 d hd) nets v (t + 1) ht) := by
  let pl := execPlacement (flowSizes7 d hd) nets v t (by omega)
  let pl' := execPlacement (flowSizes7 d hd) nets v (t + 1) ht
  have hgeom : forall (b : KBag 64 d) (r : Nat), r <= d ->
      ((b.strangers (r + 1) id (pl.regs b) : Nat) : Rat) <=
        geometricProfile d t profileScale profileEffectiveDelta b r := by
    intro b r hr
    have h := hP b r hr
    simpa [pl, geometricProfile] using h
  have hbad := badSendField_profile hd nets hspecs v t ht1 ht hgeom
  have hscalar := profileOutsiderBoundLe_to_scalar hP
  have hfringe := fringeSendField_real hd nets hspecs v t ht1 ht hscalar
  refine {
    step := realPlacementStep hd nets v t ht
    hBadSend0 := ?_
    hFringeSend := ?_
    hChildrenSubset := ?_
    hChildrenLeaf := ?_
    level0 := ?_ }
  · intro b hb
    have h := hbad b hb
    convert h using 1 <;> simp [BadSendAtProfile, pl, parentOutMass,
      sibMassBound, slackBound, realPlacementStep] <;> ring
  · intro b r hr1 hrd hb
    exact hfringe b r hr1 hrd hb
  · intro b hb hbd
    exact fromChildrenK_subset (flowSizes7 d hd) nets v t (by omega) b hbd
  · intro b hb hbd
    exact fromChildrenK_of_not_lt (flowSizes7 d hd) nets v t b hbd
  · intro b r hb0 hr
    have hz : b.strangers (r + 1) id (pl'.regs b) = 0 :=
      KBag.strangers_eq_zero_of_lt_order b (r + 1) id _ (by norm_num)
        (by omega) (by omega)
    rw [hz]
    have hscale : 0 <= profileScale := by norm_num [profileScale]
    have hmu : 0 <= invMu := invMu_pos.le
    have htheta : 0 <= profileEffectiveDelta := by
      norm_num [profileEffectiveDelta, profileGamma, invDelta]
    have hcap' := capacity_pos d 0 (t + 1)
    positivity

/-- Concrete one-stage preservation for the executed sorting networks. This is
the profile analogue of `outsiderBound_step_of_kernel`, with the real BadSend
profile proof and existing fringe theorem assembled into its kernel. -/
theorem realProfileOutsiderBound_step {d : Nat} (hd : 7 <= d)
    (nets : Nat -> (b : KBag 64 d) -> (n : Nat) -> ComparatorNetwork n)
    (hspecs : RealSpecs hd nets) (v : Equiv.Perm (Fin (64 ^ d)))
    (t : Nat) (ht1 : 1 <= t) (ht : t + 1 <= tf7 d)
    (hP : ProfileOutsiderBoundLe d t
      (execPlacement (flowSizes7 d hd) nets v t (by omega)) id) :
    ProfileOutsiderBoundLe d (t + 1)
      (execPlacement (flowSizes7 d hd) nets v (t + 1) ht) id := by
  exact profileOutsiderBound_step_of_kernel d t _ _ id hP
    (realProfileStageKernel hd nets hspecs v t ht1 ht hP)

end Chvatal
