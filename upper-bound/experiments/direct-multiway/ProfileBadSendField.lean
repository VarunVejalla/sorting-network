import AKS.Chvatal.BadSendField
import ProfileKeysBelowChild
import ProfileWeights

set_option maxHeartbeats 0

/-! Scratch BadSendField specialization using the rank-profile sibling bound.
The theorem has no `OutsiderBoundLe` hypothesis: sibling control comes from
the profile directly.
-/

namespace Chvatal

open Finset
open scoped Classical

def BadSendAtProfile {d : Nat} (hd : 7 <= d)
    (nets : Nat -> (b : KBag 64 d) -> (n : Nat) -> ComparatorNetwork n)
    (v : Equiv.Perm (Fin (64 ^ d))) (t : Nat) (ht : t <= tf7 d)
    (profileSib : Rat) (b : KBag 64 d) (_hb : 1 <= b.l) : Prop :=
  ((b.strangers 1 id (fromParentK (flowSizes7 d hd) nets v t b) : Nat) : Rat) <=
    parentOutMass d (execPlacement (flowSizes7 d hd) nets v t ht) id b _hb +
      63 * profileSib * capacity d (b.l - 1) t +
      invEpsB * capacity d (b.l - 1) t +
      slackBound d t b _hb

theorem hM_keys_profile {d : Nat} (hd : 7 <= d)
    (nets : Nat -> (b : KBag 64 d) -> (n : Nat) -> ComparatorNetwork n)
    (v : Equiv.Perm (Fin (64 ^ d))) (t : Nat)
    (ht2 : 2 <= t) (htt : t <= tf7 d)
    (hprof : forall (b : KBag 64 d) (r : Nat), r <= d ->
      ((b.strangers (r + 1) id
        ((execPlacement (flowSizes7 d hd) nets v t htt).regs b) : Nat) : Rat) <=
          geometricProfile d t profileScale profileEffectiveDelta b r)
    (q : KBag 64 d) (hq : q.l < d)
    (hα : alpha7 d t <= q.l) (hω : q.l < omega7 d t)
    (j : Fin 64) (hpar : q.l % 2 = t % 2) :
    ((((execPlacement (flowSizes7 d hd) nets v t htt).regs q).filter fun k =>
      (q.child j.val j.isLt hq).Native k id).card : Rat) <=
        capacity d q.l t / 64 +
          profileScale * invMu * profileSiblingFactor profileEffectiveDelta *
            capacity d q.l t := by
  have hkey := keys_below_child_profile (d := d) t
    (execPlacement (flowSizes7 d hd) nets v t htt)
    (fun l => (flowSizes7 d hd).a l t)
    (fun b => execPlacement_card _ nets v t htt b)
    (geometricProfile d t profileScale profileEffectiveDelta)
    (fun b r hr => hprof b r hr) q hq j
    (hwires7 d hd t ht2 htt q.l hα hω hpar)
  have hwpar : (q.child j.val j.isLt hq).l % 2 ≠ t % 2 := by
    change (q.l + 1) % 2 ≠ t % 2
    omega
  have hwpos : 1 <= (q.child j.val j.isLt hq).l := by
    change 1 <= q.l + 1
    omega
  have hsib := profileBadMass_geometric_le (d := d) t
    (fun l => (flowSizes7 d hd).a l t)
    (hpar7 d hd t (by omega) (by omega))
    profileScale profileEffectiveDelta (by norm_num [profileScale])
    (by norm_num [profileEffectiveDelta, profileGamma, invDelta])
    (by norm_num [profileEffectiveDelta, profileGamma, invDelta])
    (q.child j.val j.isLt hq) hwpar hwpos
  have hsib' : profileBadMass (geometricProfile d t profileScale profileEffectiveDelta)
      (fun l => (flowSizes7 d hd).a l t) (q.child j.val j.isLt hq) <=
        profileScale * invMu * profileSiblingFactor profileEffectiveDelta * capacity d q.l t := by
    simpa [show (q.child j.val j.isLt hq).l - 1 = q.l from rfl] using hsib
  calc
    _ <= capacity d q.l t / 64 +
          profileBadMass (geometricProfile d t profileScale profileEffectiveDelta)
            (fun l => (flowSizes7 d hd).a l t) (q.child j.val j.isLt hq) := hkey
    _ <= capacity d q.l t / 64 +
          profileScale * invMu * profileSiblingFactor profileEffectiveDelta *
            capacity d q.l t := by linarith [hsib']

/-- Profile version of the real-network BadSendField. The geometric stranger
profile supplies the sibling estimate directly. -/
theorem badSendField_profile {d : Nat} (hd : 7 <= d)
    (nets : Nat -> (b : KBag 64 d) -> (n : Nat) -> ComparatorNetwork n)
    (hspecs : RealSpecs hd nets) (v : Equiv.Perm (Fin (64 ^ d))) (t : Nat)
    (ht1 : 1 <= t) (ht : t + 1 <= tf7 d)
    (hprof : forall (b : KBag 64 d) (r : Nat), r <= d ->
      ((b.strangers (r + 1) id
        ((execPlacement (flowSizes7 d hd) nets v t (by omega)).regs b) : Nat) : Rat) <=
          geometricProfile d t profileScale profileEffectiveDelta b r) :
    forall b : KBag 64 d, (hb : 1 <= b.l) ->
      BadSendAtProfile hd nets v t (by omega)
        (profileScale * invMu * profileSiblingFactor profileEffectiveDelta)
        b hb := by
  intro b hb
  obtain ⟨q, hqlt, j, rfl⟩ := exists_parent_child b hb
  have htt : t < tf7 d := by omega
  have hsib0 : 0 <= profileScale * invMu * profileSiblingFactor profileEffectiveDelta := by
    unfold profileSiblingFactor
    have hden : 0 < 1 - (64 * 4096 * profileEffectiveDelta) ^ 2 := by
      norm_num [profileEffectiveDelta, profileGamma, invDelta]
    have htheta' : 0 <= profileEffectiveDelta := by
      norm_num [profileEffectiveDelta, profileGamma, invDelta]
    have hx : 0 <= (64 : Rat) * 4096 * profileEffectiveDelta := by
      positivity
    have hfac : 0 <= 4096 *
        ((64 * 4096 * profileEffectiveDelta) /
          (1 - (64 * 4096 * profileEffectiveDelta) ^ 2)) :=
      mul_nonneg (by norm_num) (div_nonneg hx hden.le)
    exact mul_nonneg (mul_nonneg (by norm_num [profileScale]) invMu_pos.le) hfac
  have hm0 := mul_nonneg hsib0 (capacity_nonneg d q.l t)
  by_cases hd0 : (flowSizes7 d hd).down q.l t = 0
  · have hemp := fromParentK_eq_empty hd nets v t (q.child j.val j.isLt hqlt) hd0
    have := invEpsB_nonneg
    have := slackCoeff_nonneg
    have := capacity_nonneg d ((q.child j.val j.isLt hqlt).l - 1) t
    unfold BadSendAtProfile parentOutMass slackBound
    rw [hemp]
    simp [KBag.strangers]
    positivity
  obtain ⟨Δ, hF, -, hMs⟩ := node_facts d hd t q.l ht1 htt (Nat.pos_of_ne_zero hd0)
  let rho : Rat := profileScale * invMu * profileSiblingFactor profileEffectiveDelta *
    capacity d q.l t
  have hrho : 0 <= rho := hm0
  have hM : ∀ j' : Fin 64,
      ((((execPlacement (flowSizes7 d hd) nets v t (by omega)).regs q).filter fun k =>
        (q.child j'.val j'.isLt hqlt).Native k id).card : Rat) <=
          ((flowSizes7 d hd).down q.l t : Rat) + (Δ + rho) := by
    intro j'
    rcases hMs with ⟨⟨ht2', hα, hω, hpar⟩, h⟩ | h
    · have hk' := hM_keys_profile hd nets v t ht2' htt.le hprof q hqlt hα hω j' hpar
      linarith [hk', h]
    · have hk' := hM_pow hd nets v t htt.le q hqlt j'
      have hpow : ((64 : Nat) ^ (d - q.l - 1) : Nat) <=
          (flowSizes7 d hd).down q.l t + Δ := by exact_mod_cast h
      have hrho' : (0 : Rat) <= rho := hrho
      have hΔ : 0 <= Δ := hF.nonneg
      linarith [hk', hpow]
  have hbad := bad_send0_real (flowSizes7 d hd) nets v t htt q hqlt j
    (specEB t ((flowSizes7 d hd).a q.l t)) (specJmax ((flowSizes7 d hd).up q.l t)) eps
    ((Δ + rho : Rat) : Real)
    (by exact_mod_cast add_nonneg hF.nonneg hrho)
    (hspecs t q htt (Nat.pos_of_ne_zero hd0))
    (fun j' => by exact_mod_cast (Rat.cast_le (K := Real)).mpr (hM j'))
    (by
      have hhalf := (Rat.cast_le (K := Real)).mpr
        (show ((flowSizes7 d hd).up q.l t : Rat) / 2 <=
          (q.strangers 1 id ((execPlacement (flowSizes7 d hd) nets v t (by omega)).regs q) : Rat) +
            63 * (Δ + rho) by linarith [hF.half])
      push_cast at hhalf
      push_cast
      exact hhalf)
  have hslR : 63 * (Δ + rho) - ((flowSizes7 d hd).up q.l t : Rat) / 2 <=
      63 * rho + slackCoeff * capacity d q.l t := by
    linarith [hF.slack]
  have hslRreal :
      (((63 * (Δ + rho) - ((flowSizes7 d hd).up q.l t : Rat) / 2 : Rat) : Real) <=
        ((63 * rho + slackCoeff * capacity d q.l t : Rat) : Real)) := by
    exact_mod_cast hslR
  push_cast at hslRreal
  push_cast at hslR hbad
  have hEB : 2 * specEB t ((flowSizes7 d hd).a q.l t) <=
      (1 / 59000000 : Real) * ((capacity d q.l t : Rat) : Real) := by
    unfold specEB
    rw [if_neg (by omega)]
    have h1 := paperOrdinaryEpsB_le
    have h2 : (0 : Real) <= (((flowSizes7 d hd).a q.l t : Nat) : Real) := Nat.cast_nonneg _
    have hael : (((flowSizes7 d hd).a q.l t : Nat) : Real) <=
        ((capacity d q.l t : Rat) : Real) := by exact_mod_cast hF.a_le
    nlinarith
  have e2 : (q.child j.val j.isLt hqlt).parent = q := KBag.parent_child' q j.val j.isLt hqlt
  unfold BadSendAtProfile parentOutMass slackBound
  rw [← Rat.cast_le (K := Real)]
  simp only [show (q.child j.val j.isLt hqlt).l - 1 = q.l from rfl, e2]
  push_cast
  have hepsB : ((invEpsB : Rat) : Real) = 1 / 59000000 := by simp [invEpsB]
  rw [hepsB]
  refine le_trans hbad ?_
  change _ <= (((q.strangers 1 id ((execPlacement (flowSizes7 d hd) nets v t (by omega)).regs q)
    : Nat) : Real)) + _ + _ + _
  have hrhoCast : ((rho : Rat) : Real) =
      (profileScale : Real) * invMu * profileSiblingFactor profileEffectiveDelta *
        (capacity d q.l t : Real) := by simp [rho]
  linarith [hslRreal, hEB, hrhoCast]

end Chvatal
