import AKS.Chvatal.Lemma41Real
import ProfileSibling

/-! A profile-sensitive version of the one-child count in Lemma 4.1.
Unlike the promoted theorem, its sibling term is not collapsed using
`OutsiderBoundLe`; it remains the exact finite profile sum over descendants.
-/

namespace Chvatal

open Finset
open scoped Classical

def profileBadMass {d : Nat} (profile : KBag 64 d -> Nat -> Rat)
    (a : Nat -> Nat) (w : KBag 64 d) : Rat :=
  Finset.sum (Finset.range (d - w.l + 1)) (fun h =>
    Finset.sum (descendants 64 d (by norm_num) w h) (fun z =>
      min (profile z h) (a z.l : Rat)))

def geometricProfile (d t : Nat) (scale theta : Rat) :
    KBag 64 d -> Nat -> Rat :=
  fun z r => scale * invMu * theta ^ r * capacity d z.l t

def profileSiblingFactor (theta : Rat) : Rat :=
  (4096 : Rat) * ((64 * 4096 * theta) / (1 - (64 * 4096 * theta) ^ 2))

/-- Collapse a parity-supported geometric rank profile to the sibling mass
at the parent capacity. This is the profile-dependent replacement for the
old `siblingFactor` estimate. -/
theorem profileBadMass_geometric_le {d : Nat} (t : Nat) (a : Nat -> Nat)
    (hpar : forall l, l % 2 ≠ t % 2 -> a l = 0)
    (scale theta : Rat) (hscale : 0 <= scale) (htheta : 0 <= theta)
    (hgeom : (64 * 4096 * theta) ^ 2 < 1)
    (w : KBag 64 d) (hw : w.l % 2 ≠ t % 2) (hwpos : 1 <= w.l)
    : profileBadMass (geometricProfile d t scale theta) a w <=
      scale * invMu * profileSiblingFactor theta * capacity d (w.l - 1) t := by
  let x : Rat := 64 * 4096 * theta
  have hx0 : 0 <= x := by dsimp [x]; positivity
  have hx2 : x ^ 2 < 1 := by simpa [x] using hgeom
  have hodd := odd_geom_le x hx0 hx2 (d - w.l + 1)
  have hcapw : capacity d w.l t = 4096 * capacity d (w.l - 1) t := by
    calc
      capacity d w.l t = capacity d ((w.l - 1) + 1) t := by congr 1; omega
      _ = 4096 * capacity d (w.l - 1) t := capacity_succ_level d (w.l - 1) t
  unfold profileBadMass
  calc
    _ <= ∑ h ∈ Finset.range (d - w.l + 1),
          (if h % 2 = 1 then
            (64 : Rat) ^ h *
              (scale * invMu * theta ^ h * capacity d (w.l + h) t)
          else 0) := by
      refine Finset.sum_le_sum fun h hh => ?_
      by_cases ho : h % 2 = 1
      · rw [if_pos ho]
        have hsum :
            Finset.sum (descendants 64 d (by norm_num) w h) (fun z =>
              min (geometricProfile d t scale theta z h) (a z.l : Rat)) <=
            Finset.sum (descendants 64 d (by norm_num) w h) (fun _ =>
              scale * invMu * theta ^ h * capacity d (w.l + h) t) := by
          apply Finset.sum_le_sum
          intro z hz
          have hzlevel := ((mem_descendants (by norm_num : 1 <= 64) w h z).mp hz).1
          rw [show geometricProfile d t scale theta z h =
            scale * invMu * theta ^ h * capacity d z.l t by rfl, hzlevel]
          exact min_le_left _ _
        calc
            Finset.sum (descendants 64 d (by norm_num) w h) (fun z =>
                min (geometricProfile d t scale theta z h) (a z.l : Rat))
              <= Finset.sum (descendants 64 d (by norm_num) w h) (fun _ =>
                  scale * invMu * theta ^ h * capacity d (w.l + h) t) := hsum
            _ = (64 : Rat) ^ h *
                  (scale * invMu * theta ^ h * capacity d (w.l + h) t) := by
                rw [Finset.sum_const, descendants_card (by norm_num) w h (by
                  have hwle := w.hl
                  rw [Finset.mem_range] at hh
                  omega)]
                push_cast
                ring
      · rw [if_neg ho]
        have heven : h % 2 = 0 := by omega
        have hsumpar : (w.l + h) % 2 = w.l % 2 := by omega
        have hnot : (w.l + h) % 2 ≠ t % 2 := by rw [hsumpar]; exact hw
        have hzero : a (w.l + h) = 0 := hpar (w.l + h) hnot
        have hsum : Finset.sum (descendants 64 d (by norm_num) w h) (fun z =>
            min (geometricProfile d t scale theta z h) (a z.l : Rat)) = 0 := by
          apply Finset.sum_eq_zero
          intro z hz
          have hzlevel := ((mem_descendants (by norm_num : 1 <= 64) w h z).mp hz).1
          rw [hzlevel, hzero]
          have hprof0 : 0 <= geometricProfile d t scale theta z h := by
            unfold geometricProfile
            have hmu := invMu_pos.le
            have hcz := capacity_nonneg d z.l t
            positivity
          simp [min_eq_right hprof0]
        simp [hsum]
    _ = scale * invMu * capacity d w.l t *
          ∑ h ∈ (Finset.range (d - w.l + 1)).filter (fun h => h % 2 = 1), x ^ h := by
      rw [← Finset.sum_filter]
      calc
        _ = ∑ h ∈ (Finset.range (d - w.l + 1)).filter (fun h => h % 2 = 1),
              (scale * invMu * capacity d w.l t) * x ^ h := by
          apply Finset.sum_congr rfl
          intro h hh
          rw [capacity_add d t h w.l]
          dsimp [x]
          rw [mul_pow, mul_pow]
          ring
        _ = scale * invMu * capacity d w.l t *
              ∑ h ∈ (Finset.range (d - w.l + 1)).filter (fun h => h % 2 = 1), x ^ h := by
          rw [← Finset.mul_sum]
    _ <= scale * invMu * capacity d w.l t * (x / (1 - x ^ 2)) := by
      have hcoef : 0 <= scale * invMu * capacity d w.l t := by
        have hmu := invMu_pos.le
        have hc := capacity_nonneg d w.l t
        positivity
      exact mul_le_mul_of_nonneg_left hodd hcoef
    _ = scale * invMu * profileSiblingFactor theta * capacity d (w.l - 1) t := by
      rw [hcapw]
      dsimp [profileSiblingFactor, x]
      ring

theorem keys_below_child_profile {d : Nat} (t : Nat)
    (pl : Placement 64 d) (a : Nat -> Nat)
    (hcard : forall b : KBag 64 d, (pl.regs b).card = a b.l)
    (profile : KBag 64 d -> Nat -> Rat)
    (hprofile : forall (z : KBag 64 d) (r : Nat), r <= d ->
      ((z.strangers (r + 1) id (pl.regs z) : Nat) : Rat) <= profile z r)
    (u : KBag 64 d) (hul : u.l < d) (j : Fin 64)
    (hwires : (∑ l ∈ Finset.Ioc u.l d,
        (64 : Rat) ^ (l - u.l - 1) * (a l : Rat)) =
      ((64 : Rat) ^ d / (64 : Rat) ^ u.l - capacity d u.l t) / 64) :
    (((pl.regs u).filter fun k => (u.child j.val j.isLt hul).Native k id).card : Rat) <=
      capacity d u.l t / 64 +
        profileBadMass profile a (u.child j.val j.isLt hul) := by
  have hbr : 1 <= 64 := by norm_num
  set w : KBag 64 d := u.child j.val j.isLt hul with hw
  have hwl : w.l = u.l + 1 := rfl
  set S := subtreeKeys 64 d pl (by norm_num) w with hS
  set X := (pl.regs u).filter fun k => w.Native k id with hX
  set Y := S.filter fun k => w.Native k id with hY
  set A := (Finset.univ : Finset (Fin (64 ^ d))).filter fun k => w.Native k id with hA
  have hAcard : A.card = 64 ^ (d - u.l - 1) := by
    have h1 := native_card hbr w
    rwa [hwl, show d - (u.l + 1) = d - u.l - 1 by omega] at h1
  have hdisjS : Disjoint (pl.regs u) S := by
    rw [hS, subtreeKeys, Finset.disjoint_biUnion_right]
    intro z hz
    refine pl.disjoint u z fun e => ?_
    have := subtreeBags_l_ge hbr w z hz
    rw [← e] at this
    omega
  have hcardXY : X.card + Y.card <= A.card := by
    rw [← Finset.card_union_of_disjoint
      (Finset.disjoint_of_subset_left (Finset.filter_subset _ _)
        (Finset.disjoint_of_subset_right (Finset.filter_subset _ _) hdisjS))]
    refine Finset.card_le_card (Finset.union_subset ?_ ?_) <;>
      exact fun k hk => mem_filter.2 ⟨mem_univ _, (mem_filter.1 hk).2⟩
  have hsplit := Finset.card_filter_add_card_filter_not (s := S) (fun k => w.Native k id)
  have hScard : (S.card : Rat) =
      ((64 : Rat) ^ d / (64 : Rat) ^ u.l - capacity d u.l t) / 64 := by
    rw [← hwires, hS, card_subtreeKeys hbr pl w a hcard,
      wires_reindex a u.l d hul (64 : Rat)]
    push_cast
    rw [hwl]
  have hbad : (((S.filter fun k => ¬ w.Native k id).card : Nat) : Rat) <=
      profileBadMass profile a w := by
    rw [hS]
    simpa [profileBadMass] using
      subtree_bad_le_profile d pl a hcard profile hprofile w
  have hAq : ((A.card : Nat) : Rat) = (64 : Rat) ^ d / (64 : Rat) ^ u.l / 64 := by
    rw [hAcard]
    have hpow : (64 : Rat) ^ d = (64 : Rat) ^ (d - u.l - 1) * 64 * (64 : Rat) ^ u.l := by
      rw [← pow_succ, ← pow_add]
      congr 1
      omega
    push_cast
    rw [hpow]
    field_simp
  have c1 : ((X.card + Y.card : Nat) : Rat) <= A.card := by exact_mod_cast hcardXY
  have c2 : ((Y.card + (S.filter fun k => ¬ w.Native k id).card : Nat) : Rat) = S.card := by
    exact_mod_cast hsplit
  push_cast at c1 c2 hbad hAq
  have hid : capacity d u.l t / 64 =
      (64 : Rat) ^ d / (64 : Rat) ^ u.l / 64 -
        ((64 : Rat) ^ d / (64 : Rat) ^ u.l - capacity d u.l t) / 64 := by ring
  linarith

end Chvatal
