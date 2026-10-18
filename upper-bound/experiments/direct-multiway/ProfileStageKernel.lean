import AKS.Chvatal.StageKernel
import AKS.Chvatal.StrangerBounds
import ProfileKeysBelowChild
import ProfileWeights
set_option maxHeartbeats 0

/-! Scratch profile-sensitive children transfer and one-stage coefficient checks.
This intentionally does not alter the promoted StageKernel. -/

namespace Chvatal

open Finset

/-- Children-send estimate with an arbitrary rank profile. At target order `r+1`,
each child is charged at profile rank `r+1` (its outsider order is `r+2`). -/
theorem strangers_children_profile_le
    {d : Nat} (t : Nat) (pl : Placement 64 d)
    (perm : Fin (64 ^ d) → Fin (64 ^ d))
    (profile : KBag 64 d -> Nat -> Rat)
    (hprof : forall (z : KBag 64 d) (q : Nat), q <= d ->
      ((z.strangers (q + 1) perm (pl.regs z) : Nat) : Rat) <= profile z q)
    (b : KBag 64 d) (hbd : b.l < d) (r : Nat)
    (hrd : r + 1 <= d)
    (S : Finset (Fin (64 ^ d)))
    (hS : S ⊆ univ.biUnion
      (fun i : Fin 64 => pl.regs (b.child i.val i.isLt hbd))) :
    (b.strangers (r + 1) perm S : Rat) <=
      ∑ i : Fin 64, profile (b.child i.val i.isLt hbd) (r + 1) := by
  calc
    (b.strangers (r + 1) perm S : Rat) <=
        ∑ i : Fin 64, (b.strangers (r + 1) perm
            (pl.regs (b.child i.val i.isLt hbd)) : Rat) := by
              exact_mod_cast (b.strangers_mono (r + 1) perm hS).trans
                (strangers_biUnion_le d b (r + 1) perm
                  (fun i => pl.regs (b.child i.val i.isLt hbd)))
    _ <= _ := Finset.sum_le_sum fun i _ => by
      rw [strangers_child_eq d b hbd (r + 1) (by omega) i perm _]
      exact hprof (b.child i.val i.isLt hbd) (r + 1) hrd

/-- The profile recurrence on positive ranks, isolated from combinatorial details.
`parent` is the old profile mass at the parent rank; `children` is the aggregate
old profile mass at rank `r+1` over the 64 child bags. -/
theorem profile_higher_rank_stage_closes
    (c target parent children : Rat) (r : Nat)
    (hc : 0 <= c) (hr : 1 <= r)
    (hcap : target = 64 * c)
    (hparent : parent <= profileScale * invMu *
      profileEffectiveDelta ^ (r - 1) * c)
    (hchildren : children <= 64 * profileScale * invMu *
      profileEffectiveDelta ^ (r + 1) * (4096 ^ 2 * c))
    (htransfer : profileRankTransfer <= 1) :
    invEpsF * parent + children <=
      profileScale * invMu * profileEffectiveDelta ^ r * target := by
  rw [hcap]
  have hcoef : invEpsF / (64 * profileEffectiveDelta) +
      (4096 : Rat) ^ 2 * profileEffectiveDelta <= 1 := htransfer
  have htheta : 0 < profileEffectiveDelta := by
    norm_num [profileEffectiveDelta, profileGamma, invDelta]
  have hbase : 0 <= profileScale * invMu *
      profileEffectiveDelta ^ (r - 1) * c := by
    have hs : 0 <= profileScale := by norm_num [profileScale]
    exact mul_nonneg (mul_nonneg (mul_nonneg hs invMu_pos.le)
      (pow_nonneg htheta.le _)) hc
  calc
    invEpsF * parent + children <=
        invEpsF * (profileScale * invMu * profileEffectiveDelta ^ (r - 1) * c) +
          64 * profileScale * invMu * profileEffectiveDelta ^ (r + 1) *
            (4096 ^ 2 * c) := by
              exact add_le_add (mul_le_mul_of_nonneg_left hparent invEpsF_nonneg) hchildren
    _ <= profileScale * invMu * profileEffectiveDelta ^ (r - 1) * c *
        (64 * profileEffectiveDelta) := by
          have hscaled := mul_le_mul_of_nonneg_right hcoef
            (show (0 : Rat) <= 64 * profileEffectiveDelta by positivity)
          have halg : invEpsF + 64 * 4096 ^ 2 * profileEffectiveDelta ^ 2 <=
              64 * profileEffectiveDelta := by
            have := hscaled
            field_simp [ne_of_gt htheta] at this
            nlinarith [this]
          calc
            _ = (profileScale * invMu * profileEffectiveDelta ^ (r - 1) * c) *
                (invEpsF + 64 * 4096 ^ 2 * profileEffectiveDelta ^ 2) := by
                  rw [show r + 1 = (r - 1) + 2 by omega, pow_add]
                  ring
            _ <= _ := mul_le_mul_of_nonneg_left halg hbase
    _ = profileScale * invMu * profileEffectiveDelta ^ r * (64 * c) := by
          have hrpow : profileEffectiveDelta ^ r =
              profileEffectiveDelta ^ (r - 1) * profileEffectiveDelta := by
            rw [show r = (r - 1) + 1 by omega, pow_succ,
              show r - 1 + 1 - 1 = r - 1 by omega]
          rw [hrpow]
          ring

theorem profile_rank_transfer_le_one : profileRankTransfer <= 1 :=
  le_of_lt profileRankTransfer_lt_one

/-- Rank-zero local recurrence, retaining the individual parent, sibling,
fresh-error, and children contributions. -/
theorem profile_rank_zero_stage_closes_of_components
    (c target parent sibling children : Rat) (hc : 0 <= c)
    (hcap : target = 64 * c)
    (hparent : parent <= profileScale * invMu * c)
    (hsibling : sibling <= profileScale * invMu *
      profileSiblingFactor profileEffectiveDelta * c)
    (hchildren : children <= 64 * profileScale * invMu *
      profileEffectiveDelta * (4096 ^ 2 * c)) :
    parent + 63 * sibling + (invEpsB + slackCoeff) * c + children <=
      profileScale * invMu * target := by
  have hcoef := profileRankZero_closes
  have hbase : 0 <= 64 * invMu * c :=
    mul_nonneg (mul_nonneg (by norm_num) invMu_pos.le) hc
  have hscaled := mul_le_mul_of_nonneg_right hcoef hbase
  have htheta : profileEffectiveDelta = invDelta * profileGamma := rfl
  have hfactor : profileSiblingFactor profileEffectiveDelta =
      4096 * ((64 : Rat) * 4096 * profileEffectiveDelta) /
        (1 - (64 * 4096 * profileEffectiveDelta) ^ 2) := by
    rw [profileSiblingFactor]
    ring
  have htransferForm : profileRankZeroTransfer =
      1 / 64 + 4096 ^ 2 * profileEffectiveDelta +
        (63 / 64 : Rat) * profileSiblingFactor profileEffectiveDelta := by
    unfold profileRankZeroTransfer
    rw [hfactor]
    ring
  have herr : 64 * invMu * c * profileRankZeroError =
      (invEpsB + slackCoeff) * c := by
    rw [profileRankZeroError]
    field_simp [ne_of_gt invMu_pos]
  have hterms :
      parent + 63 * sibling + (invEpsB + slackCoeff) * c + children <=
        (64 * invMu * c) *
          (profileRankZeroTransfer * profileScale + profileRankZeroError) := by
    rw [htransferForm]
    rw [← herr]
    have hchild' : children <=
        (64 * invMu * c) *
          (profileScale * (4096 : Rat) ^ 2 * profileEffectiveDelta) := by
      calc
        children <= 64 * profileScale * invMu * profileEffectiveDelta *
            (4096 ^ 2 * c) := hchildren
        _ = (64 * invMu * c) *
            (profileScale * (4096 : Rat) ^ 2 * profileEffectiveDelta) := by ring
    have hsib' : 63 * sibling <= (64 * invMu * c) *
        (profileScale * (63 / 64 : Rat) * profileSiblingFactor profileEffectiveDelta) := by
      calc
        63 * sibling <= 63 * (profileScale * invMu *
            profileSiblingFactor profileEffectiveDelta * c) := by nlinarith [hsibling]
        _ = _ := by ring
    have hpar' : parent <= (64 * invMu * c) * (profileScale / 64) := by
      calc
        parent <= profileScale * invMu * c := hparent
        _ = _ := by ring
    have hscaled' : (64 * invMu * c) *
        (profileRankZeroTransfer * profileScale + profileRankZeroError) <=
          (64 * invMu * c) * profileScale := by nlinarith [hscaled]
    nlinarith [hscaled', hchild', hsib', hpar']
  calc
    parent + 63 * sibling + (invEpsB + slackCoeff) * c + children <=
        (64 * invMu * c) *
          (profileRankZeroTransfer * profileScale + profileRankZeroError) := hterms
    _ <= (64 * invMu * c) * profileScale := by nlinarith [hscaled]
    _ = profileScale * invMu * target := by rw [hcap]; ring

/-- Profile-valued version of the outsider invariant. -/
def ProfileOutsiderBoundLe (d t : Nat) (pl : Placement 64 d)
    (perm : Fin (64 ^ d) → Fin (64 ^ d)) : Prop :=
  ∀ (b : KBag 64 d) (r : Nat), r ≤ d →
    ((b.strangers (r + 1) perm (pl.regs b) : Nat) : Rat) ≤
      profileScale * invMu * profileEffectiveDelta ^ r * capacity d b.l t

/-- The profile is a pointwise strengthening of the old scalar invariant, so
the existing fringe-send analysis can consume it without modification. -/
theorem profileOutsiderBoundLe_to_scalar
    {d t : Nat} {pl : Placement 64 d}
    {perm : Fin (64 ^ d) → Fin (64 ^ d)}
    (hP : ProfileOutsiderBoundLe d t pl perm) :
    OutsiderBoundLe d t pl perm := by
  intro b r hr
  have htheta : profileEffectiveDelta ≤ invDelta := by
    norm_num [profileEffectiveDelta, profileGamma, invDelta]
  have hpow : profileEffectiveDelta ^ r ≤ invDelta ^ r :=
    pow_le_pow_left₀ (by norm_num [profileEffectiveDelta, profileGamma, invDelta])
      htheta r
  have hscale : profileScale ≤ 1 := by norm_num [profileScale]
  have hcoef : profileScale * invMu * profileEffectiveDelta ^ r ≤
      invMu * invDelta ^ r := by
    calc
      profileScale * invMu * profileEffectiveDelta ^ r ≤
          1 * invMu * profileEffectiveDelta ^ r := by
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right hscale invMu_pos.le)
              (pow_nonneg (by norm_num [profileEffectiveDelta,
                profileGamma, invDelta]) _)
      _ = invMu * profileEffectiveDelta ^ r := by ring
      _ ≤ invMu * invDelta ^ r := by
            exact mul_le_mul_of_nonneg_left hpow invMu_pos.le
  calc
    ((b.strangers (r + 1) perm (pl.regs b) : Nat) : Rat) ≤
        profileScale * invMu * profileEffectiveDelta ^ r * capacity d b.l t := hP b r hr
    _ ≤ invMu * invDelta ^ r * capacity d b.l t :=
      mul_le_mul_of_nonneg_right hcoef (capacity_nonneg d b.l t)

/-- Minimal profile-aware one-stage interface. Unlike `StageKernel`, its children-send
field is only a containment; the quantitative estimate is derived from the full profile. -/
structure ProfileStageKernel (d : Nat) (t : Nat) (pl : Placement 64 d)
    (perm : Fin (64 ^ d) → Fin (64 ^ d))
    (pl' : Placement 64 d) where
  step : PlacementStep d pl pl'
  hBadSend0 : ∀ (b : KBag 64 d) (hb : 1 ≤ b.l),
    (b.strangers 1 perm (step.fromParent b hb) : Rat) ≤
      parentOutMass d pl perm b hb +
        63 * profileScale * invMu * profileSiblingFactor profileEffectiveDelta *
          capacity d (b.l - 1) t +
        (invEpsB + slackCoeff) * capacity d (b.l - 1) t
  hFringeSend : ∀ (b : KBag 64 d) (r : Nat) (hr : 1 ≤ r) (hrd : r ≤ d)
      (hb : 1 ≤ b.l),
    (b.strangers (r + 1) perm (step.fromParent b hb) : Rat) ≤
      invEpsF * ((b.parent).strangers r perm (pl.regs b.parent) : Rat)
  hChildrenSubset : ∀ (b : KBag 64 d) (hb : 1 ≤ b.l),
    ∀ hbd : b.l < d,
      step.fromChildren b hb ⊆ univ.biUnion
        (fun i : Fin 64 => pl.regs (b.child i.val i.isLt hbd))
  hChildrenLeaf : ∀ (b : KBag 64 d) (hb : 1 ≤ b.l),
    ¬ b.l < d → step.fromChildren b hb = ∅
  level0 : ∀ (b : KBag 64 d) (r : Nat), b.l = 0 → r ≤ d →
    ((b.strangers (r + 1) perm (pl'.regs b) : Nat) : Rat) ≤
      profileScale * invMu * profileEffectiveDelta ^ r * capacity d 0 (t + 1)

/-- A profile invariant advances one stage when parent sends obey the profile
fringe estimate and the children source is contained in the prior child registers.
The children estimate is derived from the whole profile, rather than the old scalar bound. -/
theorem profileOutsiderBound_step_of_kernel
    (d t : Nat) (pl pl' : Placement 64 d)
    (perm : Fin (64 ^ d) → Fin (64 ^ d))
    (hP : ProfileOutsiderBoundLe d t pl perm)
    (K : ProfileStageKernel d t pl perm pl') :
    ProfileOutsiderBoundLe d (t + 1) pl' perm := by
  intro b r hr
  by_cases hb0 : b.l = 0
  · simpa [hb0] using K.level0 b r hb0 hr
  have hb : 1 ≤ b.l := by omega
  have hc : 0 ≤ capacity d (b.l - 1) t := capacity_nonneg d _ _
  have hcap : capacity d b.l (t + 1) = 64 * capacity d (b.l - 1) t := by
    rw [show b.l = (b.l - 1) + 1 by omega, capacity_succ_level,
      capacity_succ_stage]
    simp only [Nat.add_sub_cancel]
    ring
  have hchildren (j : Nat) (hj : 1 ≤ j) (hjd : j ≤ d) :
      (b.strangers j perm (K.step.fromChildren b hb) : Rat) ≤
        64 * profileScale * invMu * profileEffectiveDelta ^ j *
          (4096 ^ 2 * capacity d (b.l - 1) t) := by
    by_cases hbd : b.l < d
    · let prof : KBag 64 d → Nat → Rat := fun z q =>
        profileScale * invMu * profileEffectiveDelta ^ q * capacity d z.l t
      have hraw₀ := strangers_children_profile_le t pl perm prof
        (fun z q hq => by simpa [prof] using hP z q hq) b hbd (j - 1)
        (by omega)
        (K.step.fromChildren b hb) (K.hChildrenSubset b hb hbd)
      have hraw : (b.strangers j perm (K.step.fromChildren b hb) : Rat) ≤
          ∑ i : Fin 64, prof (b.child i.val i.isLt hbd) j := by
        simpa [Nat.sub_add_cancel hj] using hraw₀
      have hsum :
          (∑ i : Fin 64, profileScale * invMu * profileEffectiveDelta ^ j *
            capacity d (b.l + 1) t) =
            64 * profileScale * invMu * profileEffectiveDelta ^ j *
              capacity d (b.l + 1) t := by simp <;> ring
      have hle :
          (∑ i : Fin 64, prof (b.child i.val i.isLt hbd) j) ≤
            ∑ i : Fin 64, profileScale * invMu * profileEffectiveDelta ^ j *
              capacity d (b.l + 1) t := Finset.sum_le_sum fun (i : Fin 64) hi => by
        have hp := hP (b.child i.val i.isLt hbd) j hjd
        simpa [prof, show (b.child i.val i.isLt hbd).l = b.l + 1 from rfl] using hp
      have hraw' : (b.strangers j perm (K.step.fromChildren b hb) : Rat) <=
          64 * profileScale * invMu * profileEffectiveDelta ^ j *
            capacity d (b.l + 1) t := by
        calc
          _ <= ∑ i : Fin 64, profileScale * invMu * profileEffectiveDelta ^ j *
              capacity d (b.l + 1) t := hraw.trans hle
          _ = _ := hsum
      rw [capacity_two_levels d t b hb] at hraw'
      convert hraw' using 1 <;> ring
    · have hempty := K.hChildrenLeaf b hb hbd
      rw [hempty, KBag.strangers_empty, Nat.cast_zero]
      have htheta : 0 ≤ profileEffectiveDelta := by
        norm_num [profileEffectiveDelta, profileGamma, invDelta]
      have hs : 0 ≤ profileScale := by norm_num [profileScale]
      have hm := invMu_pos.le
      have hcap' := capacity_nonneg d (b.l - 1) t
      positivity
  have hsplit := K.step.strangers_split_le perm b hb (r + 1)
  by_cases hr0 : r = 0
  · subst r
    have hparent : parentOutMass d pl perm b hb <=
        profileScale * invMu * capacity d (b.l - 1) t := by
      simpa [parentOutMass] using hP b.parent 0 (Nat.zero_le d)
    have hchildren0 : (b.strangers 1 perm (K.step.fromChildren b hb) : Rat) <=
        64 * profileScale * invMu * profileEffectiveDelta *
          (4096 ^ 2 * capacity d (b.l - 1) t) := by
      simpa [pow_one] using hchildren 1 le_rfl (by have := b.hl; omega)
    have hlocal := profile_rank_zero_stage_closes_of_components
      (capacity d (b.l - 1) t) (capacity d b.l (t + 1))
      (parentOutMass d pl perm b hb)
      (profileScale * invMu * profileSiblingFactor profileEffectiveDelta *
        capacity d (b.l - 1) t)
      (b.strangers 1 perm (K.step.fromChildren b hb) : Rat)
      hc hcap hparent le_rfl hchildren0
    calc
      ((b.strangers 1 perm (pl'.regs b) : Nat) : Rat) <=
          (b.strangers 1 perm (K.step.fromParent b hb) : Rat) +
            (b.strangers 1 perm (K.step.fromChildren b hb) : Rat) := hsplit
      _ <= parentOutMass d pl perm b hb +
          63 * profileScale * invMu * profileSiblingFactor profileEffectiveDelta *
            capacity d (b.l - 1) t +
          (invEpsB + slackCoeff) * capacity d (b.l - 1) t +
          (b.strangers 1 perm (K.step.fromChildren b hb) : Rat) := by
            exact add_le_add (K.hBadSend0 b hb) le_rfl
      _ <= profileScale * invMu * profileEffectiveDelta ^ 0 *
          capacity d b.l (t + 1) := by
            convert hlocal using 1 <;> simp [pow_zero] <;> ring
  · have hr1 : 1 ≤ r := by omega
    have hparent :
        ((b.parent).strangers r perm (pl.regs b.parent) : Rat) <=
          profileScale * invMu * profileEffectiveDelta ^ (r - 1) *
            capacity d (b.l - 1) t := by
      have hp := hP b.parent (r - 1) (by omega)
      rw [Nat.sub_add_cancel hr1,
        show (b.parent).l = b.l - 1 from rfl] at hp
      exact hp
    have hchildrenR : (b.strangers (r + 1) perm
        (K.step.fromChildren b hb) : Rat) <=
        64 * profileScale * invMu * profileEffectiveDelta ^ (r + 1) *
          (4096 ^ 2 * capacity d (b.l - 1) t) := by
      by_cases hrd' : r + 1 <= d
      · exact hchildren (r + 1) (by omega) hrd'
      · have hbl : b.l ≤ d := b.hl
        have hdr : d ≤ r := by omega
        have horder : b.l < r + 1 := by omega
        rw [KBag.strangers_eq_zero_of_lt_order b (r + 1) perm
          (K.step.fromChildren b hb) (by norm_num) (by omega) horder,
          Nat.cast_zero]
        have htheta : 0 ≤ profileEffectiveDelta := by
          norm_num [profileEffectiveDelta, profileGamma, invDelta]
        have hs : 0 ≤ profileScale := by norm_num [profileScale]
        have hm := invMu_pos.le
        have hcap' := capacity_nonneg d (b.l - 1) t
        positivity
    have hlocal := profile_higher_rank_stage_closes
      (capacity d (b.l - 1) t) (capacity d b.l (t + 1))
      ((b.parent).strangers r perm (pl.regs b.parent) : Rat)
      (b.strangers (r + 1) perm (K.step.fromChildren b hb) : Rat)
      r hc hr1 hcap hparent hchildrenR profile_rank_transfer_le_one
    calc
      ((b.strangers (r + 1) perm (pl'.regs b) : Nat) : Rat) <=
          (b.strangers (r + 1) perm (K.step.fromParent b hb) : Rat) +
            (b.strangers (r + 1) perm (K.step.fromChildren b hb) : Rat) := hsplit
      _ <= invEpsF * ((b.parent).strangers r perm (pl.regs b.parent) : Rat) +
          (b.strangers (r + 1) perm (K.step.fromChildren b hb) : Rat) := by
            exact add_le_add (K.hFringeSend b r hr1 hr hb) le_rfl
      _ <= profileScale * invMu * profileEffectiveDelta ^ r *
          capacity d b.l (t + 1) := hlocal


end Chvatal
