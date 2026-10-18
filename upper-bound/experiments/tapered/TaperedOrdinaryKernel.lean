import AKS.Chvatal.StageKernel
import CandidateFrontier
import SignedReserve
import Mathlib.Tactic

/-!
Candidate-specific ordinary transition interface for the tapered 945 flow.
The interface separates physical routing coverage and local separator estimates
from the scalar induction. Frontier transitions are intentionally excluded.
-/
namespace Tapered945

open Chvatal

/-- All-order outsider invariant at the candidate's tapered scale. -/
def TaperedOutsiderBoundLe (d t : Nat) (pl : Placement 64 d)
    (perm : Fin (64 ^ d) → Fin (64 ^ d)) : Prop :=
  ∀ (b : KBag 64 d) (r : Nat), r ≤ d →
    ((b.strangers (r + 1) perm (pl.regs b) : Rat)) ≤
      mu * delta ^ r * candidateReferenceCapacity d b.l t

/-- The child-up estimate follows from the all-order invariant once the
physical up-sets are proved to belong to the corresponding child registers.
The capacity identity is explicit because the candidate placement has not yet
been built from these local set choices. -/
theorem tapered_child_send_bound_of_owned_cover
    (d t : Nat) (pl : Placement 64 d)
    (perm : Fin (64 ^ d) → Fin (64 ^ d))
    (hP : TaperedOutsiderBoundLe d t pl perm)
    (b : KBag 64 d) (_hb : 1 ≤ b.l) (hdepth : b.l < d)
    (r : Nat) (hr : r + 1 ≤ d)
    (fromChildren : Finset (Fin (64 ^ d)))
    (childUp : Fin 64 → Finset (Fin (64 ^ d)))
    (hcover : fromChildren ⊆ Finset.univ.biUnion childUp)
    (howned : ∀ j : Fin 64,
      childUp j ⊆ pl.regs (b.child j.val j.isLt hdepth))
    (hcapacity : ∀ j : Fin 64,
      candidateReferenceCapacity d (b.child j.val j.isLt hdepth).l t =
        4096 * candidateReferenceCapacity d (b.l - 1) t) :
    ((b.strangers (r + 1) perm fromChildren : Rat)) ≤
      (64 : Rat) ^ 3 * mu * delta ^ (r + 1) *
        candidateReferenceCapacity d (b.l - 1) t := by
  classical
  have hmono := b.strangers_mono (r + 1) perm hcover
  have hunion := Chvatal.strangers_biUnion_le d b (r + 1) perm childUp
  have hnat := hmono.trans hunion
  have hreal :
      ((b.strangers (r + 1) perm fromChildren : Nat) : Rat) ≤
        ∑ j : Fin 64, (b.strangers (r + 1) perm (childUp j) : Rat) := by
    exact_mod_cast hnat
  have hsum :
      (∑ j : Fin 64, (b.strangers (r + 1) perm (childUp j) : Rat)) ≤
        ∑ j : Fin 64,
          (mu * delta ^ (r + 1) *
            candidateReferenceCapacity d (b.child j.val j.isLt hdepth).l t) := by
    apply Finset.sum_le_sum
    intro j hj
    let z := b.child j.val j.isLt hdepth
    have hstr := Chvatal.strangers_child_eq d b hdepth (r + 1) (by omega)
      j perm (childUp j)
    have hown := z.strangers_mono (r + 2) perm (howned j)
    have hPz := hP z (r + 1) hr
    change (z.strangers (r + 2) perm (pl.regs z) : Rat) ≤
      mu * delta ^ (r + 1) * candidateReferenceCapacity d z.l t at hPz
    have hchild :
        ((z.strangers (r + 2) perm (childUp j) : Nat) : Rat) ≤
          mu * delta ^ (r + 1) * candidateReferenceCapacity d z.l t := by
      exact (show ((z.strangers (r + 2) perm (childUp j) : Nat) : Rat) ≤
          ((z.strangers (r + 2) perm (pl.regs z) : Nat) : Rat) by exact_mod_cast hown).trans hPz
    rw [hstr]
    exact hchild
  have hsumEq :
      (∑ j : Fin 64,
          (mu * delta ^ (r + 1) *
            candidateReferenceCapacity d (b.child j.val j.isLt hdepth).l t)) =
        (64 : Rat) ^ 3 * mu * delta ^ (r + 1) *
          candidateReferenceCapacity d (b.l - 1) t := by
    calc
      _ = ∑ _j : Fin 64,
          (mu * delta ^ (r + 1) *
            (4096 * candidateReferenceCapacity d (b.l - 1) t)) := by
              apply Finset.sum_congr rfl
              intro j hj
              rw [hcapacity j]
      _ = (64 : Rat) * (mu * delta ^ (r + 1) *
          (4096 * candidateReferenceCapacity d (b.l - 1) t)) := by simp
      _ = (64 : Rat) ^ 3 * mu * delta ^ (r + 1) *
          candidateReferenceCapacity d (b.l - 1) t := by norm_num; ring
  exact hreal.trans (hsum.trans_eq hsumEq)

/-- The ordinary-node proof obligations, in the same split form as Chvatal's
`StageKernel`, but with tapered capacities and the candidate's signed-debt
price. `badSend0` and `fringeSend` are the exact separator/parent-rank seams;
the two child-send bounds are the geometrically small descendant terms. -/
structure TaperedOrdinaryKernel (d t : Nat)
    (pl : Placement 64 d) (perm : Fin (64 ^ d) → Fin (64 ^ d))
    (pl' : Placement 64 d) (perm' : Fin (64 ^ d) → Fin (64 ^ d)) where
  step : PlacementStep d pl pl'
  capacity : ∀ (b : KBag 64 d), 1 ≤ b.l →
    candidateReferenceCapacity d b.l (t + 1) =
      4 * candidateReferenceCapacity d (b.l - 1) t
  /-- Two-sided cut/rank-window output needed for the parent send. -/
  badSend0 : ∀ (b : KBag 64 d) (hb : 1 ≤ b.l),
    ((b.strangers 1 perm' (step.fromParent b hb) : Rat)) ≤
      ((b.parent).strangers 1 perm (pl.regs b.parent) : Rat) +
        (64 * mu * siblingFactor + epsB + reserve + activeRounding) *
          candidateReferenceCapacity d (b.l - 1) t
  /-- Multiplicative two-round fringe coefficient supplied by the selected
  separator provider. -/
  fringeCoeff : Rat
  fringeCoeff_nonneg : 0 ≤ fringeCoeff
  /-- The recursive scalar budget paid by the selected fringe coefficient. -/
  fringeScalar : fringeCoeff + (64 : Rat) ^ 3 * delta ^ 2 ≤ 4 * delta
  fringeSend : ∀ (b : KBag 64 d) (r : Nat)
      (_hr1 : 1 ≤ r) (_hrd : r ≤ d) (hb : 1 ≤ b.l),
    ((b.strangers (r + 1) perm' (step.fromParent b hb) : Rat)) ≤
      fringeCoeff *
        ((b.parent).strangers r perm (pl.regs b.parent) : Rat)
  /-- Order-zero spill from the child up-sends. -/
  children0 : ∀ (b : KBag 64 d) (hb : 1 ≤ b.l),
    ((b.strangers 1 perm' (step.fromChildren b hb) : Rat)) ≤
      mu * delta * (64 : Rat) ^ 3 *
        candidateReferenceCapacity d (b.l - 1) t
  /-- Higher-order spill from child up-sends. -/
  childrenR : ∀ (b : KBag 64 d) (r : Nat)
      (hr1 : 1 ≤ r) (hrd : r ≤ d) (hb : 1 ≤ b.l),
    ((b.strangers (r + 1) perm' (step.fromChildren b hb) : Rat)) ≤
      (64 : Rat) ^ 3 * mu * delta ^ (r + 1) *
        candidateReferenceCapacity d (b.l - 1) t
  /-- Separate stage-zero/frontier base; no ordinary transition is assumed. -/
  level0 : ∀ (b : KBag 64 d) (r : Nat), b.l = 0 → r ≤ d →
    ((b.strangers (r + 1) perm' (pl'.regs b) : Rat)) ≤
      mu * delta ^ r * candidateReferenceCapacity d 0 (t + 1)

/-- Candidate ordinary transition: P(t) and the listed separator/routing
obligations imply P(t+1). This does not provide the kernel fields. -/
theorem tapered_outsider_step_of_kernel
    (d t : Nat) (pl pl' : Placement 64 d)
    (perm perm' : Fin (64 ^ d) → Fin (64 ^ d))
    (hP : TaperedOutsiderBoundLe d t pl perm)
    (K : TaperedOrdinaryKernel d t pl perm pl' perm') :
    TaperedOutsiderBoundLe d (t + 1) pl' perm' := by
  intro b r hr
  by_cases hb0 : b.l = 0
  · simpa [hb0] using K.level0 b r hb0 hr
  have hb : 1 ≤ b.l := by omega
  rw [K.capacity b hb]
  have hsplit := K.step.strangers_split_le perm' b hb (r + 1)
  by_cases hr0 : r = 0
  · subst r
    have hbad := K.badSend0 b hb
    have hchild := K.children0 b hb
    have hparent :
        ((b.parent).strangers 1 perm (pl.regs b.parent) : Rat) ≤
          mu * candidateReferenceCapacity d (b.l - 1) t := by
      simpa [TaperedOutsiderBoundLe] using hP b.parent 0 (Nat.zero_le d)
    have hmargin := candidate_screened_margin_positive
    unfold screenedMargin at hmargin
    have hcap0 : 0 ≤ candidateReferenceCapacity d (b.l - 1) t := by
      unfold candidateReferenceCapacity
      positivity
    have hscaled := mul_nonneg hmargin.le hcap0
    simp only [pow_zero, mul_one] at ⊢
    nlinarith [hbad, hchild, hparent, hscaled]
  · have hr1 : 1 ≤ r := by omega
    have hparent := hP b.parent (r - 1) (by omega : r - 1 ≤ d)
    have hrpow : r - 1 + 1 = r := Nat.sub_add_cancel hr1
    rw [hrpow] at hparent
    have hfringe := K.fringeSend b r hr1 hr hb
    have hchild := K.childrenR b r hr1 hr hb
    rw [show b.parent.l = b.l - 1 from rfl] at hparent
    have hmu : 0 ≤ mu := by norm_num [mu]
    have hdelta : 0 ≤ delta := by norm_num [delta]
    have hcap0 : 0 ≤ candidateReferenceCapacity d (b.l - 1) t := by
      unfold candidateReferenceCapacity
      positivity
    have hbase : 0 ≤ mu * delta ^ (r - 1) *
        candidateReferenceCapacity d (b.l - 1) t :=
      mul_nonneg (mul_nonneg hmu (pow_nonneg hdelta _)) hcap0
    have hnum := mul_le_mul_of_nonneg_right K.fringeScalar hbase
    have hpowChild : r + 1 = (r - 1) + 2 := by omega
    have hdeltaPow : delta ^ r = delta ^ (r - 1) * delta := by
      calc
        delta ^ r = delta ^ (r - 1 + 1) :=
          congrArg (fun n : Nat => delta ^ n) hrpow.symm
        _ = delta ^ (r - 1) * delta := pow_succ delta (r - 1)
    have hchild' :
        ((b.strangers (r + 1) perm' (K.step.fromChildren b hb) : Rat)) ≤
          (64 : Rat) ^ 3 * delta ^ 2 *
            (mu * delta ^ (r - 1) * candidateReferenceCapacity d (b.l - 1) t) := by
      calc
        _ ≤ (64 : Rat) ^ 3 * mu * delta ^ (r + 1) *
            candidateReferenceCapacity d (b.l - 1) t := hchild
        _ = (64 : Rat) ^ 3 * delta ^ 2 *
            (mu * delta ^ (r - 1) * candidateReferenceCapacity d (b.l - 1) t) := by
          rw [hpowChild, pow_add]
          ring
    have hnum' :
        K.fringeCoeff *
            (mu * delta ^ (r - 1) * candidateReferenceCapacity d (b.l - 1) t) +
          (64 : Rat) ^ 3 * delta ^ 2 *
            (mu * delta ^ (r - 1) * candidateReferenceCapacity d (b.l - 1) t) ≤
          mu * delta ^ r * (4 * candidateReferenceCapacity d (b.l - 1) t) := by
      calc
        _ ≤ (K.fringeCoeff + (64 : Rat) ^ 3 * delta ^ 2) *
              (mu * delta ^ (r - 1) * candidateReferenceCapacity d (b.l - 1) t) := by
          nlinarith [hnum]
        _ ≤ 4 * delta * (mu * delta ^ (r - 1) *
            candidateReferenceCapacity d (b.l - 1) t) := hnum
        _ = mu * delta ^ r * (4 * candidateReferenceCapacity d (b.l - 1) t) := by
          rw [hdeltaPow]
          ring
    have hparent' :
        ((b.strangers (r + 1) perm' (K.step.fromParent b hb) : Rat)) ≤
        K.fringeCoeff *
            (mu * delta ^ (r - 1) * candidateReferenceCapacity d (b.l - 1) t) := by
      exact le_trans hfringe
        (mul_le_mul_of_nonneg_left hparent K.fringeCoeff_nonneg)
    have hresult := add_le_add hparent' hchild'
    exact le_trans (hsplit.trans hresult) hnum'

end Tapered945
