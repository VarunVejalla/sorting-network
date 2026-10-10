module

-- Chvátal §4: the outsider scalars of the §7 instance, the algebraic cores of Lemmas 4.2-4.5,
-- the invariant `P`, placement steps, and `StageKernel`, the one-stage interface by which `P`
-- advances one stage.

public import AKS.Chvatal.Schedule7
public import AKS.Chvatal.Tree
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Field.GeomSum
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

@[expose] public section

namespace Chvatal

/-- Outsider-bound scalars: `μ = (1 - 2^-10)·2^-30` (keeps (4.1)–(4.5) true and makes `μ·c < 1`
whenever `c ≤ 2^30`), `δ = 1/(5.3·10^9)`, `ε_B = 1/(5.9·10^7)` and `ε_F = 1/(8.6·10^7)`. -/
def invMu : Rat := 1023 / 1099511627776
def invDelta : Rat := 1 / 5300000000
def invEpsB : Rat := 1 / 59000000
def invEpsF : Rat := 1 / 86000000

theorem invMu_pos : (0 : Rat) < invMu := by unfold invMu; norm_num
theorem invDelta_pos : (0 : Rat) < invDelta := by unfold invDelta; norm_num
theorem invDelta_lt_one : invDelta < 1 := by unfold invDelta; norm_num
theorem invEpsB_nonneg : (0 : Rat) ≤ invEpsB := by unfold invEpsB; norm_num
theorem invEpsF_nonneg : (0 : Rat) ≤ invEpsF := by unfold invEpsF; norm_num

/-- Geometric factor of Lemmas 4.1-4.3: `δ k A² / (1 - δ² k² A²)`. -/
def siblingFactor : Rat :=
  invDelta * 64 * 4096 ^ 2 / (1 - invDelta ^ 2 * 64 ^ 2 * 4096 ^ 2)

/-- Lemma 4.2 residual `(k-1)Δ₂ - π/2` as a coefficient of `c`. -/
def slackCoeff : Rat :=
  (4096 * (1 / 64) * 64 - 2 * 4096 * (1 / 64) + 1) / (2 * 4096 ^ 2 * 64 ^ 2)

/-- Cond (4.2) scaled by `c ≥ 0`. -/
theorem cond42_scaled (c : Rat) (hc : 0 ≤ c) :
    (invMu + ((64 : Rat) - 1) * invMu * siblingFactor + slackCoeff + invEpsB) * c +
        invMu * invDelta * 64 * 4096 ^ 2 * c ≤ invMu * (4096 * (1 / 64 : Rat) * c) := by
  have h : (invMu + ((64 : Rat) - 1) * invMu * siblingFactor + slackCoeff + invEpsB) /
      (4096 * (1 / 64 : Rat)) + invMu * invDelta * 4096 * 64 / (1 / 64 : Rat) ≤ invMu := by
    unfold siblingFactor slackCoeff invMu invDelta invEpsB; norm_num
  have := mul_le_mul_of_nonneg_right h (mul_nonneg (by norm_num : (0 : Rat) ≤ 4096 * (1 / 64)) hc)
  convert this using 1
  field_simp

/-- Cond (4.5) scaled by `μ δ^{r-1} A ν c`. -/
theorem cond45_scaled (c : Rat) (hc : 0 ≤ c) (r : Nat) (hr : 1 ≤ r) :
    invEpsF * (invMu * invDelta ^ (r - 1) * c) +
        invDelta ^ 2 * 4096 * 64 / (1 / 64 : Rat) *
          (invMu * invDelta ^ (r - 1) * (4096 * (1 / 64 : Rat) * c)) ≤
      invMu * invDelta ^ r * (4096 * (1 / 64 : Rat) * c) := by
  have h : invEpsF / (4096 * (1 / 64 : Rat)) + invDelta ^ 2 * 4096 * 64 / (1 / 64 : Rat) ≤
      invDelta := by
    unfold invEpsF invDelta; norm_num
  have := mul_le_mul_of_nonneg_right h (mul_nonneg (mul_nonneg (mul_nonneg invMu_pos.le
    (pow_nonneg invDelta_pos.le (r - 1))) hc) (by norm_num : (0 : Rat) ≤ 4096 * (1 / 64)))
  obtain ⟨s, rfl⟩ : ∃ s, r = s + 1 := ⟨r - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at this ⊢
  convert this using 1 <;> field_simp
  ring

/-- Non-strict form of proposition `P` at stage `t`, for a placement and rank permutation. -/
def OutsiderBoundLe (d t : Nat) (pl : Placement 64 d)
    (perm : Fin (64 ^ d) → Fin (64 ^ d)) : Prop :=
  ∀ (b : KBag 64 d) (r : Nat), r ≤ d →
    ((b.strangers (r + 1) perm (pl.regs b) : Rat)) ≤
      invMu * invDelta ^ r * capacity d b.l t

/-- One stage's register routing: each non-root child bag is covered by keys sent from its parent
    and keys sent up from its children. -/
structure PlacementStep (d : Nat)
    (pl pl' : Placement 64 d) where
  fromParent : ∀ (b : KBag 64 d), 1 ≤ b.l → Finset (Fin (64 ^ d))
  fromChildren : ∀ (b : KBag 64 d), 1 ≤ b.l → Finset (Fin (64 ^ d))
  hregs : ∀ (b : KBag 64 d) (hb : 1 ≤ b.l),
    pl'.regs b ⊆ fromParent b hb ∪ fromChildren b hb

/-- Outsider count on a covered bag splits across the two send Finsets. -/
theorem PlacementStep.strangers_split_le {d : Nat}
    {pl pl' : Placement 64 d} (S : PlacementStep d pl pl')
    (perm' : Fin (64 ^ d) → Fin (64 ^ d))
    (b : KBag 64 d) (hb : 1 ≤ b.l) (j : Nat) :
    (b.strangers j perm' (pl'.regs b) : Rat) ≤
      (b.strangers j perm' (S.fromParent b hb) : Rat) +
        (b.strangers j perm' (S.fromChildren b hb) : Rat) := by
  exact_mod_cast (b.strangers_mono j perm' (S.hregs b hb)).trans
    (b.strangers_union_le j perm' _ _)

/-- Parent order-0 outsider mass at time `t`. -/
def parentOutMass (d : Nat) (pl : Placement 64 d)
    (perm : Fin (64 ^ d) → Fin (64 ^ d)) (b : KBag 64 d) (_hb : 1 ≤ b.l) : Rat :=
  ((b.parent).strangers 1 perm
    (pl.regs (b.parent)) : Rat)

/-- Paper Lemma 4.2 sibling-contamination budget at the parent capacity. -/
def sibMassBound (d t : Nat)
    (b : KBag 64 d) (_hb : 1 ≤ b.l) : Rat :=
  ((64 : Rat) - 1) * invMu * siblingFactor * capacity d (b.l - 1) t

/-- Schedule slack used by Lemma 4.2: `slackCoeff · c`. -/
def slackBound (d t : Nat)
    (b : KBag 64 d) (_hb : 1 ≤ b.l) : Rat :=
  slackCoeff * capacity d (b.l - 1) t

structure StageKernel (d : Nat)
    (t : Nat) (pl : Placement 64 d)
    (perm : Fin (64 ^ d) → Fin (64 ^ d)) (pl' : Placement 64 d)
    (perm' : Fin (64 ^ d) → Fin (64 ^ d)) where
  ht : t + 1 ≤ tf7 d
  step : PlacementStep d pl pl'
  /-- Order-0 bad keys in the parent-send Finset ≤ parent outsiders + sibling budget +
      intrusion + slack. -/
  hBadSend0 : ∀ (b : KBag 64 d) (hb : 1 ≤ b.l),
    ((b.strangers 1 perm' (step.fromParent b hb) : Rat)) ≤
      parentOutMass d pl perm b hb +
        sibMassBound d t b hb + invEpsB * capacity d (b.l - 1) t +
        slackBound d t b hb
  hFringeSend : ∀ (b : KBag 64 d) (r : Nat)
      (_hr1 : 1 ≤ r) (_hrd : r ≤ d) (hb : 1 ≤ b.l),
    ((b.strangers (r + 1) perm' (step.fromParent b hb) : Rat)) ≤
      invEpsF *
        ((b.parent).strangers r perm
          (pl.regs (b.parent)) : Rat)
  hFromChildren0 : ∀ (b : KBag 64 d) (hb : 1 ≤ b.l),
    ((b.strangers 1 perm' (step.fromChildren b hb) : Rat)) ≤
      invMu * invDelta * (64 : Rat) * (4096 : Rat) ^ 2 * capacity d (b.l - 1) t
  hFromChildrenR : ∀ (b : KBag 64 d) (r : Nat)
      (_hr1 : 1 ≤ r) (_hrd : r ≤ d) (hb : 1 ≤ b.l),
    ((b.strangers (r + 1) perm' (step.fromChildren b hb) : Rat)) ≤
      invDelta ^ 2 * (4096 : Rat) * (64 : Rat) / (1 / 64 : Rat) *
        (invMu * invDelta ^ (r - 1) *
          ((4096 : Rat) * (1 / 64 : Rat) * capacity d (b.l - 1) t))
  level0 : ∀ (b : KBag 64 d) (r : Nat), b.l = 0 → r ≤ d →
    ((b.strangers (r + 1) perm' (pl'.regs b) : Rat)) ≤
      invMu * invDelta ^ r * capacity d 0 (t + 1)

/-- One-step preservation under the stage kernel: `P(t)` + conds + kernel ⇒ `P(t+1)`. -/
theorem outsiderBound_step_of_kernel
    (d : Nat) (t : Nat) (pl pl' : Placement 64 d)
    (perm perm' : Fin (64 ^ d) → Fin (64 ^ d))
    (hP : OutsiderBoundLe d t pl perm)
    (K : StageKernel d t pl perm pl' perm') :
    OutsiderBoundLe d (t + 1) pl' perm' := by
  intro b r hr
  by_cases hb0 : b.l = 0
  · simpa [hb0] using K.level0 b r hb0 hr
  have hb : 1 ≤ b.l := by omega
  have hc := (capacity_pos d (b.l - 1) t).le
  have hcap : capacity d b.l (t + 1) = (4096 : Rat) * (1 / 64 : Rat) * capacity d (b.l - 1) t := by
    rw [show b.l = (b.l - 1) + 1 by omega, capacity_succ_level, capacity_succ_stage]
    simp only [Nat.add_sub_cancel]
    ring
  rw [hcap]
  have hsplit := K.step.strangers_split_le perm' b hb (r + 1)
  by_cases hr0 : r = 0
  · subst hr0
    have hpar : parentOutMass d pl perm b hb ≤ invMu * capacity d (b.l - 1) t := by
      simpa [parentOutMass] using hP b.parent 0 (Nat.zero_le d)
    have h := cond42_scaled _ hc
    have h1 := K.hBadSend0 b hb
    unfold sibMassBound at h1
    unfold slackBound at h1
    simp only [pow_zero, mul_one]
    linarith [K.hFromChildren0 b hb]
  · have hr1 : 1 ≤ r := by omega
    have hsrc := hP b.parent (r - 1) (by omega)
    rw [Nat.sub_add_cancel hr1, show b.parent.l = b.l - 1 from rfl] at hsrc
    have hf := mul_le_mul_of_nonneg_left hsrc invEpsF_nonneg
    have h := cond45_scaled _ hc r hr1
    linarith [K.hFringeSend b r hr1 hr hb, K.hFromChildrenR b r hr1 hr hb]

section

open Finset

/-- Stranger count on a `biUnion` is at most the sum of the counts. -/
theorem strangers_biUnion_le (d : Nat) (b : KBag 64 d) (j : Nat)
    (perm : Fin (64 ^ d) → Fin (64 ^ d)) (f : Fin 64 → Finset (Fin (64 ^ d))) :
    (b.strangers j perm ((univ : Finset (Fin 64)).biUnion f) : Nat) ≤
      ∑ i : Fin 64, b.strangers j perm (f i) := by
  classical
  simp only [KBag.strangers, filter_biUnion]
  exact card_biUnion_le

/-- On any set, order-`j` outsiders at a parent equal order-`(j+1)` at a child. -/
theorem strangers_child_eq (d : Nat) (b : KBag 64 d) (hbd : b.l < d)
    (j : Nat) (hj : 1 ≤ j) (childIdx : Fin 64) (perm : Fin (64 ^ d) → Fin (64 ^ d))
    (S : Finset (Fin (64 ^ d))) :
    b.strangers j perm S =
      (b.child childIdx.val childIdx.isLt hbd).strangers (j + 1) perm S := by
  have h := KBag.strangers_parent_eq (b.child childIdx.val childIdx.isLt hbd) j hj
    (show 1 ≤ b.l + 1 by omega) perm S (by norm_num)
  rwa [KBag.child_parent b childIdx.val childIdx.isLt hbd (by norm_num)] at h

/-- Scale `k · μ · δ^{r+1} · A² · c` into the `StageKernel` children-send form. -/
theorem childrenR_scale (c : Rat) (r : Nat) (hr1 : 1 ≤ r) :
    (64 : Rat) * (invMu * invDelta ^ (r + 1) * ((4096 : Rat) * ((4096 : Rat) * c))) =
      invDelta ^ 2 * (4096 : Rat) * (64 : Rat) / (1 / 64 : Rat) *
        (invMu * invDelta ^ (r - 1) * ((4096 : Rat) * (1 / 64 : Rat) * c)) := by
  obtain ⟨s, rfl⟩ : ∃ s, r = s + 1 := ⟨r - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  field_simp
  ring

end

end Chvatal
