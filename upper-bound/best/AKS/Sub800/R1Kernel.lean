import AKS.Sub800.R1Sched
import AKS.Sub800.R1Scal
import AKS.Sub800.R1BadSend

/-! # The outsider invariant `P` and one stage of Lemma 4.3′ at the R1 constants (W1, step 7)

Constants (R1-PROOF): `k = 16`, `A = 32`, `ν = 1/8`, `μ = (1 − 2^-10)·63/4194304`, `δ = 135/10^8`,
`ε_B = 1/105000`, `ε_F = 1/190000`, `r* = 15/524288`, `η = 1 + 7/4096`, and a reserve `γ` for the
separator-geometry charge; they are the fields of `sc : R1Scal`. The order-0 send budget per parent capacity is
`B0 = 15 μ sib + r* + ε_B η + 0.1 μ`, `sib = δ k A²/(1 − δ² k² A²)`, and (4.2′) reads
`μ + B0 + μ δ k A² ≤ μ A ν` (`cond42`); (4.5) is `ε_F/(Aν) + δ² A k/ν ≤ δ` (`cond45`). -/

namespace R1T

open Chvatal (KBag Placement)

variable {sc : R1Scal}

/-- Proposition `P` at stage `t` (non-strict form). -/
def OutsiderBoundLe (sc : R1Scal) (d t : ℕ) (pl : Placement 16 d) (perm : Fin (16 ^ d) → Fin (16 ^ d)) : Prop :=
  ∀ (b : KBag 16 d) (r : ℕ), r ≤ d →
    ((b.strangers (r + 1) perm (pl.regs b) : ℚ)) ≤ sc.mu * sc.delta ^ r * cap d b.l t

/-- One stage's register routing. -/
structure PlacementStep (d : ℕ) (pl pl' : Placement 16 d) where
  fromParent : ∀ (b : KBag 16 d), 1 ≤ b.l → Finset (Fin (16 ^ d))
  fromChildren : ∀ (b : KBag 16 d), 1 ≤ b.l → Finset (Fin (16 ^ d))
  hregs : ∀ (b : KBag 16 d) (hb : 1 ≤ b.l), pl'.regs b ⊆ fromParent b hb ∪ fromChildren b hb

theorem PlacementStep.strangers_split_le {d : ℕ} {pl pl' : Placement 16 d}
    (S : PlacementStep d pl pl') (perm' : Fin (16 ^ d) → Fin (16 ^ d))
    (b : KBag 16 d) (hb : 1 ≤ b.l) (j : ℕ) :
    (b.strangers j perm' (pl'.regs b) : ℚ) ≤
      (b.strangers j perm' (S.fromParent b hb) : ℚ) + (b.strangers j perm' (S.fromChildren b hb) : ℚ) := by
  exact_mod_cast (b.strangers_mono j perm' (S.hregs b hb)).trans (b.strangers_union_le j perm' _ _)

/-- The stage interface: the per-child send bounds at stage `t`. -/
structure StageKernel (sc : R1Scal) (d t : ℕ) (pl : Placement 16 d) (perm : Fin (16 ^ d) → Fin (16 ^ d))
    (pl' : Placement 16 d) (perm' : Fin (16 ^ d) → Fin (16 ^ d)) where
  step : PlacementStep d pl pl'
  hBadSend0 : ∀ (b : KBag 16 d) (hb : 1 ≤ b.l),
    ((b.strangers 1 perm' (step.fromParent b hb) : ℚ)) ≤
      ((b.parent).strangers 1 perm (pl.regs b.parent) : ℚ) + sc.B0 * cap d (b.l - 1) t
  hFringeSend : ∀ (b : KBag 16 d) (r : ℕ) (_hr1 : 1 ≤ r) (_hrd : r ≤ d) (hb : 1 ≤ b.l),
    ((b.strangers (r + 1) perm' (step.fromParent b hb) : ℚ)) ≤
      sc.epsF * ((b.parent).strangers r perm (pl.regs b.parent) : ℚ)
  hFromChildren0 : ∀ (b : KBag 16 d) (hb : 1 ≤ b.l),
    ((b.strangers 1 perm' (step.fromChildren b hb) : ℚ)) ≤
      sc.mu * sc.delta * 16 * 32 ^ 2 * cap d (b.l - 1) t
  hFromChildrenR : ∀ (b : KBag 16 d) (r : ℕ) (_hr1 : 1 ≤ r) (_hrd : r ≤ d) (hb : 1 ≤ b.l),
    ((b.strangers (r + 1) perm' (step.fromChildren b hb) : ℚ)) ≤
      sc.delta ^ 2 * 32 * 16 / (1 / 8) * (sc.mu * sc.delta ^ (r - 1) * (4 * cap d (b.l - 1) t))
  level0 : ∀ (b : KBag 16 d) (r : ℕ), b.l = 0 → r ≤ d →
    ((b.strangers (r + 1) perm' (pl'.regs b) : ℚ)) ≤ sc.mu * sc.delta ^ r * cap d 0 (t + 1)

/-- `c(l, t+1) = A ν · c(l−1, t)`. -/
theorem cap_next (d l t : ℕ) (hl : 1 ≤ l) : cap d l (t + 1) = 4 * cap d (l - 1) t := by
  obtain ⟨m, rfl⟩ : ∃ m, l = m + 1 := ⟨l - 1, by omega⟩
  rw [cap_succ_stage, cap_succ_level, Nat.add_sub_cancel]; ring

/-- **One stage of Lemma 4.3′**: `P(t)` and the stage kernel give `P(t+1)`. -/
theorem outsiderBound_step (d t : ℕ) (pl pl' : Placement 16 d)
    (perm perm' : Fin (16 ^ d) → Fin (16 ^ d)) (hP : OutsiderBoundLe sc d t pl perm)
    (K : StageKernel sc d t pl perm pl' perm') : OutsiderBoundLe sc d (t + 1) pl' perm' := by
  intro b r hr
  by_cases hb0 : b.l = 0
  · simpa [hb0] using K.level0 b r hb0 hr
  have hb : 1 ≤ b.l := by omega
  have hc := (cap_pos d (b.l - 1) t).le
  rw [cap_next d b.l t hb]
  have hsplit := K.step.strangers_split_le perm' b hb (r + 1)
  by_cases hr0 : r = 0
  · subst hr0
    have hpar : ((b.parent).strangers 1 perm (pl.regs b.parent) : ℚ) ≤ sc.mu * cap d (b.l - 1) t := by
      simpa using hP b.parent 0 (Nat.zero_le d)
    have h := mul_le_mul_of_nonneg_right sc.cond42' hc
    have h1 := K.hBadSend0 b hb
    have h2 := K.hFromChildren0 b hb
    simp only [pow_zero, mul_one, zero_add] at hsplit ⊢
    nlinarith
  · have hr1 : 1 ≤ r := by omega
    have hsrc := hP b.parent (r - 1) (by omega)
    rw [Nat.sub_add_cancel hr1, show b.parent.l = b.l - 1 from rfl] at hsrc
    have hf := mul_le_mul_of_nonneg_left hsrc sc.epsF_nonneg
    have h45 : sc.epsF * (sc.mu * sc.delta ^ (r - 1) * cap d (b.l - 1) t) +
        sc.delta ^ 2 * 32 * 16 / (1 / 8) * (sc.mu * sc.delta ^ (r - 1) * (4 * cap d (b.l - 1) t)) ≤
        sc.mu * sc.delta ^ r * (4 * cap d (b.l - 1) t) := by
      have hm : 0 ≤ sc.mu * sc.delta ^ (r - 1) * cap d (b.l - 1) t :=
        mul_nonneg (mul_nonneg sc.mu_pos.le (pow_nonneg sc.delta_pos.le _)) hc
      have := mul_le_mul_of_nonneg_right sc.cond45 (mul_nonneg hm (by norm_num : (0 : ℚ) ≤ 4))
      obtain ⟨s, rfl⟩ : ∃ s, r = s + 1 := ⟨r - 1, by omega⟩
      simp only [Nat.add_sub_cancel] at this hm ⊢
      have e1 : sc.epsF * (sc.mu * sc.delta ^ s * cap d (b.l - 1) t) +
          sc.delta ^ 2 * 32 * 16 / (1 / 8) * (sc.mu * sc.delta ^ s * (4 * cap d (b.l - 1) t)) =
          (sc.epsF / 4 + sc.delta ^ 2 * 32 * 16 / (1 / 8)) * (sc.mu * sc.delta ^ s * cap d (b.l - 1) t * 4) := by
        ring
      have e2 : sc.mu * sc.delta ^ (s + 1) * (4 * cap d (b.l - 1) t) =
          sc.delta * (sc.mu * sc.delta ^ s * cap d (b.l - 1) t * 4) := by ring
      rw [e1, e2]; exact this
    linarith [K.hFringeSend b r hr1 hr hb, K.hFromChildrenR b r hr1 hr hb]

end R1T
