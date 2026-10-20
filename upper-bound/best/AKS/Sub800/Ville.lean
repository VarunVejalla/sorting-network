import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fin.Tuple.Finset
import Mathlib.Data.Fintype.Pi
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic

/-! # Ville's inequality for a walk with independent rows (W4.2 of LEAN-PLAN.md)

Counting form over a product of finite uniform row samples `s r`. Row `r` contributes the
increment `D r (ω r)`. If every row satisfies `E e^{θ D_r} ≤ 1`, then for every `x`

  `#{ω : ∃ h ≤ R, x ≤ D_0 + … + D_{h-1}} ≤ e^{-θ x} · #Ω`.

Proof: induction on `R`, peeling the first row. The event is `{d ≥ x} ∪ {max of the tail ≥ x - d}`,
and `1{d ≥ x} ≤ e^{-θ(x-d)}`. -/

open Finset BigOperators

namespace Ville

/-- Prefix sum of the first `h` increments. -/
def prefixSum {Ω : Type*} {R : ℕ} (D : Fin R → Ω → ℝ) (ω : Fin R → Ω) (h : ℕ) : ℝ :=
  ∑ r : Fin R, if r.val < h then D r (ω r) else 0

theorem prefixSum_zero {Ω : Type*} {R : ℕ} (D : Fin R → Ω → ℝ) (ω : Fin R → Ω) :
    prefixSum D ω 0 = 0 := by
  simp [prefixSum]

theorem prefixSum_cons {Ω : Type*} {R : ℕ} (D : Fin (R + 1) → Ω → ℝ) (x : Ω) (ω : Fin R → Ω)
    (h : ℕ) : prefixSum D (Fin.cons x ω) (h + 1) =
      D 0 x + prefixSum (fun r => D r.succ) ω h := by
  simp only [prefixSum, Fin.sum_univ_succ, Fin.val_zero, Fin.cons_zero, Fin.cons_succ,
    Fin.val_succ]
  simp

/-- The walk reaches `x` at some time `h ≤ R`. -/
def Reaches {Ω : Type*} {R : ℕ} (D : Fin R → Ω → ℝ) (x : ℝ) (ω : Fin R → Ω) : Prop :=
  ∃ h ≤ R, x ≤ prefixSum D ω h

theorem reaches_cons {Ω : Type*} {R : ℕ} (D : Fin (R + 1) → Ω → ℝ) (x : ℝ) (y : Ω)
    (ω : Fin R → Ω) :
    Reaches D x (Fin.cons y ω) ↔ x ≤ 0 ∨ Reaches (fun r => D r.succ) (x - D 0 y) ω := by
  constructor
  · rintro ⟨h, hh, hx⟩
    cases h with
    | zero => left; simpa [prefixSum_zero] using hx
    | succ h =>
      right
      refine ⟨h, by omega, ?_⟩
      rw [prefixSum_cons] at hx
      linarith
  · rintro (hx | ⟨h, hh, hx⟩)
    · exact ⟨0, Nat.zero_le _, by simpa [prefixSum_zero] using hx⟩
    · refine ⟨h + 1, by omega, ?_⟩
      rw [prefixSum_cons]
      linarith

open Classical in
/-- **Ville's inequality**, counting form. -/
theorem ville {Ω : Type*} [DecidableEq Ω] (θ : ℝ) (hθ : 0 ≤ θ) :
    ∀ (R : ℕ) (s : Fin R → Finset Ω) (D : Fin R → Ω → ℝ),
      (∀ r, ∑ ω ∈ s r, Real.exp (θ * D r ω) ≤ ((s r).card : ℝ)) →
      ∀ x : ℝ, (((Fintype.piFinset s).filter (Reaches D x)).card : ℝ) ≤
        Real.exp (-(θ * x)) * ((Fintype.piFinset s).card : ℝ) := by
  intro R
  induction R with
  | zero =>
    intro s D _ x
    have hs : Fintype.piFinset s = {Fin.elim0} := by
      ext ω
      simp only [Fintype.mem_piFinset, Finset.mem_singleton]
      exact ⟨fun _ => funext fun r => r.elim0, fun _ r => r.elim0⟩
    rw [hs]
    by_cases hx : x ≤ 0
    · have : Reaches D x Fin.elim0 := ⟨0, le_rfl, by simpa [prefixSum_zero] using hx⟩
      rw [Finset.filter_singleton, if_pos this]
      simp only [Finset.card_singleton, Nat.cast_one, mul_one]
      exact Real.one_le_exp (by nlinarith)
    · have : ¬ Reaches D x Fin.elim0 := by
        rintro ⟨h, hh, hx'⟩
        have : h = 0 := by omega
        subst this
        simp [prefixSum_zero] at hx'
        exact hx hx'
      rw [Finset.filter_singleton, if_neg this]
      simp only [Finset.card_empty, Nat.cast_zero]
      positivity
  | succ R ih =>
    intro s D hD x
    by_cases hx : x ≤ 0
    · calc (((Fintype.piFinset s).filter (Reaches D x)).card : ℝ)
          ≤ ((Fintype.piFinset s).card : ℝ) := by exact_mod_cast Finset.card_filter_le _ _
        _ ≤ Real.exp (-(θ * x)) * ((Fintype.piFinset s).card : ℝ) := by
          have : 1 ≤ Real.exp (-(θ * x)) := Real.one_le_exp (by nlinarith)
          nlinarith [show (0 : ℝ) ≤ (Fintype.piFinset s).card by positivity]
    push_neg at hx
    -- decompose the sample along `Fin.cons`
    set T := Fintype.piFinset fun r : Fin R => s r.succ
    have hpi : ∀ φ : (Fin (R + 1) → Ω) → ℝ, ∑ ω ∈ Fintype.piFinset s, φ ω =
        ∑ y ∈ s 0, ∑ ω ∈ T, φ (Fin.cons y ω) := by
      intro φ
      rw [← Finset.sum_product']
      refine (Finset.sum_bij' (fun p _ => (Fin.cons p.1 p.2 : Fin (R + 1) → Ω))
        (fun ω _ => (ω 0, Fin.tail ω)) ?_ ?_ ?_ ?_ ?_).symm
      · rintro ⟨y, ω⟩ hp
        rw [Finset.mem_product, Fintype.mem_piFinset] at hp
        rw [Fintype.mem_piFinset]
        intro r
        refine Fin.cases ?_ (fun i => ?_) r
        · simpa using hp.1
        · simpa using hp.2 i
      · intro ω hω
        rw [Fintype.mem_piFinset] at hω
        rw [Finset.mem_product, Fintype.mem_piFinset]
        exact ⟨hω 0, fun i => hω i.succ⟩
      · rintro ⟨y, ω⟩ _
        simp
      · intro ω _
        exact Fin.cons_self_tail ω
      · rintro ⟨y, ω⟩ _
        rfl
    have hcard_eq : ∀ (u : Finset (Fin (R + 1) → Ω)), (u.card : ℝ) = ∑ ω ∈ u, (1 : ℝ) := by
      intro u; simp
    rw [hcard_eq, hcard_eq, Finset.sum_filter, hpi, hpi]
    have inner : ∀ y ∈ s 0, ∑ ω ∈ T, (if Reaches D x (Fin.cons y ω) then (1 : ℝ) else 0) ≤
        Real.exp (-(θ * x)) * (Real.exp (θ * D 0 y) * (T.card : ℝ)) := by
      intro y _
      have hih := ih (fun r => s r.succ) (fun r => D r.succ) (fun r => hD r.succ) (x - D 0 y)
      have hcT : (T.card : ℝ) = ∑ ω ∈ T, (1 : ℝ) := by simp
      calc ∑ ω ∈ T, (if Reaches D x (Fin.cons y ω) then (1 : ℝ) else 0)
          = (((T.filter (Reaches (fun r => D r.succ) (x - D 0 y))).card : ℝ)) := by
            rw [Finset.card_filter]
            push_cast
            refine Finset.sum_congr rfl fun ω _ => ?_
            have := reaches_cons D x y ω
            by_cases h1 : Reaches (fun r => D r.succ) (x - D 0 y) ω
            · rw [if_pos (this.2 (Or.inr h1)), if_pos h1]
            · have h2 : ¬ Reaches D x (Fin.cons y ω) := by
                rw [this]; push_neg; exact ⟨hx, h1⟩
              rw [if_neg h2, if_neg h1]
        _ ≤ Real.exp (-(θ * (x - D 0 y))) * ((T.card : ℝ)) := hih
        _ = Real.exp (-(θ * x)) * (Real.exp (θ * D 0 y) * (T.card : ℝ)) := by
            rw [← mul_assoc, ← Real.exp_add]; congr 2; ring
    calc ∑ y ∈ s 0, ∑ ω ∈ T, (if Reaches D x (Fin.cons y ω) then (1 : ℝ) else 0)
        ≤ ∑ y ∈ s 0, Real.exp (-(θ * x)) * (Real.exp (θ * D 0 y) * (T.card : ℝ)) :=
          Finset.sum_le_sum inner
      _ = Real.exp (-(θ * x)) * ((∑ y ∈ s 0, Real.exp (θ * D 0 y)) * (T.card : ℝ)) := by
          rw [← Finset.mul_sum, ← Finset.sum_mul]
      _ ≤ Real.exp (-(θ * x)) * (((s 0).card : ℝ) * (T.card : ℝ)) := by
          gcongr
          exact hD 0
      _ = Real.exp (-(θ * x)) * ∑ y ∈ s 0, ∑ _ω ∈ T, (1 : ℝ) := by
          simp [Finset.sum_const]

end Ville
