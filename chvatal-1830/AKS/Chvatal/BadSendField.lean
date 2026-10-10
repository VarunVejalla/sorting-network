module
public import AKS.Chvatal.KernelSetup
public import AKS.Chvatal.BadSendReal
public import AKS.Chvatal.Lemma41Real
public import AKS.Chvatal.Wires31
public import Mathlib.Analysis.Complex.ExponentialBounds

@[expose] public section

namespace Chvatal

open Finset
open scoped Classical

theorem paperOrdinaryEpsB_le : paperOrdinaryEpsB ≤ (1 / 80000000 : ℝ) := by
  unfold paperOrdinaryEpsB
  have hl := Real.log_two_lt_d9
  rw [div_le_iff₀ (by positivity)]
  calc Real.sqrt (1 + 59 * Real.log 2) ≤ (2 : ℝ) ^ 29 / 80000000 := by
        rw [Real.sqrt_le_iff]; refine ⟨by positivity, ?_⟩; norm_num; nlinarith
    _ = 1 / 80000000 * (2 : ℝ) ^ 29 := by ring

theorem siblingFactor_real_nonneg : 0 ≤ siblingFactor := by
  unfold siblingFactor invDelta; norm_num

theorem slackCoeff_nonneg : 0 ≤ slackCoeff := by
  unfold slackCoeff; norm_num

theorem sibling_m_nonneg (c : ℚ) (hc : 0 ≤ c) :
    0 ≤ invMu * siblingFactor * c :=
  mul_nonneg (mul_nonneg invMu_pos.le siblingFactor_real_nonneg) hc

theorem delta_sq_lt_one :
    invDelta ^ 2 * (64 : ℚ) ^ 2 * (4096 : Rat) ^ 2 < 1 := by
  unfold invDelta; norm_num

/-- The statement of `BadSendField` for one child `b`. -/
def BadSendAt {d : ℕ} (hd : 7 ≤ d)
    (nets : ℕ → (b : KBag 64 d) → (n : ℕ) → ComparatorNetwork n)
    (v : Equiv.Perm (Fin (64 ^ d))) (t : ℕ) (ht : t ≤ tf7 d) (b : KBag 64 d) (hb : 1 ≤ b.l) :
    Prop :=
  ((b.strangers 1 id (fromParentK (flowSizes7 d hd) nets v t b) : ℕ) : ℚ) ≤
    parentOutMass d (execPlacement (flowSizes7 d hd) nets v t ht) id b hb +
      sibMassBound d t b hb +
      invEpsB * capacity d (b.l - 1) t +
      slackBound d t b hb

/-- Lemma 4.1 for occupied node. -/
theorem hM_keys {d : ℕ} (hd : 7 ≤ d)
    (nets : ℕ → (b : KBag 64 d) → (n : ℕ) → ComparatorNetwork n)
    (v : Equiv.Perm (Fin (64 ^ d))) (t : ℕ) (ht2 : 2 ≤ t) (htt : t ≤ tf7 d)
    (hP : OutsiderBoundLe d t
      (execPlacement (flowSizes7 d hd) nets v t htt) id)
    (q : KBag 64 d) (hq : q.l < d) (hα : alpha7 d t ≤ q.l) (hω : q.l < omega7 d t)
    (hpar : q.l % 2 = t % 2) (j' : Fin 64) :
    ((((execPlacement (flowSizes7 d hd) nets v t htt).regs q).filter fun κ =>
        (q.child j'.val j'.isLt hq).Native κ id).card : ℚ) ≤
      capacity d q.l t / 64 +
        invMu * siblingFactor * capacity d q.l t := by
  have h := keys_below_child_le d t
    (execPlacement (flowSizes7 d hd) nets v t htt) (fun l => (flowSizes7 d hd).a l t)
    (fun b => execPlacement_card _ nets v t htt b) (hpar7 d hd t (by omega) htt) hP
    delta_sq_lt_one q hq j' (hwires7 d hd t ht2 htt q.l hα hω hpar) hpar
  exact h

/-- Trivial Lemma 4.1 bound. -/
theorem hM_pow {d : ℕ} (hd : 7 ≤ d)
    (nets : ℕ → (b : KBag 64 d) → (n : ℕ) → ComparatorNetwork n)
    (v : Equiv.Perm (Fin (64 ^ d))) (t : ℕ) (htt : t ≤ tf7 d)
    (q : KBag 64 d) (hq : q.l < d) (j' : Fin 64) :
    ((((execPlacement (flowSizes7 d hd) nets v t htt).regs q).filter fun κ =>
        (q.child j'.val j'.isLt hq).Native κ id).card : ℚ) ≤ (64 : ℚ) ^ (d - q.l - 1) := by
  have h := keys_below_child_le_pow d (execPlacement (flowSizes7 d hd) nets v t htt) q hq j'
  exact_mod_cast h

/-- **BadSendField for real network** (Lemma 4.2, order 0).  Uniform in the node type: only
`node_facts` (with the deficit `Δ`, `ρ = Δ + m`) is used. -/
theorem badSendField_real {d : ℕ} (hd : 7 ≤ d)
    (nets : ℕ → (b : KBag 64 d) → (n : ℕ) → ComparatorNetwork n)
    (hspecs : RealSpecs hd nets) (v : Equiv.Perm (Fin (64 ^ d))) (t : ℕ) (ht1 : 1 ≤ t)
    (ht : t + 1 ≤ tf7 d)
    (hP : OutsiderBoundLe d t
      (execPlacement (flowSizes7 d hd) nets v t (by omega)) id) :
    BadSendField hd nets v t (by omega) := by
  intro b hb
  obtain ⟨q, hqlt, j, rfl⟩ := exists_parent_child b hb
  show BadSendAt hd nets v t (by omega) _ hb
  have htt : t < tf7 d := by omega
  have hk : ((64 : ℚ) - 1) = 63 := by norm_num
  have hm0 := sibling_m_nonneg _ (capacity_nonneg d q.l t)
  by_cases hd0 : (flowSizes7 d hd).down q.l t = 0
  · -- nothing is sent down
    have hemp := fromParentK_eq_empty hd nets v t (q.child j.val j.isLt hqlt) hd0
    have := invEpsB_nonneg
    have := invMu_pos.le
    have := siblingFactor_real_nonneg
    have := slackCoeff_nonneg
    have := capacity_nonneg d ((q.child j.val j.isLt hqlt).l - 1) t
    unfold BadSendAt parentOutMass sibMassBound slackBound
    rw [hemp, hk]
    simp [KBag.strangers]
    positivity
  obtain ⟨Δ, hF, -, hMs⟩ := node_facts d hd t q.l ht1 htt (Nat.pos_of_ne_zero hd0)
  have hM : ∀ j' : Fin 64,
      ((((execPlacement (flowSizes7 d hd) nets v t (by omega)).regs q).filter fun κ =>
        (q.child j'.val j'.isLt hqlt).Native κ id).card : ℚ) ≤
          ((flowSizes7 d hd).down q.l t : ℚ) +
            (Δ + invMu * siblingFactor * capacity d q.l t) := fun j' => by
    rcases hMs with ⟨⟨ht2, hα, hω, hpar⟩, h⟩ | h
    · linarith [hM_keys hd nets v t ht2 htt.le hP q hqlt hα hω hpar j']
    · linarith [hM_pow hd nets v t htt.le q hqlt j']
  have hout : (0 : ℚ) ≤ (q.strangers 1 id ((execPlacement (flowSizes7 d hd) nets v t (by omega)).regs q)
      : ℕ) := Nat.cast_nonneg _
  have hbad := bad_send0_real (flowSizes7 d hd) nets v t htt q hqlt j
    (specEB t ((flowSizes7 d hd).a q.l t)) (specJmax ((flowSizes7 d hd).up q.l t)) eps
    ((Δ + invMu * siblingFactor * capacity d q.l t : ℚ) : ℝ)
    (by exact_mod_cast add_nonneg hF.nonneg hm0) (hspecs t q htt (Nat.pos_of_ne_zero hd0))
    (fun j' => by exact_mod_cast (Rat.cast_le (K := ℝ)).mpr (hM j'))
    (by
      have := (Rat.cast_le (K := ℝ)).mpr
        (show ((flowSizes7 d hd).up q.l t : ℚ) / 2 ≤
          (q.strangers 1 id ((execPlacement (flowSizes7 d hd) nets v t (by omega)).regs q)
            : ℚ) + 63 * (Δ + invMu * siblingFactor * capacity d q.l t) by
          linarith [hF.half])
      push_cast at this ⊢; exact this)
  have hslR := (Rat.cast_le (K := ℝ)).mpr
    (show 63 * (Δ + invMu * siblingFactor * capacity d q.l t) - ((flowSizes7 d hd).up q.l t : ℚ) / 2 ≤
        63 * (invMu * siblingFactor * capacity d q.l t) + slackCoeff * capacity d q.l t by
      linarith [hF.slack])
  push_cast at hslR hbad
  have hael : (((flowSizes7 d hd).a q.l t : ℕ) : ℝ) ≤ ((capacity d q.l t : ℚ) : ℝ) := by
    exact_mod_cast hF.a_le
  have hEB : 2 * specEB t ((flowSizes7 d hd).a q.l t) ≤
      (1 / 80000000 : ℝ) * ((capacity d q.l t : ℚ) : ℝ) := by
    unfold specEB
    rw [if_neg (by omega)]
    have h1 := paperOrdinaryEpsB_le
    have h2 : (0 : ℝ) ≤ (((flowSizes7 d hd).a q.l t : ℕ) : ℝ) := Nat.cast_nonneg _
    nlinarith
  have e2 : (q.child j.val j.isLt hqlt).parent = q :=
    KBag.parent_child' q j.val j.isLt hqlt
  unfold BadSendAt parentOutMass sibMassBound slackBound
  rw [← Rat.cast_le (K := ℝ)]
  simp only [show (q.child j.val j.isLt hqlt).l - 1 = q.l from rfl, e2, hk]
  push_cast
  have hepsB : ((invEpsB : ℚ) : ℝ) = 1 / 80000000 := by simp [invEpsB]
  rw [hepsB]
  refine le_trans hbad ?_
  change _ ≤ (((q.strangers 1 id ((execPlacement (flowSizes7 d hd) nets v t (by omega)).regs q)
    : ℕ) : ℝ)) + _ + _ + _
  linarith

end Chvatal
