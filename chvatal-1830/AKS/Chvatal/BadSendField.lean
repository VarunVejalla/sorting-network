module
public import AKS.Chvatal.KernelSetup
public import AKS.Chvatal.BadSendReal
public import AKS.Chvatal.Lemma41Real
public import AKS.Chvatal.Wires31
public import Mathlib.Analysis.Complex.ExponentialBounds

@[expose] public section

/-! The real-network `BadSendField` (Chvátal, Lemma 4.2 order 0 and §7): `badSendField_real`. -/

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

theorem siblingFactor_real_nonneg : 0 ≤ siblingFactor params7 invariantReal := by
  unfold siblingFactor params7 invariantReal invariant7; norm_num

theorem sibling_m_nonneg (c : ℚ) (hc : 0 ≤ c) :
    0 ≤ invariantReal.mu * siblingFactor params7 invariantReal * c :=
  mul_nonneg (mul_nonneg invariantReal.hmu_pos.le siblingFactor_real_nonneg) hc

theorem delta_sq_lt_one :
    invariantReal.delta ^ 2 * ((params7.br : ℕ) : ℚ) ^ 2 * params7.A ^ 2 < 1 := by
  unfold invariantReal invariant7 params7; norm_num

theorem capacity_one_one (d : ℕ) : capacity params7 d 1 1 = 64 ^ d / 64 := by
  unfold capacity params7
  simp only [Nat.cast_pow]
  push_cast
  field_simp

/-- `a ≤ c` for `t ≥ 1`. -/
theorem a_le_cap (d : ℕ) (hd : 7 ≤ d) (l t : ℕ) (ht1 : 1 ≤ t) (ht : t ≤ tf7 d) :
    (flowA7 d hd l t : ℚ) ≤ capacity params7 d l t := by
  have hc0 := capacity_params7_nonneg d l t
  by_cases h1 : t = 1
  · subst h1
    unfold flowA7
    rw [if_neg (by omega), if_pos rfl]
    split_ifs with hl
    · subst hl
      rw [capacity_one_one]
      have : (64 : ℚ) ^ d = 64 ^ (d - 1) * 64 := by rw [← pow_succ]; congr 1; omega
      push_cast
      rw [this]; field_simp; exact le_refl _
    · simpa using hc0
  · have ht2 : 2 ≤ t := by omega
    rw [cast_flowA7 d hd l t ht2 ht]
    by_cases hact : t ≤ tf7 d ∧ alpha7 d t ≤ l ∧ l ≤ omega7 d t ∧ l % 2 = t % 2
    swap
    · rw [allocation_inactive _ _ _ _ _ hact]; exact hc0
    by_cases hα : l = alpha7 d t
    · rw [alloc_top params7 d (levelSchedule7 d hd) hact hα]
    · by_cases hω : l = omega7 d t
      · rw [alloc_bot params7 d (levelSchedule7 d hd) hact hα hω]
        have hb := omega7_bounds d t ht2
        have hωd := omega7_le_d d t hd ht
        obtain ⟨e, he⟩ : ∃ e, d + 2 * l = t + 2 + e := ⟨d + 2 * l - (t + 2), by omega⟩
        rw [capacity_params7 d l t e he]
        have hQ : (0 : ℚ) < capacityRatio params7 := capacityRatio_pos params7
        have h64 : (((params7.br ^ d : ℕ)) : ℚ) / ((params7.br : ℕ) : ℚ) ^ l = 64 ^ (d - l) := by
          simp only [params7, Nat.cast_pow]
          push_cast
          rw [div_eq_iff (by positivity), ← pow_add]; congr 1; omega
        simp only [Nat.cast_pow] at h64 ⊢
        have : ((64 : ℚ)) ^ (d - l) ≤ 64 ^ e := pow_le_pow_right₀ (by norm_num) (by omega)
        have hpos : 0 ≤ ((64 : ℚ) ^ e) / capacityRatio params7 := by positivity
        rw [params7_br] at h64 ⊢
        simp only [Nat.cast_ofNat] at h64 ⊢
        linarith
      · rw [alloc_mid params7 d (levelSchedule7 d hd) hact hα hω]
        have hQ : 1 ≤ capacityRatio params7 := by rw [capacityRatio_params7]; norm_num
        have : 0 ≤ 1 / capacityRatio params7 := by positivity
        nlinarith

/-- The statement of `BadSendField` for one child `b`. -/
def BadSendAt {d : ℕ} (hd : 7 ≤ d)
    (nets : ℕ → (b : KBag 64 d) → (n : ℕ) → ComparatorNetwork n)
    (v : Equiv.Perm (Fin (64 ^ d))) (t : ℕ) (ht : t ≤ tf7 d) (b : KBag 64 d) (hb : 1 ≤ b.l) :
    Prop :=
  ((b.strangers 1 id (fromParentK (flowSizes7 d hd) nets v t b) (br_ge_one params7) : ℕ) : ℚ) ≤
    parentOutMass params7 d (execPlacement (flowSizes7 d hd) nets v t ht) id b hb +
      sibMassBound params7 invariantReal d t b hb +
      invariantReal.epsB * capacity params7 d (b.l - 1) t +
      slackBound params7 d t b hb

/-- Node shapes (`π = 0`; rising top; interior/bottom-desc) reduce `BadSendAt` to a Lemma 4.1
bound `hM` with the matching `ρ`; uses `bad_send0_real`. -/
theorem badSend_shape {d : ℕ} (hd : 7 ≤ d)
    (nets : ℕ → (b : KBag 64 d) → (n : ℕ) → ComparatorNetwork n)
    (hspecs : RealSpecs hd nets) (v : Equiv.Perm (Fin (64 ^ d))) (t : ℕ) (ht1 : 1 ≤ t)
    (ht : t + 1 ≤ tf7 d) (q b : KBag 64 d) (hq : q.l < d) (j : Fin 64)
    (hbq : q.child j.val j.isLt hq = b) (hb : 1 ≤ b.l) (ρ : ℚ)
    (hdown : 0 < (flowSizes7 d hd).down q.l t)
    (hshape :
      (((flowSizes7 d hd).up q.l t : ℚ) = 0 ∧
        ρ = invariantReal.mu * siblingFactor params7 invariantReal * capacity params7 d q.l t) ∨
      (((flowSizes7 d hd).up q.l t : ℚ) =
          params7.nu * capacity params7 d q.l t / (params7.A * 64) ∧
        ρ = delta2_7 (capacity params7 d q.l t) +
          invariantReal.mu * siblingFactor params7 invariantReal * capacity params7 d q.l t) ∨
      (((flowSizes7 d hd).up q.l t : ℚ) =
          (params7.A * params7.nu * 64 - 1) * capacity params7 d q.l t / capacityRatio params7 ∧
        ρ = delta2_7 (capacity params7 d q.l t) +
          invariantReal.mu * siblingFactor params7 invariantReal * capacity params7 d q.l t))
    (hM : ∀ j' : Fin 64,
      ((((execPlacement (flowSizes7 d hd) nets v t (by omega)).regs q).filter fun κ =>
        (q.child j'.val j'.isLt hq).Native κ id).card : ℚ) ≤
          ((flowSizes7 d hd).down q.l t : ℚ) + ρ) :
    BadSendAt hd nets v t (by omega) b hb := by
  subst hbq
  have hc0 := capacity_params7_nonneg d q.l t
  have hm0 := sibling_m_nonneg _ hc0
  have hΔ : 0 ≤ delta2_7 (capacity params7 d q.l t) := by rw [delta2_7_eq]; positivity
  have hk : (((params7.br : ℕ) : ℚ) - 1) = 63 := by rw [params7_br]; norm_num
  have hρ : 0 ≤ ρ := by rcases hshape with ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ <;> rw [h] <;> linarith
  have hmid := slack_mid invariantReal (capacity params7 d q.l t)
  have hrise := slack_top_rise invariantReal (capacity params7 d q.l t) hc0
  rw [hk] at hmid hrise
  have hs0 : 0 ≤ slackCoeff params7 * capacity params7 d q.l t := mul_nonneg slackCoeff7_nonneg hc0
  have hout : (0 : ℚ) ≤ (q.strangers 1 id ((execPlacement (flowSizes7 d hd) nets v t (by omega)).regs q)
      (br_ge_one params7) : ℕ) := Nat.cast_nonneg _
  have htt : t < tf7 d := by omega
  have hρR : (0 : ℝ) ≤ (ρ : ℝ) := by exact_mod_cast hρ
  have hpos : ((flowSizes7 d hd).up q.l t : ℚ) / 2 ≤
      (q.strangers 1 id ((execPlacement (flowSizes7 d hd) nets v t (by omega)).regs q)
        (br_ge_one params7) : ℚ) + 63 * ρ := by
    rcases hshape with ⟨hu, h⟩ | ⟨hu, h⟩ | ⟨hu, h⟩ <;> rw [hu, h]
    · linarith
    · rw [delta2_7_eq, show params7.nu = 1 / 64 from rfl, show params7.A = 4096 from rfl]; nlinarith
    · linarith
  have hslack : 63 * ρ - ((flowSizes7 d hd).up q.l t : ℚ) / 2 ≤
      63 * (invariantReal.mu * siblingFactor params7 invariantReal * capacity params7 d q.l t) +
        slackCoeff params7 * capacity params7 d q.l t := by
    rcases hshape with ⟨hu, h⟩ | ⟨hu, h⟩ | ⟨hu, h⟩ <;> rw [hu, h] <;> linarith
  have hbad := bad_send0_real (flowSizes7 d hd) nets v t htt q hq j
    (specEB t ((flowSizes7 d hd).a q.l t)) (specJmax ((flowSizes7 d hd).up q.l t)) eps (ρ : ℝ)
    hρR (hspecs t q htt hdown)
    (fun j' => by exact_mod_cast (Rat.cast_le (K := ℝ)).mpr (hM j'))
    (by have := (Rat.cast_le (K := ℝ)).mpr hpos; push_cast at this; exact this)
  have hslR := (Rat.cast_le (K := ℝ)).mpr hslack
  push_cast at hslR
  have hael : (((flowSizes7 d hd).a q.l t : ℕ) : ℝ) ≤ ((capacity params7 d q.l t : ℚ) : ℝ) := by
    exact_mod_cast a_le_cap d hd q.l t ht1 htt.le
  have hEB : 2 * specEB t ((flowSizes7 d hd).a q.l t) ≤
      (1 / 80000000 : ℝ) * ((capacity params7 d q.l t : ℚ) : ℝ) := by
    unfold specEB
    rw [if_neg (by omega)]
    have h1 := paperOrdinaryEpsB_le
    have h2 : (0 : ℝ) ≤ (((flowSizes7 d hd).a q.l t : ℕ) : ℝ) := Nat.cast_nonneg _
    nlinarith
  have e2 : @KBag.parent params7.br d (q.child j.val j.isLt hq) (br_ge_one params7) = q :=
    KBag.parent_child' q j.val j.isLt hq
  unfold BadSendAt parentOutMass sibMassBound slackBound
  rw [← Rat.cast_le (K := ℝ)]
  simp only [show (q.child j.val j.isLt hq).l - 1 = q.l from rfl, e2, hk]
  push_cast
  have hepsB : ((invariantReal.epsB : ℚ) : ℝ) = 1 / 80000000 := by simp [invariantReal]
  rw [hepsB]
  refine le_trans hbad ?_
  change _ ≤ (((q.strangers 1 id ((execPlacement (flowSizes7 d hd) nets v t (by omega)).regs q)
    (br_ge_one params7) : ℕ) : ℝ)) + _ + _ + _
  linarith

/-- Lemma 4.1 (`keys_below_child_le`) for an occupied node `q` with `α ≤ q.l < ω`, `t ≥ 2`. -/
theorem hM_keys {d : ℕ} (hd : 7 ≤ d)
    (nets : ℕ → (b : KBag 64 d) → (n : ℕ) → ComparatorNetwork n)
    (v : Equiv.Perm (Fin (64 ^ d))) (t : ℕ) (ht2 : 2 ≤ t) (htt : t ≤ tf7 d)
    (hP : OutsiderBoundLe params7 invariantReal d (levelSchedule7 d hd) t
      (execPlacement (flowSizes7 d hd) nets v t htt) id)
    (q : KBag 64 d) (hq : q.l < d) (hα : alpha7 d t ≤ q.l) (hω : q.l < omega7 d t)
    (hpar : q.l % 2 = t % 2) (j' : Fin 64) :
    ((((execPlacement (flowSizes7 d hd) nets v t htt).regs q).filter fun κ =>
        (q.child j'.val j'.isLt hq).Native κ id).card : ℚ) ≤
      capacity params7 d q.l t / 64 +
        invariantReal.mu * siblingFactor params7 invariantReal * capacity params7 d q.l t := by
  have h := keys_below_child_le params7 invariantReal d (levelSchedule7 d hd) t
    (execPlacement (flowSizes7 d hd) nets v t htt) (fun l => (flowSizes7 d hd).a l t)
    (fun b => execPlacement_card _ nets v t htt b) (hpar7 d hd t (by omega) htt) hP
    delta_sq_lt_one q hq j' (hwires7_real d hd t ht2 htt q.l hα hω hpar) hpar
  rwa [params7_br] at h

/-- The trivial Lemma 4.1 bound `k^(d-l-1)`. -/
theorem hM_pow {d : ℕ} (hd : 7 ≤ d)
    (nets : ℕ → (b : KBag 64 d) → (n : ℕ) → ComparatorNetwork n)
    (v : Equiv.Perm (Fin (64 ^ d))) (t : ℕ) (htt : t ≤ tf7 d)
    (q : KBag 64 d) (hq : q.l < d) (j' : Fin 64) :
    ((((execPlacement (flowSizes7 d hd) nets v t htt).regs q).filter fun κ =>
        (q.child j'.val j'.isLt hq).Native κ id).card : ℚ) ≤ (64 : ℚ) ^ (d - q.l - 1) := by
  have h := keys_below_child_le_pow params7 d (execPlacement (flowSizes7 d hd) nets v t htt) q hq j'
  exact_mod_cast h

/-- At `t = 1` the level-1 node has the rising-top sizes, with `τ + Δ₂ = 64^(d-2)`. -/
theorem t1_vals (d : ℕ) (hd : 7 ≤ d) :
    ((flowUp7 d hd 1 1 : ℕ) : ℚ) =
        params7.nu * capacity params7 d 1 1 / (params7.A * 64) ∧
      ((flowDown7 d hd 1 1 : ℕ) : ℚ) + delta2_7 (capacity params7 d 1 1) =
        (64 : ℚ) ^ (d - 1 - 1) := by
  obtain ⟨e, rfl⟩ : ∃ e, d = e + 7 := ⟨d - 7, by omega⟩
  have hle : 64 ^ (e + 7 - 6) ≤ 64 ^ (e + 7 - 2) :=
    Nat.pow_le_pow_right (by norm_num) (by omega : e + 7 - 6 ≤ e + 7 - 2)
  have hu : flowUp7 (e + 7) hd 1 1 = 64 ^ (e + 7 - 5) := by simp [flowUp7]
  have hdn : flowDown7 (e + 7) hd 1 1 = 64 ^ (e + 7 - 2) - 64 ^ (e + 7 - 6) := by simp [flowDown7]
  rw [hu, hdn, capacity_one_one, delta2_7_eq, Nat.cast_sub hle]
  rw [show params7.nu = 1 / 64 from rfl, show params7.A = 4096 from rfl,
    show e + 7 - 5 = e + 2 by omega, show e + 7 - 6 = e + 1 by omega,
    show e + 7 - 2 = e + 5 by omega, show e + 7 - 1 - 1 = e + 5 by omega]
  push_cast
  constructor <;> ring

/-- **`BadSendField` for the real network** (Lemma 4.2, order 0, §7 schedule). -/
theorem badSendField_real {d : ℕ} (hd : 7 ≤ d)
    (nets : ℕ → (b : KBag 64 d) → (n : ℕ) → ComparatorNetwork n)
    (hspecs : RealSpecs hd nets) (v : Equiv.Perm (Fin (64 ^ d))) (t : ℕ) (ht1 : 1 ≤ t)
    (ht : t + 1 ≤ tf7 d)
    (hP : OutsiderBoundLe params7 invariantReal d (levelSchedule7 d hd) t
      (execPlacement (flowSizes7 d hd) nets v t (by omega)) id) :
    BadSendField hd nets v t (by omega) := by
  intro b hb
  obtain ⟨q, hqlt, j, rfl⟩ := exists_parent_child b hb
  show BadSendAt hd nets v t (by omega) _ hb
  by_cases hd0 : (flowSizes7 d hd).down q.l t = 0
  · -- nothing is sent down
    have hemp := fromParentK_eq_empty hd nets v t (q.child j.val j.isLt hqlt) hd0
    have hk : (((params7.br : ℕ) : ℚ) - 1) = 63 := by rw [params7_br]; norm_num
    have := invariantReal.hmu_pos.le
    have := invariantReal.hepsB_nonneg
    have := siblingFactor_real_nonneg
    have := slackCoeff7_nonneg
    have := capacity_params7_nonneg d ((q.child j.val j.isLt hqlt).l - 1) t
    unfold BadSendAt parentOutMass sibMassBound slackBound
    rw [hemp, hk]
    simp [KBag.strangers]
    positivity
  have hdpos : 0 < (flowSizes7 d hd).down q.l t := Nat.pos_of_ne_zero hd0
  have key := badSend_shape hd nets hspecs v t ht1 ht q _ hqlt j rfl hb
  have hm0 := sibling_m_nonneg _ (capacity_params7_nonneg d q.l t)
  by_cases ht2 : 2 ≤ t
  · -- ordinary stage
    have htt : t < tf7 d := by omega
    by_cases hact : t ≤ tf7 d ∧ alpha7 d t ≤ q.l ∧ q.l ≤ omega7 d t ∧ q.l % 2 = t % 2
    swap
    · exfalso
      have h := cast_flowDown7 d hd q.l t ht2 htt
      rw [flowDown_inactive _ _ _ hact] at h
      have : (flowSizes7 d hd).down q.l t = 0 := by exact_mod_cast h
      omega
    obtain ⟨-, hαle, hωle, hpar⟩ := hact
    have hlt := alpha7_lt_omega7 d hd t ht2 htt
    have hp1 := alpha7_parity d t
    have hp2 := alpha7_parity d (t + 1)
    have hst := alpha7_step d t hd ht
    by_cases hα : q.l = alpha7 d t
    · have hM := hM_keys hd nets v t ht2 htt.le hP q hqlt hαle (by omega) hpar
      by_cases hs : alpha7 d t < alpha7 d (t + 1)
      · obtain ⟨hu, hdn⟩ := tau_top_desc d hd t ht2 htt q.l ⟨htt.le, hαle, hωle, hpar⟩ hα hs
        refine key _ hdpos (Or.inl ⟨hu, rfl⟩) fun j' => ?_
        rw [show (((flowSizes7 d hd).down q.l t : ℕ) : ℚ) = _ from hdn]; exact hM j'
      · obtain ⟨hu, hdn⟩ := tau_top_rise d hd t ht2 htt q.l ⟨htt.le, hαle, hωle, hpar⟩ hα (by omega)
        refine key _ hdpos (Or.inr (Or.inl ⟨hu, rfl⟩)) fun j' => ?_
        rw [show (((flowSizes7 d hd).down q.l t : ℕ) : ℚ) = _ from hdn]; linarith [hM j']
    · by_cases hω : q.l = omega7 d t
      · by_cases hs : omega7 d t < omega7 d (t + 1)
        · obtain ⟨hu, hdn⟩ := tau_bot_desc d hd t ht2 htt q.l ⟨htt.le, hαle, hωle, hpar⟩ hα hω hs
          refine key _ hdpos (Or.inr (Or.inr ⟨hu, rfl⟩)) fun j' => ?_
          have := hM_pow hd nets v t htt.le q hqlt j'
          have hdn' : (((flowSizes7 d hd).down q.l t : ℕ) : ℚ) +
              delta2_7 (capacity params7 d q.l t) = (64 : ℚ) ^ (d - q.l - 1) := hdn
          linarith
        · exfalso
          have h := cast_flowDown7 d hd q.l t ht2 htt
          rw [flowDown_bot_rise params7 d (levelSchedule7 d hd)
            ⟨htt.le, hαle, hωle, hpar⟩ hα hω hs] at h
          have : (flowSizes7 d hd).down q.l t = 0 := by exact_mod_cast h
          omega
      · have hM := hM_keys hd nets v t ht2 htt.le hP q hqlt hαle (by omega) hpar
        obtain ⟨hu, hdn⟩ := tau_mid d hd t ht2 htt q.l ⟨htt.le, hαle, hωle, hpar⟩ hα hω
        refine key _ hdpos (Or.inr (Or.inr ⟨hu, rfl⟩)) fun j' => ?_
        rw [show (((flowSizes7 d hd).down q.l t : ℕ) : ℚ) = _ from hdn]; linarith [hM j']
  · -- the special stage `t = 1`
    obtain rfl : t = 1 := by omega
    have hql1 : q.l = 1 := by
      by_contra hne
      apply hd0
      show flowDown7 d hd q.l 1 = 0
      unfold flowDown7
      rw [if_neg (by omega), if_pos rfl, if_neg hne]
    obtain ⟨hu, hdn⟩ := t1_vals d hd
    have hdn' : (((flowSizes7 d hd).down q.l 1 : ℕ) : ℚ) + delta2_7 (capacity params7 d q.l 1) =
        (64 : ℚ) ^ (d - q.l - 1) := by rw [hql1]; exact hdn
    refine key _ hdpos (Or.inr (Or.inl ⟨by rw [hql1]; exact hu, rfl⟩)) fun j' => ?_
    have := hM_pow hd nets v 1 (by omega) q hqlt j'
    linarith

end Chvatal
