module

public import AKS.Chvatal.KernelSetup
public import AKS.Chvatal.BadSendReal
public import AKS.Chvatal.Lemma41Real
public import AKS.Chvatal.Schedule7

@[expose] public section

/-! The root step `P_one` (Lemma 4.3 root case, exceptional separator), the induction `P_all` and
purity `real_purity` (level `d - 6` at `t = tf7 d`) for the real network (`params7`,
`invariantReal`, `levelSchedule7`, execution-defined placements with `perm = id`). -/

namespace Chvatal

open Finset
open scoped Classical

theorem one_le_tf7 {d : ℕ} (hd : 7 ≤ d) : 1 ≤ tf7 d := by unfold tf7; omega

/-- The right-hand side of the outsider invariant is nonnegative. -/
theorem outsider_rhs_nonneg (d r l t : ℕ) :
    (0 : ℚ) ≤ invariantReal.mu * invariantReal.delta ^ r * capacity params7 d l t := by
  have h1 := invariantReal.hmu_pos
  have h2 := invariantReal.hdelta_pos
  have h3 := capacity_pos params7 d l t
  positivity

/-- `ε_* ≤ μ/64` numerically: `√(1+79 log 2)/2^39 ≈ 1.36e-11 ≤ 1023/2^46 ≈ 1.45e-11`. -/
theorem paperRootEpsB_le_epsStar :
    paperRootEpsB ≤ ((invariantReal.epsStar : ℚ) : ℝ) := by
  have hl := Real.log_two_lt_d9
  have hs : Real.sqrt (1 + 79 * Real.log 2) ≤ 1023 / 128 := by
    rw [Real.sqrt_le_iff]
    refine ⟨by norm_num, ?_⟩
    norm_num at hl ⊢
    linarith
  unfold paperRootEpsB invariantReal
  push_cast
  rw [div_le_iff₀ (by positivity)]
  norm_num at hs ⊢
  linarith

variable {d : ℕ}

set_option linter.constructorNameAsVariable false in
/-- The root step (Lemma 4.3, root case, exceptional separator). -/
theorem P_one (hd : 7 ≤ d)
    (nets : ℕ → (b : KBag 64 d) → (n : ℕ) → ComparatorNetwork n)
    (hspecs : RealSpecs hd nets)
    (v : Equiv.Perm (Fin (64 ^ d))) :
    OutsiderBoundLe params7 invariantReal d (levelSchedule7 d hd) 1
      (execPlacement (flowSizes7 d hd) nets v 1 (one_le_tf7 hd)) id := by
  show ∀ (b : KBag 64 d) (r : ℕ), r ≤ d →
    (((b.strangers (r + 1) id
      ((execPlacement (flowSizes7 d hd) nets v 1 (one_le_tf7 hd)).regs b)
      (by norm_num : 1 ≤ 64) : ℕ) : ℚ)) ≤
      invariantReal.mu * invariantReal.delta ^ r * capacity params7 d b.l 1
  intro b r hr
  have h1 := one_le_tf7 hd
  have hrhs := outsider_rhs_nonneg d r b.l 1
  by_cases hl : b.l = 1
  swap
  · have hE : (execPlacement (flowSizes7 d hd) nets v 1 h1).regs b = ∅ :=
      Finset.card_eq_zero.mp ((execPlacement_card (flowSizes7 d hd) nets v 1 h1 b).trans (by
        show flowA7 d hd b.l 1 = 0
        unfold flowA7
        simp [hl]))
    rw [hE, KBag.strangers_empty]
    simpa using hrhs
  rcases Nat.eq_zero_or_pos r with hr0 | hr0
  swap
  · rw [KBag.strangers_eq_zero_of_lt_order b (r + 1) id _ (by norm_num : 1 ≤ 64) (by omega) (by omega)]
    simpa using hrhs
  subst hr0
  -- main case: level-1 bag, order 0
  have hbl : b.l < d := by omega
  have hroot : (KBag.root 64 d).l < d := by show 0 < d; omega
  have hjx : b.x < 64 := by simpa [hl] using b.hx
  have hbj : b = (KBag.root 64 d).child b.x hjx hroot :=
    KBag.ext (by simp [KBag.child, KBag.root, hl]) (by simp [KBag.child, KBag.root])
  have ht0 : 0 < tf7 d := by omega
  have hchE : fromChildrenK (flowSizes7 d hd) nets v 0 b = ∅ := by
    unfold fromChildrenK
    rw [dif_pos hbl]
    refine Finset.eq_empty_of_forall_notMem fun k hk => ?_
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and] at hk
    obtain ⟨j, hj⟩ := hk
    have hne : b.child j.val j.isLt hbl ≠ KBag.root 64 d := fun h => by
      simpa [KBag.child, KBag.root] using congrArg KBag.l h
    rw [wireSets_zero_of_ne _ hne] at hj
    simp [upSet, blockOf] at hj
  have hregs : (execPlacement (flowSizes7 d hd) nets v 1 h1).regs b =
      fromParentK (flowSizes7 d hd) nets v 0 b := by
    rw [show (execPlacement (flowSizes7 d hd) nets v 1 h1).regs b =
        (execPlacement (flowSizes7 d hd) nets v (0 + 1) ht0).regs b from rfl,
      execPlacement_succ_regs (flowSizes7 d hd) nets v 0 ht0 b (by omega), hchE, Finset.union_empty]
  -- apply bad_send0_real at t = 0, q = root
  have hdown : (flowSizes7 d hd).down (KBag.root 64 d).l 0 = 64 ^ (d - 1) := by
    simp [flowSizes7, flowDown7, KBag.root]
  have hup : (flowSizes7 d hd).up (KBag.root 64 d).l 0 = 0 := by
    simp [flowSizes7, flowUp7, KBag.root]
  have ha0 : (flowSizes7 d hd).a (KBag.root 64 d).l 0 = 64 ^ d := by
    simp [flowSizes7, flowA7, KBag.root]
  have hM : ∀ j' : Fin 64,
      ((((execPlacement (flowSizes7 d hd) nets v 0 ht0.le).regs (KBag.root 64 d)).filter fun κ =>
        ((KBag.root 64 d).child j'.val j'.isLt hroot).Native κ id).card : ℝ) ≤
        ((flowSizes7 d hd).down (KBag.root 64 d).l 0 : ℝ) + 0 := by
    intro j'
    have hle := (Finset.card_le_card (Finset.filter_subset_filter _ (Finset.subset_univ
      ((execPlacement (flowSizes7 d hd) nets v 0 ht0.le).regs (KBag.root 64 d))))).trans_eq
      (native_card (br := 64) (d := d) (by norm_num) ((KBag.root 64 d).child j'.val j'.isLt hroot))
    rw [hdown, add_zero]
    exact_mod_cast hle
  have hroot0 : (KBag.root 64 d).strangers 1 id
      ((execPlacement (flowSizes7 d hd) nets v 0 ht0.le).regs (KBag.root 64 d))
        (by norm_num : 1 ≤ 64) = 0 :=
    KBag.strangers_eq_zero_of_lt_order _ 1 id _ (by norm_num : 1 ≤ 64) le_rfl (by
      show 0 < 1; omega)
  have hbad := bad_send0_real (flowSizes7 d hd) nets v 0 ht0 (KBag.root 64 d) hroot
    ⟨b.x, hjx⟩ (specEB 0 ((flowSizes7 d hd).a (KBag.root 64 d).l 0))
    (specJmax ((flowSizes7 d hd).up (KBag.root 64 d).l 0)) eps 0 le_rfl
    (hspecs 0 (KBag.root 64 d) ht0 (by rw [hdown]; positivity)) hM
    (by rw [hup, hroot0]; simp)
  rw [hroot0, ← hbj, ha0, hup] at hbad
  have hEB : specEB 0 (64 ^ d) = paperRootEpsB * (64 : ℝ) ^ d / 2 := by simp [specEB]
  rw [hEB] at hbad
  have hcap : capacity params7 d b.l 1 = (64 : ℚ) ^ (d - 1) := by
    rw [hl]
    obtain ⟨e, rfl⟩ : ∃ e, d = e + 1 := ⟨d - 1, by omega⟩
    simp only [capacity, params7, Nat.add_sub_cancel]
    push_cast
    rw [pow_succ]
    field_simp
  have hεle := paperRootEpsB_le_epsStar
  have hpd : (64 : ℝ) ^ d = 64 * 64 ^ (d - 1) := by
    obtain ⟨e, rfl⟩ : ∃ e, d = e + 1 := ⟨d - 1, by omega⟩
    simp [pow_succ]; ring
  have hμ : (invariantReal.epsStar : ℝ) * 64 = (invariantReal.mu : ℝ) := by
    unfold invariantReal; push_cast; norm_num
  have hb2 : ((b.strangers 1 id (fromParentK (flowSizes7 d hd) nets v 0 b) : ℕ) : ℝ) ≤
      paperRootEpsB * (64 : ℝ) ^ d := by
    push_cast at hbad; refine hbad.trans (le_of_eq ?_); ring
  have key : ((b.strangers 1 id (fromParentK (flowSizes7 d hd) nets v 0 b) : ℕ) : ℝ) ≤
      (invariantReal.mu : ℝ) * ((64 : ℝ) ^ (d - 1)) :=
    calc _ ≤ paperRootEpsB * (64 : ℝ) ^ d := hb2
      _ = paperRootEpsB * (64 * 64 ^ (d - 1)) := by rw [hpd]
      _ ≤ (invariantReal.epsStar : ℝ) * (64 * 64 ^ (d - 1)) :=
          mul_le_mul_of_nonneg_right hεle (by positivity)
      _ = (invariantReal.mu : ℝ) * ((64 : ℝ) ^ (d - 1)) := by rw [← hμ]; ring
  rw [hregs, hcap, pow_zero, mul_one]
  rw [← Rat.cast_le (K := ℝ)]
  push_cast
  exact key

/-- The stage kernels of the real network, as supplied to the induction. -/
abbrev KernelFamily {d : ℕ} (hd : 7 ≤ d)
    (nets : ℕ → (b : KBag 64 d) → (n : ℕ) → ComparatorNetwork n)
    (v : Equiv.Perm (Fin (64 ^ d))) : Type :=
  ∀ t, 1 ≤ t → ∀ (ht : t + 1 ≤ tf7 d),
    OutsiderBoundLe params7 invariantReal d (levelSchedule7 d hd) t
      (execPlacement (flowSizes7 d hd) nets v t (by omega)) id →
    StageKernel params7 invariantReal d (levelSchedule7 d hd) t
      (execPlacement (flowSizes7 d hd) nets v t (by omega)) id
      (execPlacement (flowSizes7 d hd) nets v (t + 1) ht) id

/-- The induction from `P_one`, using the stage kernels. -/
theorem P_all (hd : 7 ≤ d)
    (nets : ℕ → (b : KBag 64 d) → (n : ℕ) → ComparatorNetwork n)
    (hspecs : RealSpecs hd nets) (v : Equiv.Perm (Fin (64 ^ d))) (hK : KernelFamily hd nets v) :
    ∀ t, 1 ≤ t → ∀ (ht : t ≤ tf7 d),
      OutsiderBoundLe params7 invariantReal d (levelSchedule7 d hd) t
        (execPlacement (flowSizes7 d hd) nets v t ht) id := by
  intro t ht1
  induction t, ht1 using Nat.le_induction with
  | base => intro ht; exact P_one hd nets hspecs v
  | succ t ht1 ih =>
    intro ht
    have ht' : t ≤ tf7 d := by omega
    exact outsiderBound_step_of_kernel params7 invariantReal d (levelSchedule7 d hd) t
      (execPlacement (flowSizes7 d hd) nets v t ht')
      (execPlacement (flowSizes7 d hd) nets v (t + 1) ht) id id separatorConds_real
      (ih ht') (hK t ht1 ht (ih ht'))

/-- Purity: at `t = tf7 d` no key of a level-`(d-6)` bag is an order-2 stranger
(`μ δ 2^36 = 1023/2^36 < 1`; only `7 ≤ d` is needed). -/
theorem real_purity (hd : 7 ≤ d)
    (nets : ℕ → (b : KBag 64 d) → (n : ℕ) → ComparatorNetwork n)
    (hspecs : RealSpecs hd nets) (v : Equiv.Perm (Fin (64 ^ d))) (hK : KernelFamily hd nets v)
    (b : KBag 64 d) (hb : b.l = d - 6) :
    b.strangers 2 id ((execPlacement (flowSizes7 d hd) nets v (tf7 d) le_rfl).regs b)
      (by norm_num : 1 ≤ 64) = 0 := by
  have hP := P_all hd nets hspecs v hK (tf7 d) (one_le_tf7 hd) le_rfl b 1 (by omega)
  rw [show capacity params7 d b.l (tf7 d) = (64 : ℚ) ^ 6 by rw [hb]; exact capacity_meet7 d hd] at hP
  have hlt := lt_of_le_of_lt hP (by unfold invariantReal invariant7; norm_num : _ < (1 : ℚ))
  exact Nat.lt_one_iff.mp (by exact_mod_cast hlt)

end Chvatal
