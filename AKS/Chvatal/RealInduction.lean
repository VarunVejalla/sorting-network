module

/-
  # The root step, the induction, and purity for the real network (task B8)

  Source: V. Chvatal, *Lecture Notes on the New AKS Sorting Network*,
  Rutgers DCS-TR-294 (1992), Lemma 4.3 (root case with the exceptional separator), §4
  (induction) and §7 (purity at `t_f`).

  For `params7`, `invariantReal`, `sched = levelSchedule7 d hd`, `F = flowSizes7 d hd` and the
  execution-defined placement `pl t = execPlacement F nets v t _` (with `perm = id`):
  * `P_zero`: `OutsiderBoundLe … 0` (all keys at the root);
  * `P_one`: `OutsiderBoundLe … 1` (root step, from `bad_send0_real` at `t = 0`, `q = root`,
    `EB = ε_*·64^d/2`, and `ε_* ≤ μ/64`);
  * `P_all`: `OutsiderBoundLe … t` for `1 ≤ t ≤ tf7 d`, from `P_one` and the stage kernels `hK`;
  * `real_purity`: no order-2 strangers on the level-`d-6` bags at `t = tf7 d`.
  The stage kernels `hK` and node guarantees `hspecs` are hypotheses.
-/

public import AKS.Chvatal.KernelSetup
public import AKS.Chvatal.BadSendReal
public import AKS.Chvatal.Lemma41Real
public import AKS.Chvatal.Schedule7

@[expose] public section

namespace Chvatal

open Finset

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

/-- **B8.0.** At `t = 0` all keys sit at the root, which has no strangers of any order. -/
theorem P_zero (hd : 7 ≤ d)
    (nets : ℕ → (b : KBag 64 d) → (n : ℕ) → ComparatorNetwork n)
    (v : Equiv.Perm (Fin (64 ^ d))) :
    OutsiderBoundLe params7 invariantReal d (levelSchedule7 d hd) 0
      (execPlacement (flowSizes7 d hd) nets v 0 (Nat.zero_le _)) id := by
  show ∀ (b : KBag 64 d) (r : ℕ), r ≤ d →
    (((b.strangers (r + 1) id
      ((execPlacement (flowSizes7 d hd) nets v 0 (Nat.zero_le _)).regs b)
      (by norm_num : 1 ≤ 64) : ℕ) : ℚ)) ≤
      invariantReal.mu * invariantReal.delta ^ r * capacity params7 d b.l 0
  intro b r _
  by_cases hb : b = KBag.root 64 d
  · subst hb
    have h0 := KBag.strangers_eq_zero_of_lt_order (KBag.root 64 d) (r + 1) id
      ((execPlacement (flowSizes7 d hd) nets v 0 (Nat.zero_le _)).regs (KBag.root 64 d))
      (by norm_num : 1 ≤ 64) (by omega) (by show 0 < r + 1; omega)
    rw [h0]
    simpa using outsider_rhs_nonneg d r 0 0
  · have hE : (execPlacement (flowSizes7 d hd) nets v 0 (Nat.zero_le _)).regs b = ∅ := by
      show (wireSets (flowSizes7 d hd) 0 b).image _ = ∅
      rw [wireSets_zero_of_ne _ hb]; simp
    rw [hE, KBag.strangers_empty]
    simpa using outsider_rhs_nonneg d r b.l 0

set_option linter.constructorNameAsVariable false in
/-- **B8.1.** The root step (Lemma 4.3, root case, exceptional separator). -/
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
  by_cases hl : b.l = 1
  swap
  · have hcard := execPlacement_card (flowSizes7 d hd) nets v 1 h1 b
    have ha : (flowSizes7 d hd).a b.l 1 = 0 := by
      show flowA7 d hd b.l 1 = 0
      unfold flowA7
      simp [hl]
    have hE : (execPlacement (flowSizes7 d hd) nets v 1 h1).regs b = ∅ :=
      Finset.card_eq_zero.mp (hcard.trans ha)
    rw [hE, KBag.strangers_empty]
    simpa using outsider_rhs_nonneg d r b.l 1
  rcases Nat.eq_zero_or_pos r with hr0 | hr0
  swap
  · have h0 := KBag.strangers_eq_zero_of_lt_order b (r + 1) id
      ((execPlacement (flowSizes7 d hd) nets v 1 h1).regs b)
      (by norm_num : 1 ≤ 64) (by omega) (by omega)
    rw [h0]
    simpa using outsider_rhs_nonneg d r b.l 1
  subst hr0
  -- main case: level-1 bag, order 0
  have hbl : b.l < d := by omega
  have hroot : (KBag.root 64 d).l < d := by show 0 < d; omega
  have hjx : b.x < 64 := by
    have := b.hx
    rw [hl] at this
    simpa using this
  have hbj : b = (KBag.root 64 d).child b.x hjx hroot :=
    KBag.ext (by simp [KBag.child, KBag.root, hl]) (by simp [KBag.child, KBag.root])
  have ht0 : 0 < tf7 d := by omega
  have hreg := execPlacement_succ_regs (flowSizes7 d hd) nets v 0 ht0 b (by omega)
  have hchE : fromChildrenK (flowSizes7 d hd) nets v 0 b = ∅ := by
    unfold fromChildrenK
    rw [dif_pos hbl]
    apply Finset.eq_empty_of_forall_notMem
    intro k hk
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and] at hk
    obtain ⟨j, hj⟩ := hk
    have hne : b.child j.val j.isLt hbl ≠ KBag.root 64 d := by
      intro h
      have := congrArg KBag.l h
      simp [KBag.child, KBag.root] at this
    rw [wireSets_zero_of_ne _ hne] at hj
    simp [upSet, blockOf] at hj
  have hregs : (execPlacement (flowSizes7 d hd) nets v 1 h1).regs b =
      fromParentK (flowSizes7 d hd) nets v 0 b := by
    rw [show (execPlacement (flowSizes7 d hd) nets v 1 h1).regs b =
        (execPlacement (flowSizes7 d hd) nets v (0 + 1) ht0).regs b from rfl, hreg, hchE,
      Finset.union_empty]
  -- apply bad_send0_real at t = 0, q = root
  have hdown : (flowSizes7 d hd).down 0 0 = 64 ^ (d - 1) := by
    show flowDown7 d hd 0 0 = _
    simp [flowDown7]
  have hup : (flowSizes7 d hd).up 0 0 = 0 := by
    show flowUp7 d hd 0 0 = _
    simp [flowUp7]
  have ha0 : (flowSizes7 d hd).a 0 0 = 64 ^ d := by
    show flowA7 d hd 0 0 = _
    simp [flowA7]
  have hdpos : 0 < (flowSizes7 d hd).down (KBag.root 64 d).l 0 := by
    show 0 < (flowSizes7 d hd).down 0 0
    rw [hdown]; positivity
  have hspec := hspecs 0 (KBag.root 64 d) ht0 hdpos
  have hM : ∀ j' : Fin 64,
      ((((execPlacement (flowSizes7 d hd) nets v 0 ht0.le).regs (KBag.root 64 d)).filter fun κ =>
        ((KBag.root 64 d).child j'.val j'.isLt hroot).Native κ id).card : ℝ) ≤
        ((flowSizes7 d hd).down (KBag.root 64 d).l 0 : ℝ) + 0 := by
    intro j'
    have hc := native_card (br := 64) (d := d) (by norm_num)
      ((KBag.root 64 d).child j'.val j'.isLt hroot)
    have hsub : (((execPlacement (flowSizes7 d hd) nets v 0 ht0.le).regs
        (KBag.root 64 d)).filter fun κ =>
          ((KBag.root 64 d).child j'.val j'.isLt hroot).Native κ id) ⊆
        Finset.univ.filter fun κ : Fin (64 ^ d) =>
          ((KBag.root 64 d).child j'.val j'.isLt hroot).Native κ id :=
      Finset.filter_subset_filter _ (Finset.subset_univ _)
    have hle := Finset.card_le_card hsub
    rw [hc] at hle
    have hdn : (flowSizes7 d hd).down (KBag.root 64 d).l 0 = 64 ^ (d - 1) := hdown
    rw [hdn, add_zero]
    have : (KBag.child (KBag.root 64 d) j'.val j'.isLt hroot).l = 1 := rfl
    rw [this] at hle
    exact_mod_cast hle
  have hpos : (((flowSizes7 d hd).up (KBag.root 64 d).l 0 : ℕ) : ℝ) / 2 ≤
      (((KBag.root 64 d).strangers 1 id
        ((execPlacement (flowSizes7 d hd) nets v 0 ht0.le).regs (KBag.root 64 d)) : ℕ) : ℝ) +
        63 * 0 := by
    have : (flowSizes7 d hd).up (KBag.root 64 d).l 0 = 0 := hup
    rw [this]; simp
  have hbad := bad_send0_real (flowSizes7 d hd) nets v 0 ht0 (KBag.root 64 d) hroot
    ⟨b.x, hjx⟩ (specEB 0 ((flowSizes7 d hd).a (KBag.root 64 d).l 0))
    (specJmax ((flowSizes7 d hd).up (KBag.root 64 d).l 0)) eps 0 le_rfl hspec hM hpos
  have hroot0 : (KBag.root 64 d).strangers 1 id
      ((execPlacement (flowSizes7 d hd) nets v 0 ht0.le).regs (KBag.root 64 d))
        (by norm_num : 1 ≤ 64) = 0 :=
    KBag.strangers_eq_zero_of_lt_order _ 1 id _ (by norm_num : 1 ≤ 64) le_rfl (by
      show 0 < 1; omega)
  rw [hroot0] at hbad
  rw [← hbj] at hbad
  -- numeric finish
  have hEB : specEB 0 ((flowSizes7 d hd).a (KBag.root 64 d).l 0) =
      paperRootEpsB * (64 : ℝ) ^ d / 2 := by
    unfold specEB
    have : (flowSizes7 d hd).a (KBag.root 64 d).l 0 = 64 ^ d := ha0
    rw [this]; simp
  have hup' : (((flowSizes7 d hd).up (KBag.root 64 d).l 0 : ℕ) : ℝ) = 0 := by
    have : (flowSizes7 d hd).up (KBag.root 64 d).l 0 = 0 := hup
    rw [this]; simp
  rw [hEB, hup'] at hbad
  have hcap : capacity params7 d b.l 1 = (64 : ℚ) ^ (d - 1) := by
    rw [hl]
    unfold capacity params7
    simp only []
    obtain ⟨e, rfl⟩ : ∃ e, d = e + 1 := ⟨d - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    push_cast
    rw [pow_succ]
    field_simp
  have hεle := paperRootEpsB_le_epsStar
  have hpd : (64 : ℝ) ^ d = 64 * 64 ^ (d - 1) := by
    obtain ⟨e, rfl⟩ : ∃ e, d = e + 1 := ⟨d - 1, by omega⟩
    simp [pow_succ]; ring
  rw [hregs]
  have key : (((b.strangers 1 id (fromParentK (flowSizes7 d hd) nets v 0 b) : ℕ)) : ℝ) ≤
      (invariantReal.mu : ℝ) * ((64 : ℝ) ^ (d - 1)) := by
    have hμ : (invariantReal.epsStar : ℝ) * 64 = (invariantReal.mu : ℝ) := by
      unfold invariantReal; push_cast; norm_num
    calc _ ≤ _ := hbad
      _ = paperRootEpsB * (64 * 64 ^ (d - 1)) := by rw [hpd]; ring
      _ ≤ (invariantReal.epsStar : ℝ) * (64 * 64 ^ (d - 1)) :=
          mul_le_mul_of_nonneg_right hεle (by positivity)
      _ = (invariantReal.mu : ℝ) * ((64 : ℝ) ^ (d - 1)) := by rw [← hμ]; ring
  have : (((b.strangers (0 + 1) id (fromParentK (flowSizes7 d hd) nets v 0 b) : ℕ)) : ℚ) ≤
      invariantReal.mu * invariantReal.delta ^ 0 * capacity params7 d b.l 1 := by
    rw [hcap, pow_zero, mul_one]
    have : (((b.strangers 1 id (fromParentK (flowSizes7 d hd) nets v 0 b) : ℕ)) : ℝ) ≤
        (((invariantReal.mu * (64 : ℚ) ^ (d - 1) : ℚ)) : ℝ) := by
      push_cast; exact key
    exact_mod_cast this
  exact this

/-- **B8.2.** The induction from `P_one`, using the stage kernels. -/
theorem P_all (hd : 7 ≤ d)
    (nets : ℕ → (b : KBag 64 d) → (n : ℕ) → ComparatorNetwork n)
    (hspecs : RealSpecs hd nets)
    (v : Equiv.Perm (Fin (64 ^ d)))
    (hK : ∀ t, 1 ≤ t → ∀ (ht : t + 1 ≤ tf7 d),
      OutsiderBoundLe params7 invariantReal d (levelSchedule7 d hd) t
        (execPlacement (flowSizes7 d hd) nets v t (by omega)) id →
      StageKernel params7 invariantReal d (levelSchedule7 d hd) t
        (execPlacement (flowSizes7 d hd) nets v t (by omega)) id
        (execPlacement (flowSizes7 d hd) nets v (t + 1) ht) id) :
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

/-- **B8.3.** Purity: at `t = tf7 d` no key of a level-`(d-6)` bag is an order-2 stranger.
(`μ δ 2^36 = 1023/2^36 < 1`; only `7 ≤ d` is needed.) -/
theorem real_purity (hd : 7 ≤ d)
    (nets : ℕ → (b : KBag 64 d) → (n : ℕ) → ComparatorNetwork n)
    (hspecs : RealSpecs hd nets)
    (v : Equiv.Perm (Fin (64 ^ d)))
    (hK : ∀ t, 1 ≤ t → ∀ (ht : t + 1 ≤ tf7 d),
      OutsiderBoundLe params7 invariantReal d (levelSchedule7 d hd) t
        (execPlacement (flowSizes7 d hd) nets v t (by omega)) id →
      StageKernel params7 invariantReal d (levelSchedule7 d hd) t
        (execPlacement (flowSizes7 d hd) nets v t (by omega)) id
        (execPlacement (flowSizes7 d hd) nets v (t + 1) ht) id)
    (b : KBag 64 d) (hb : b.l = d - 6) :
    b.strangers 2 id ((execPlacement (flowSizes7 d hd) nets v (tf7 d) le_rfl).regs b)
      (by norm_num : 1 ≤ 64) = 0 := by
  have hP := P_all hd nets hspecs v hK (tf7 d) (one_le_tf7 hd) le_rfl b 1 (by omega)
  have hcap : capacity params7 d b.l (tf7 d) = (64 : ℚ) ^ 6 := by
    rw [hb]; exact capacity_meet7 d hd
  rw [hcap] at hP
  have hlt : ((b.strangers (1 + 1) id
      ((execPlacement (flowSizes7 d hd) nets v (tf7 d) le_rfl).regs b)
      (by norm_num : 1 ≤ 64) : ℕ) : ℚ) < 1 := by
    refine lt_of_le_of_lt hP ?_
    unfold invariantReal invariant7
    norm_num
  have : b.strangers (1 + 1) id
      ((execPlacement (flowSizes7 d hd) nets v (tf7 d) le_rfl).regs b)
      (by norm_num : 1 ≤ 64) < 1 := by exact_mod_cast hlt
  exact Nat.lt_one_iff.mp this

end Chvatal
