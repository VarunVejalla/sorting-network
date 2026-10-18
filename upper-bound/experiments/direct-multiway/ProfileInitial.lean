import AKS.Chvatal.RealInduction
import ProfileStageKernel
set_option maxRecDepth 4096
set_option maxHeartbeats 0

/-! Stage-one initialization for the geometric outsider profile. This is a
scratch strengthening of `P_one`; it leaves the promoted scalar theorem intact. -/

namespace Chvatal

/-- Sharpen the paper's initial exceptional epsilon just enough for the
profile scale. The slack comes from the numerical value of the square root,
not from weakening the proposed profile. -/
theorem paperRootEpsB_le_profileEps :
    paperRootEpsB <= (profileScale : Rat) * (invMu : Rat) / 64 := by
  have hl := Real.log_two_lt_d9
  have hs : Real.sqrt (1 + 79 * Real.log 2) <= (998 : Real) / 128 := by
    rw [Real.sqrt_le_iff]
    refine ⟨by norm_num, ?_⟩
    norm_num at hl ⊢
    nlinarith
  unfold paperRootEpsB invMu
  push_cast
  rw [div_le_iff₀ (by positivity)]
  norm_num [profileScale] at hs ⊢
  nlinarith

theorem profile_rhs_nonneg (d r l t : Nat) :
    (0 : Rat) <= profileScale * invMu * profileEffectiveDelta ^ r * capacity d l t := by
  have hs : 0 <= profileScale := by norm_num [profileScale]
  have hm := invMu_pos.le
  have hd : 0 <= profileEffectiveDelta := by
    norm_num [profileEffectiveDelta, profileGamma, invDelta]
  have hc := capacity_nonneg d l t
  positivity

/-- The actual stage-one register placement satisfies the proposed full
rank profile. All non-root, positive-rank cases vanish exactly as in `P_one`;
the root exceptional estimate uses the sharper epsilon lemma above. -/
theorem Profile_P_one (hd : 7 <= d)
    (nets : Nat -> (b : KBag 64 d) -> (n : Nat) -> ComparatorNetwork n)
    (hspecs : RealSpecs hd nets) (v : Equiv.Perm (Fin (64 ^ d))) :
    ProfileOutsiderBoundLe d 1
      (execPlacement (flowSizes7 d hd) nets v 1 (one_le_tf7 hd)) id := by
  intro b r hr
  have h1 := one_le_tf7 hd
  have hrhs := profile_rhs_nonneg d r b.l 1
  by_cases hl : b.l = 1
  swap
  · have hE : (execPlacement (flowSizes7 d hd) nets v 1 h1).regs b = ∅ :=
      Finset.card_eq_zero.mp ((execPlacement_card (flowSizes7 d hd) nets v 1 h1 b).trans (by
        show flowA7 d hd b.l 1 = 0
        unfold flowA7
        simp [hl]))
    rw [hE, KBag.strangers_empty]
    exact hrhs
  rcases Nat.eq_zero_or_pos r with hr0 | hrpos
  swap
  · rw [KBag.strangers_eq_zero_of_lt_order b (r + 1) id _
      (by norm_num : 1 <= 64) (by omega) (by omega)]
    exact hrhs
  subst r
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
      execPlacement_succ_regs (flowSizes7 d hd) nets v 0 ht0 b (by omega), hchE,
      Finset.union_empty]
  have hdown : (flowSizes7 d hd).down (KBag.root 64 d).l 0 = 64 ^ (d - 1) := by
    simp [flowSizes7, flowDown7, KBag.root]
  have hup : (flowSizes7 d hd).up (KBag.root 64 d).l 0 = 0 := by
    simp [flowSizes7, flowUp7, KBag.root]
  have ha0 : (flowSizes7 d hd).a (KBag.root 64 d).l 0 = 64 ^ d := by
    simp [flowSizes7, flowA7, KBag.root]
  have hM : ∀ j' : Fin 64,
      ((((execPlacement (flowSizes7 d hd) nets v 0 ht0.le).regs (KBag.root 64 d)).filter fun κ =>
        ((KBag.root 64 d).child j'.val j'.isLt hroot).Native κ id).card : ℝ) <=
        ((flowSizes7 d hd).down (KBag.root 64 d).l 0 : ℝ) + 0 := by
    intro j'
    have hle := (Finset.card_le_card (Finset.filter_subset_filter _ (Finset.subset_univ
      ((execPlacement (flowSizes7 d hd) nets v 0 ht0.le).regs (KBag.root 64 d))))).trans_eq
      (native_card (br := 64) (d := d) (by norm_num)
        ((KBag.root 64 d).child j'.val j'.isLt hroot))
    rw [hdown, add_zero]
    exact_mod_cast hle
  have hroot0 : (KBag.root 64 d).strangers 1 id
      ((execPlacement (flowSizes7 d hd) nets v 0 ht0.le).regs (KBag.root 64 d))
        (by norm_num : 1 <= 64) = 0 :=
    KBag.strangers_eq_zero_of_lt_order _ 1 id _ (by norm_num : 1 <= 64) le_rfl (by
      show 0 < 1; omega)
  have hbad := bad_send0_real (flowSizes7 d hd) nets v 0 ht0 (KBag.root 64 d) hroot
    ⟨b.x, hjx⟩ (specEB 0 ((flowSizes7 d hd).a (KBag.root 64 d).l 0))
    (specJmax ((flowSizes7 d hd).up (KBag.root 64 d).l 0)) eps 0 le_rfl
    (hspecs 0 (KBag.root 64 d) ht0 (by rw [hdown]; positivity)) hM
    (by rw [hup, hroot0]; simp)
  rw [hroot0, ← hbj, ha0, hup] at hbad
  have hEB : specEB 0 (64 ^ d) = paperRootEpsB * (64 : ℝ) ^ d / 2 := by
    simp [specEB]
  rw [hEB] at hbad
  have hcap : capacity d b.l 1 = (64 : Rat) ^ (d - 1) := by
    rw [hl]
    obtain ⟨e, rfl⟩ : ∃ e, d = e + 1 := ⟨d - 1, by omega⟩
    simp only [capacity, Nat.add_sub_cancel]
    push_cast
    rw [pow_succ]
    field_simp
  have hpd : (64 : ℝ) ^ d = 64 * 64 ^ (d - 1) := by
    obtain ⟨e, rfl⟩ : ∃ e, d = e + 1 := ⟨d - 1, by omega⟩
    simp [pow_succ]
    ring
  have hb2 : ((b.strangers 1 id (fromParentK (flowSizes7 d hd) nets v 0 b) : Nat) : ℝ) <=
      paperRootEpsB * (64 : ℝ) ^ d := by
    push_cast at hbad
    refine hbad.trans (le_of_eq ?_)
    ring
  have hεle := paperRootEpsB_le_profileEps
  have key : ((b.strangers 1 id (fromParentK (flowSizes7 d hd) nets v 0 b) : Nat) : ℝ) <=
      (profileScale : ℝ) * invMu * ((64 : ℝ) ^ (d - 1)) := by
    calc
      _ <= paperRootEpsB * (64 : ℝ) ^ d := hb2
      _ = paperRootEpsB * (64 * 64 ^ (d - 1)) := by rw [hpd]
      _ <= ((profileScale : Rat) : ℝ) * (invMu : ℝ) / 64 *
            (64 * 64 ^ (d - 1)) := by
              exact mul_le_mul_of_nonneg_right hεle (by positivity)
      _ = (profileScale : ℝ) * invMu * ((64 : ℝ) ^ (d - 1)) := by push_cast; ring
  rw [hregs, hcap, pow_zero, mul_one]
  rw [← Rat.cast_le (K := ℝ)]
  push_cast
  exact key

end Chvatal
