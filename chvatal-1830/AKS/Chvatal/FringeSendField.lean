module

public import AKS.Chvatal.KernelSetup
public import AKS.Chvatal.FringeSendReal
public import AKS.Chvatal.Wires31

@[expose] public section

namespace Chvatal

open Finset

theorem jmax_of_le (n π : ℕ) (c : ℚ)
    (h : (n : ℚ) ≤ invMu * c)
    (h2 : invMu * c ≤ (1 / 2) * (128 / 4095 : ℚ) * (π : ℚ)) :
    n ≤ specJmax π := by
  unfold specJmax
  apply Nat.le_floor
  have h3 : (n : ℚ) ≤ (128 / 4095 : ℚ) * ((π : ℚ) / 2) := by linarith
  have h4 : ((n : ℚ) : ℝ) ≤ (((128 / 4095 : ℚ) * ((π : ℚ) / 2) : ℚ) : ℝ) := by exact_mod_cast h3
  push_cast at h4
  exact h4

/-- Nodes with high π: upper bound on mu times capacity. -/
theorem mu_le_of_up_lower (c : ℚ) (hc : 0 ≤ c) (π : ℕ)
    (hπ : 4095 * c / 68719476736 ≤ (π : ℚ)) :
    invMu * c ≤ (1 / 2) * (128 / 4095 : ℚ) * (π : ℚ) := by
  have h44 := cond44_real
  linarith [mul_le_mul_of_nonneg_right h44 hc]

/-- The invariant at the parent gives `strangers r ≤ μ c` (order `r - 1` in `P`). -/
theorem strangers_le_mu_cap {d : ℕ} (hd : 7 ≤ d) (t : ℕ) (pl : Placement 64 d)
    (hP : OutsiderBoundLe d t pl id)
    (q : KBag 64 d) (r : ℕ) (hr1 : 1 ≤ r) (hrd : r ≤ d) :
    ((q.strangers r id (pl.regs q) : ℕ) : ℚ) ≤
      invMu * capacity d q.l t := by
  have h := hP q (r - 1) (by omega)
  rw [Nat.sub_add_cancel hr1] at h
  have hδ : invDelta ^ (r - 1) ≤ 1 :=
    pow_le_one₀ invDelta_pos.le invDelta_lt_one.le
  have hc := capacity_nonneg d q.l t
  have hμ := invMu_pos
  calc _ ≤ invMu * invDelta ^ (r - 1) * capacity d q.l t := h
    _ ≤ invMu * 1 * capacity d q.l t := by gcongr
    _ = _ := by ring

theorem up_mid_ge (c : ℚ) :
    4095 * c / 68719476736 ≤
      (4095 : Rat) * c / capacityRatio := by
  rw [capacityRatio_eq]; apply le_of_eq; norm_num

theorem up_rise_ge (c : ℚ) (hc : 0 ≤ c) :
    4095 * c / 68719476736 ≤ (1 / 64 : Rat) * c / ((4096 : Rat) * 64) := by
  norm_num; linarith

/-- Nodes sending wires down have either low up or high capacity. -/
theorem up_lower_or_top_desc (d : ℕ) (hd : 7 ≤ d) (t : ℕ) (ht2 : 2 ≤ t) (ht : t < tf7 d)
    (i : ℕ) (hdown : 0 < flowDown7 d hd i t) :
    (i = alpha7 d t ∧ alpha7 d t < alpha7 d (t + 1)) ∨
      4095 * capacity d i t / 68719476736 ≤ (flowUp7 d hd i t : ℚ) := by
  have hc := capacity_nonneg d i t
  have hdq : (0 : ℚ) < (flowDown7 d hd i t : ℚ) := by exact_mod_cast hdown
  have hdc := cast_flowDown7 d hd i t ht2 ht
  by_cases hact : alpha7 d t ≤ i ∧ i ≤ omega7 d t ∧ i % 2 = t % 2
  swap
  · exfalso
    rw [flowDown_inactive d (by
      show ¬(t ≤ tf7 d ∧ alpha7 d t ≤ i ∧ i ≤ omega7 d t ∧ i % 2 = t % 2)
      omega)] at hdc
    linarith
  have hact' : t ≤ tf7 d ∧ alpha7 d t ≤ i ∧ i ≤ omega7 d t ∧ i % 2 = t % 2 := ⟨ht.le, hact⟩
  have hp1 := alpha7_parity d t
  have hp2 := alpha7_parity d (t + 1)
  have hst := alpha7_step d t hd ht
  by_cases hi : i = alpha7 d t
  · by_cases hs : alpha7 d t < alpha7 d (t + 1)
    · exact Or.inl ⟨hi, hs⟩
    · right
      rw [(tau_top_rise d hd t ht2 ht i hact' hi (by omega)).1]
      exact up_rise_ge _ hc
  · right
    by_cases hω : i = omega7 d t
    · by_cases hs : omega7 d t < omega7 d (t + 1)
      · rw [(tau_bot_desc d hd t ht2 ht i hact' hi hω hs).1]
        exact up_mid_ge _
      · exfalso
        rw [flowDown_bot_rise d hact' hi hω hs] at hdc
        linarith
    · rw [(tau_mid d hd t ht2 ht i hact' hi hω).1]
      exact up_mid_ge _

/-- At `t = 1`: only level-1 node sends wires down. -/
theorem up_lower_one (d : ℕ) (hd : 7 ≤ d) (i : ℕ) (hdown : 0 < flowDown7 d hd i 1) :
    4095 * capacity d i 1 / 68719476736 ≤ (flowUp7 d hd i 1 : ℚ) := by
  obtain rfl : i = 1 := by
    by_contra h
    simp [flowDown7, h] at hdown
  obtain ⟨e, rfl⟩ : ∃ e, d = e + 7 := ⟨d - 7, by omega⟩
  rw [capacity_eq_pow (e + 7) 1 1 (e + 6) (by omega)]
  simp only [flowUp7, if_true, show (1 : ℕ) ≠ 0 by omega, if_false]
  rw [show e + 7 - 5 = e + 2 by omega]
  push_cast
  rw [show e + 6 = (e + 2) + 4 by omega, pow_add]
  have : (0 : ℚ) ≤ 64 ^ (e + 2) := by positivity
  norm_num; nlinarith

/-- Descending top nodes have no outsiders. -/
theorem top_desc_no_strangers {d : ℕ} (hd : 7 ≤ d) (t : ℕ) (pl : Placement 64 d)
    (hP : OutsiderBoundLe d t pl id)
    (q : KBag 64 d) (r : ℕ) (hr1 : 1 ≤ r) (hrd : r ≤ d)
    (hq : q.l = alpha7 d t) (hs : alpha7 d t < alpha7 d (t + 1)) :
    q.strangers r id (pl.regs q) = 0 := by
  by_cases h0 : alpha7 d t = 0
  · exact KBag.strangers_eq_zero_of_lt_order q r id _ _ hr1 (by omega)
  rcases lemma32_schedule7 d hd t hs with hl | hl
  · exact absurd hl h0
  have hc : capacity d q.l t ≤ 1073741824 := hq ▸ hl
  have h1 := strangers_le_mu_cap hd t pl hP q r hr1 hrd
  have h2 := mu_real_mul_le_one _ hc
  have : ((q.strangers r id (pl.regs q) : ℕ) : ℚ) < 1 := by linarith
  exact_mod_cast Nat.lt_one_iff.mp (by exact_mod_cast this)

/-- `Jmax` hypothesis for nodes sending wires down. -/
theorem jmax_ok {d : ℕ} (hd : 7 ≤ d) (t : ℕ) (ht1 : 1 ≤ t) (ht : t < tf7 d)
    (pl : Placement 64 d)
    (hP : OutsiderBoundLe d t pl id)
    (q : KBag 64 d) (r : ℕ) (hr1 : 1 ≤ r) (hrd : r ≤ d)
    (hdown : 0 < (flowSizes7 d hd).down q.l t) :
    q.strangers r id (pl.regs q) ≤ specJmax ((flowSizes7 d hd).up q.l t) := by
  have hdown' : 0 < flowDown7 d hd q.l t := hdown
  have hmu := strangers_le_mu_cap hd t pl hP q r hr1 hrd
  have key : 4095 * capacity d q.l t / 68719476736 ≤ (flowUp7 d hd q.l t : ℚ) →
      q.strangers r id (pl.regs q) ≤ specJmax (flowUp7 d hd q.l t) :=
    fun h => jmax_of_le _ _ _ hmu (mu_le_of_up_lower _ (capacity_nonneg d q.l t) _ h)
  show _ ≤ specJmax (flowUp7 d hd q.l t)
  by_cases h1 : t = 1
  · subst h1
    exact key (up_lower_one d hd q.l hdown')
  · rcases up_lower_or_top_desc d hd t (by omega) ht q.l hdown' with ⟨hq, hs⟩ | h
    · rw [top_desc_no_strangers hd t pl hP q r hr1 hrd hq hs]; exact Nat.zero_le _
    · exact key h

/-- **Fringe send field** (Chvátal, Lemma 4.4 parent). -/
theorem fringeSendField_real {d : ℕ} (hd : 7 ≤ d)
    (nets : ℕ → (b : KBag 64 d) → (n : ℕ) → ComparatorNetwork n)
    (hspecs : RealSpecs hd nets) (v : Equiv.Perm (Fin (64 ^ d))) (t : ℕ) (ht1 : 1 ≤ t)
    (ht : t + 1 ≤ tf7 d)
    (hP : OutsiderBoundLe d t
      (execPlacement (flowSizes7 d hd) nets v t (by omega)) id) :
    FringeSendField hd nets v t (by omega) := by
  intro b r hr1 hrd hb
  obtain ⟨q, hqd, j, rfl⟩ := exists_parent_child b hb
  rw [KBag.child_parent q _ _ _ (by norm_num)]
  by_cases hdown : (flowSizes7 d hd).down q.l t = 0
  · rw [fromParentK_eq_empty hd nets v t (q.child j.val j.isLt hqd) hdown]
    simp only [KBag.strangers_empty, Nat.cast_zero]
    have := invEpsF_nonneg
    positivity
  · have hpos : 0 < (flowSizes7 d hd).down q.l t := Nat.pos_of_ne_zero hdown
    have ha : (wireSets (flowSizes7 d hd) t q).card =
        (flowSizes7 d hd).up q.l t + 64 * (flowSizes7 d hd).down q.l t := by
      rw [wireSets_card (flowSizes7 d hd) (by omega)]
      exact flowSizes7_split d hd q.l t (by omega)
    have hfs := fringe_send_real (flowSizes7 d hd) nets v t (by omega) q hqd j r hr1 _ _ eps
      ha (hspecs t q (by omega) hpos)
      (jmax_ok hd t ht1 (by omega) _ hP q r hr1 hrd hpos)
    have e : ((invEpsF : ℚ) : ℝ) = eps := by
      unfold eps invEpsF; norm_num
    rw [← Rat.cast_le (K := ℝ)]
    push_cast
    rw [e]
    exact hfs

end Chvatal
