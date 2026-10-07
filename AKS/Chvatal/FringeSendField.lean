module
/-
  # The fringe-send field of the real stage kernel (task KF)

  Source: V. Chvátal, *Lecture Notes on the New AKS Sorting Network*, Rutgers DCS-TR-294 (1992),
  Lemma 4.4 (parent part) with condition (4.4) and Lemma 3.2.

  Main result: `fringeSendField_real`.  The send bound `fringe_send_real` needs
  `strangers r q ≤ Jmax = ⌊δ_F π/2⌋`.  For nodes with `π > 0` this follows from the invariant
  `strangers r ≤ μ c` and (4.4); at descending top nodes (`π = 0`) the capacity is `≤ 2^30`
  so `μ c < 1` and there are no outsiders at all.
-/

public import AKS.Chvatal.KernelSetup
public import AKS.Chvatal.FringeSendReal
public import AKS.Chvatal.Wires31
public import AKS.Chvatal.Schedule7
public import AKS.Chvatal.OutsiderInduction

@[expose] public section

namespace Chvatal

open Finset

/-! ## Scalar helpers -/

theorem jmax_of_le (n π : ℕ) (c : ℚ)
    (h : (n : ℚ) ≤ invariantReal.mu * c)
    (h2 : invariantReal.mu * c ≤ (1 / 2) * (128 / 4095 : ℚ) * (π : ℚ)) :
    n ≤ specJmax π := by
  unfold specJmax
  apply Nat.le_floor
  have h3 : (n : ℚ) ≤ (128 / 4095 : ℚ) * ((π : ℚ) / 2) := by linarith
  have h4 : ((n : ℚ) : ℝ) ≤ (((128 / 4095 : ℚ) * ((π : ℚ) / 2) : ℚ) : ℝ) := by exact_mod_cast h3
  push_cast at h4
  exact h4

/-- Interior / bottom-descending / top-rising nodes: `π ≥ (Aνk−1)c/Q` gives `μ c ≤ ½ δ_F π`. -/
theorem mu_le_of_up_lower (c : ℚ) (hc : 0 ≤ c) (π : ℕ)
    (hπ : 4095 * c / 68719476736 ≤ (π : ℚ)) :
    invariantReal.mu * c ≤ (1 / 2) * (128 / 4095 : ℚ) * (π : ℚ) := by
  have h44 := cond44_real
  have e : invariantReal.deltaF = 128 / 4095 := by unfold invariantReal invariant7; rfl
  rw [e] at h44
  have h1 : invariantReal.mu * c ≤ ((1 / 2) * (128 / 4095 : ℚ) * 4095 / 68719476736) * c :=
    mul_le_mul_of_nonneg_right h44 hc
  have h2 : ((1 / 2) * (128 / 4095 : ℚ) * 4095 / 68719476736) * c =
      (1 / 2) * (128 / 4095 : ℚ) * (4095 * c / 68719476736) := by ring
  have h3 : (1 / 2) * (128 / 4095 : ℚ) * (4095 * c / 68719476736) ≤
      (1 / 2) * (128 / 4095 : ℚ) * (π : ℚ) :=
    mul_le_mul_of_nonneg_left hπ (by norm_num)
  linarith

theorem capacity7_nonneg (d i t : ℕ) : 0 ≤ capacity params7 d i t := (capacity_pos params7 d i t).le

/-- The invariant at the parent gives `strangers r ≤ μ c` (order `r - 1` in `P`). -/
theorem strangers_le_mu_cap {d : ℕ} (hd : 7 ≤ d) (t : ℕ) (pl : Placement params7.br d)
    (hP : OutsiderBoundLe params7 invariantReal d (levelSchedule7 d hd) t pl id)
    (q : KBag 64 d) (r : ℕ) (hr1 : 1 ≤ r) (hrd : r ≤ d) :
    ((q.strangers r id (pl.regs q) (br_ge_one params7) : ℕ) : ℚ) ≤
      invariantReal.mu * capacity params7 d q.l t := by
  have h := hP q (r - 1) (by omega)
  rw [Nat.sub_add_cancel hr1] at h
  have hδ : invariantReal.delta ^ (r - 1) ≤ 1 :=
    pow_le_one₀ invariantReal.hdelta_pos.le invariantReal.hdelta_lt.le
  have hc := capacity7_nonneg d q.l t
  have hμ : 0 < invariantReal.mu := invariantReal.hmu_pos
  calc _ ≤ invariantReal.mu * invariantReal.delta ^ (r - 1) * capacity params7 d q.l t := h
    _ ≤ invariantReal.mu * 1 * capacity params7 d q.l t := by gcongr
    _ = _ := by ring

/-! ## Node types at `t ≥ 2` -/

theorem up_mid_ge (c : ℚ) :
    4095 * c / 68719476736 ≤
      (params7.A * params7.nu * 64 - 1) * c / capacityRatio params7 := by
  rw [capacityRatio_params7]; apply le_of_eq; norm_num [params7]

theorem up_rise_ge (c : ℚ) (hc : 0 ≤ c) :
    4095 * c / 68719476736 ≤ params7.nu * c / (params7.A * 64) := by
  norm_num [params7]; linarith

/-- For `t ≥ 2`: a node that sends wires down is either a descending top node, or has
`π ≥ (Aνk−1)c/Q`. -/
theorem up_lower_or_top_desc (d : ℕ) (hd : 7 ≤ d) (t : ℕ) (ht2 : 2 ≤ t) (ht : t < tf7 d)
    (i : ℕ) (hdown : 0 < flowDown7 d hd i t) :
    (i = alpha7 d t ∧ alpha7 d t < alpha7 d (t + 1)) ∨
      4095 * capacity params7 d i t / 68719476736 ≤ (flowUp7 d hd i t : ℚ) := by
  have hc := capacity7_nonneg d i t
  have hdq : (0 : ℚ) < (flowDown7 d hd i t : ℚ) := by exact_mod_cast hdown
  have hdc := cast_flowDown7 d hd i t ht2 ht
  by_cases hact : alpha7 d t ≤ i ∧ i ≤ omega7 d t ∧ i % 2 = t % 2
  swap
  · exfalso
    have hz : flowDown params7 d (levelSchedule7 d hd) i t = 0 :=
      flowDown_inactive params7 d (levelSchedule7 d hd) (by
        show ¬(t ≤ tf7 d ∧ alpha7 d t ≤ i ∧ i ≤ omega7 d t ∧ i % 2 = t % 2)
        omega)
    rw [hz] at hdc; linarith
  have hact' : t ≤ tf7 d ∧ alpha7 d t ≤ i ∧ i ≤ omega7 d t ∧ i % 2 = t % 2 :=
    ⟨ht.le, hact⟩
  have hp1 := alpha7_parity d t
  have hp2 := alpha7_parity d (t + 1)
  have hst := alpha7_step d t hd ht
  by_cases hi : i = alpha7 d t
  · by_cases hs : alpha7 d t < alpha7 d (t + 1)
    · exact Or.inl ⟨hi, hs⟩
    · right
      have hs' : alpha7 d (t + 1) < alpha7 d t := by omega
      rw [(tau_top_rise d hd t ht2 ht i hact' hi hs').1]
      exact up_rise_ge _ hc
  · right
    by_cases hω : i = omega7 d t
    · by_cases hs : omega7 d t < omega7 d (t + 1)
      · rw [(tau_bot_desc d hd t ht2 ht i hact' hi hω hs).1]
        exact up_mid_ge _
      · exfalso
        have hz : flowDown params7 d (levelSchedule7 d hd) i t = 0 :=
          flowDown_bot_rise params7 d (levelSchedule7 d hd) hact' hi hω hs
        rw [hz] at hdc; linarith
    · rw [(tau_mid d hd t ht2 ht i hact' hi hω).1]
      exact up_mid_ge _

/-- At `t = 1` only the level-1 node sends wires down, with `π = 64^(d-5)`, `c = 64^(d-1)`. -/
theorem up_lower_one (d : ℕ) (hd : 7 ≤ d) (i : ℕ) (hdown : 0 < flowDown7 d hd i 1) :
    4095 * capacity params7 d i 1 / 68719476736 ≤ (flowUp7 d hd i 1 : ℚ) := by
  have hi : i = 1 := by
    by_contra h
    simp [flowDown7, h] at hdown
  subst hi
  obtain ⟨e, rfl⟩ : ∃ e, d = e + 7 := ⟨d - 7, by omega⟩
  rw [capacity_params7 (e + 7) 1 1 (e + 6) (by omega)]
  simp only [flowUp7, if_true, show (1 : ℕ) ≠ 0 by omega, if_false]
  rw [show e + 7 - 5 = e + 2 by omega]
  push_cast
  rw [show e + 6 = (e + 2) + 4 by omega, pow_add]
  have : (0 : ℚ) ≤ 64 ^ (e + 2) := by positivity
  norm_num; nlinarith

/-- Descending top nodes have no outsiders of any order `r ≥ 1`: either the node is the root,
or its capacity is `≤ 2^30` so `μ c < 1`. -/
theorem top_desc_no_strangers {d : ℕ} (hd : 7 ≤ d) (t : ℕ) (pl : Placement params7.br d)
    (hP : OutsiderBoundLe params7 invariantReal d (levelSchedule7 d hd) t pl id)
    (q : KBag 64 d) (r : ℕ) (hr1 : 1 ≤ r) (hrd : r ≤ d)
    (hq : q.l = alpha7 d t) (hs : alpha7 d t < alpha7 d (t + 1)) :
    q.strangers r id (pl.regs q) (br_ge_one params7) = 0 := by
  by_cases h0 : alpha7 d t = 0
  · exact KBag.strangers_eq_zero_of_lt_order q r id _ _ hr1 (by omega)
  · have hl := lemma32_levelSchedule7 d hd t hs
    rcases hl with hl | hl
    · exact absurd hl h0
    · have hc : capacity params7 d q.l t ≤ 1073741824 := by
        rw [hq]
        have : params7.A * (params7.br : ℚ) ^ 2 / params7.nu = 1073741824 := by
          norm_num [params7]
        exact this ▸ hl
      have h1 := strangers_le_mu_cap hd t pl hP q r hr1 hrd
      have h2 := mu_real_mul_le_one _ hc
      have : ((q.strangers r id (pl.regs q) (br_ge_one params7) : ℕ) : ℚ) < 1 := by linarith
      exact_mod_cast (Nat.lt_one_iff.mp (by exact_mod_cast this))

/-- The `Jmax` hypothesis of `fringe_send_real`, for every node that sends wires down. -/
theorem jmax_ok {d : ℕ} (hd : 7 ≤ d) (t : ℕ) (ht1 : 1 ≤ t) (ht : t < tf7 d)
    (pl : Placement params7.br d)
    (hP : OutsiderBoundLe params7 invariantReal d (levelSchedule7 d hd) t pl id)
    (q : KBag 64 d) (r : ℕ) (hr1 : 1 ≤ r) (hrd : r ≤ d)
    (hdown : 0 < (flowSizes7 d hd).down q.l t) :
    q.strangers r id (pl.regs q) (br_ge_one params7) ≤ specJmax ((flowSizes7 d hd).up q.l t) := by
  have hdown' : 0 < flowDown7 d hd q.l t := hdown
  have hmu := strangers_le_mu_cap hd t pl hP q r hr1 hrd
  have hc := capacity7_nonneg d q.l t
  have key : 4095 * capacity params7 d q.l t / 68719476736 ≤ (flowUp7 d hd q.l t : ℚ) →
      q.strangers r id (pl.regs q) (br_ge_one params7) ≤ specJmax (flowUp7 d hd q.l t) :=
    fun h => jmax_of_le _ _ _ hmu (mu_le_of_up_lower _ hc _ h)
  show _ ≤ specJmax (flowUp7 d hd q.l t)
  by_cases h1 : t = 1
  · subst h1
    exact key (up_lower_one d hd q.l hdown')
  · rcases up_lower_or_top_desc d hd t (by omega) ht q.l hdown' with ⟨hq, hs⟩ | h
    · rw [top_desc_no_strangers hd t pl hP q r hr1 hrd hq hs]; exact Nat.zero_le _
    · exact key h

/-- If the parent sends nothing down, nothing arrives from it. -/
theorem fromParentK_eq_empty {d : ℕ} (hd : 7 ≤ d)
    (nets : ℕ → (b : KBag 64 d) → (n : ℕ) → ComparatorNetwork n)
    (v : Equiv.Perm (Fin (64 ^ d))) (t : ℕ) (b : KBag 64 d)
    (h0 : (flowSizes7 d hd).down (b.l - 1) t = 0) :
    fromParentK (flowSizes7 d hd) nets v t b = ∅ := by
  unfold fromParentK
  rw [Finset.image_eq_empty]
  unfold downSet blockOf
  rw [h0]
  apply Finset.filter_false_of_mem
  intro w _ h
  omega

/-- **Fringe send field of the real stage kernel** (Chvátal, Lemma 4.4 parent part). -/
theorem fringeSendField_real {d : ℕ} (hd : 7 ≤ d)
    (nets : ℕ → (b : KBag 64 d) → (n : ℕ) → ComparatorNetwork n)
    (hspecs : RealSpecs hd nets) (v : Equiv.Perm (Fin (64 ^ d))) (t : ℕ) (ht1 : 1 ≤ t)
    (ht : t + 1 ≤ tf7 d)
    (hP : OutsiderBoundLe params7 invariantReal d (levelSchedule7 d hd) t
      (execPlacement (flowSizes7 d hd) nets v t (by omega)) id) :
    FringeSendField hd nets v t (by omega) := by
  intro b r hr1 hrd hb
  have hbl := b.hl
  set q := b.parent (br_ge_one params7) with hqdef
  have hql : q.l = b.l - 1 := rfl
  have hqd : q.l < d := by omega
  set j : Fin 64 := ⟨b.x % 64, Nat.mod_lt _ (by norm_num)⟩ with hjdef
  have hbq : b = q.child j.val j.isLt hqd := by
    ext
    · show b.l = q.l + 1; omega
    · show b.x = 64 * (b.x / 64) + b.x % 64
      omega
  by_cases hdown : (flowSizes7 d hd).down q.l t = 0
  · rw [fromParentK_eq_empty hd nets v t b hdown]
    simp only [KBag.strangers_empty, Nat.cast_zero]
    have : (0 : ℚ) ≤ (((q.strangers r id
        ((execPlacement (flowSizes7 d hd) nets v t (by omega)).regs q)
          (br_ge_one params7) : ℕ) : ℚ)) := Nat.cast_nonneg _
    have := invariantReal.hepsF_nonneg
    positivity
  · have hpos : 0 < (flowSizes7 d hd).down q.l t := Nat.pos_of_ne_zero hdown
    have hspec := hspecs t q (by omega) hpos
    have hJ := jmax_ok hd t ht1 (by omega)
      (execPlacement (flowSizes7 d hd) nets v t (by omega)) hP q r hr1 hrd hpos
    have ha : (wireSets (flowSizes7 d hd) t q).card =
        (flowSizes7 d hd).up q.l t + 64 * (flowSizes7 d hd).down q.l t := by
      rw [wireSets_card (flowSizes7 d hd) (by omega)]
      exact flowSizes7_split d hd q.l t (by omega)
    have hfs := fringe_send_real (flowSizes7 d hd) nets v t (by omega) q hqd j r hr1 _ _ eps
      ha hspec hJ
    rw [← hbq] at hfs
    have e : ((invariantReal.epsF : ℚ) : ℝ) = eps := by
      unfold eps invariantReal invariant7; norm_num
    have hfs' : (((b.strangers (r + 1) id (fromParentK (flowSizes7 d hd) nets v t b) : ℕ) : ℚ) : ℝ) ≤
        ((invariantReal.epsF * ((q.strangers r id
          ((execPlacement (flowSizes7 d hd) nets v t (by omega)).regs q) : ℕ) : ℚ) : ℚ) : ℝ) := by
      push_cast
      rw [e]; exact hfs
    exact_mod_cast hfs'

end Chvatal
