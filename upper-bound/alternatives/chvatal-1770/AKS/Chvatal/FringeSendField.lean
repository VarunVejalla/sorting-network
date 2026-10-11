module

public import AKS.Chvatal.KernelSetup
public import AKS.Chvatal.FringeSendReal
public import AKS.Chvatal.Wires31

@[expose] public section

namespace Chvatal

open Finset

/-- `Jmax` from `π ≥ 4095 c/2^36`: `n ≤ μ c ≤ (128/4095) (π/2)`. -/
theorem jmax_of_le (n π : ℕ) (c : ℚ) (hc : 0 ≤ c) (h : (n : ℚ) ≤ invMu * c)
    (hπ : 4095 * c / 2 ^ 36 ≤ (π : ℚ)) : n ≤ specJmax π := by
  unfold specJmax
  apply Nat.le_floor
  have h4 : ((n : ℚ) : ℝ) ≤ (((128 / 4095 : ℚ) * ((π : ℚ) / 2) : ℚ) : ℝ) := by
    exact_mod_cast (by linarith [mul_le_mul_of_nonneg_right cond44_real hc] :
      (n : ℚ) ≤ (128 / 4095 : ℚ) * ((π : ℚ) / 2))
  push_cast at h4
  exact h4

/-- The invariant at the parent gives `strangers r ≤ μ c` (order `r - 1` in `P`). -/
theorem strangers_le_mu_cap {d : ℕ} (t : ℕ) (pl : Placement 64 d)
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

/-- `Jmax` hypothesis for nodes sending wires down.  Uniform: by `node_facts`, either `π ≥ 4095 c/2^36`,
or `π = 0` at a top-descending node, which has no outsiders (level `0`, or `μ c < 1`). -/
theorem jmax_ok {d : ℕ} (hd : 7 ≤ d) (t : ℕ) (ht1 : 1 ≤ t) (ht : t < tf7 d)
    (pl : Placement 64 d)
    (hP : OutsiderBoundLe d t pl id)
    (q : KBag 64 d) (r : ℕ) (hr1 : 1 ≤ r) (hrd : r ≤ d)
    (hdown : 0 < (flowSizes7 d hd).down q.l t) :
    q.strangers r id (pl.regs q) ≤ specJmax ((flowSizes7 d hd).up q.l t) := by
  obtain ⟨-, -, hlow, -⟩ := node_facts d hd t q.l ht1 ht hdown
  have hmu := strangers_le_mu_cap t pl hP q r hr1 hrd
  rcases hlow with ⟨-, h0 | hc⟩ | h
  · rw [KBag.strangers_eq_zero_of_lt_order q r id _ _ hr1 (by omega)]; exact Nat.zero_le _
  · have h2 := mu_real_mul_le_one _ (by exact_mod_cast hc.trans (by norm_num))
    have : q.strangers r id (pl.regs q) = 0 := by
      have : ((q.strangers r id (pl.regs q) : ℕ) : ℚ) < 1 := by linarith
      exact_mod_cast Nat.lt_one_iff.mp (by exact_mod_cast this)
    rw [this]; exact Nat.zero_le _
  · exact jmax_of_le _ _ _ (capacity_nonneg d q.l t) hmu h

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
