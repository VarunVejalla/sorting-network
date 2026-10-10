module

public import AKS.Chvatal.NodeGeom
public import AKS.Chvatal.Schedule7
public import AKS.Chvatal.StageKernel

@[expose] public section

namespace Chvatal

open Finset

theorem total_mass {d tf : ℕ} (F : FlowSizes d tf) :
    ∀ t, t ≤ tf → (∑ l ∈ range (d + 1), 64 ^ l * F.a l t) = 64 ^ d := by
  intro t
  induction t with
  | zero =>
    intro _
    rw [sum_range_succ']
    have : ∀ l ∈ range d, 64 ^ (l + 1) * F.a (l + 1) 0 = 0 := by
      intro l _; rw [F.ha_init (l + 1) (by omega)]; simp
    rw [sum_eq_zero this, F.ha_root]; simp
  | succ t ih =>
    intro ht
    have ih := ih (by omega)
    have htt : t < tf := by omega
    rw [← ih]
    have h1 : (∑ l ∈ range (d + 1), 64 ^ l * F.a l (t + 1)) =
        (∑ l ∈ range d, 64 ^ (l + 1) * F.down l t) +
          ∑ l ∈ range d, 64 ^ (l + 1) * F.up (l + 1) t := by
      have e : ∀ l ∈ range (d + 1), 64 ^ l * F.a l (t + 1) =
          64 ^ l * (if 1 ≤ l then F.down (l - 1) t else 0) +
            64 ^ l * (if l < d then 64 * F.up (l + 1) t else 0) := by
        intro l hl
        rw [F.hcons l t (by have := mem_range.mp hl; omega) htt, mul_add]
      rw [sum_congr rfl e, sum_add_distrib,
        sum_range_succ' (fun l => 64 ^ l * (if 1 ≤ l then F.down (l - 1) t else 0)),
        sum_range_succ (fun l => 64 ^ l * (if l < d then 64 * F.up (l + 1) t else 0))]
      simp only [show ¬ (1 ≤ 0) by omega, if_false, mul_zero, add_zero,
        show ¬ (d < d) by omega, if_true, le_add_iff_nonneg_left, zero_le]
      congr 1 <;>
      (apply sum_congr rfl; intro l hl; have h := mem_range.mp hl
       simp [h, pow_succ]; try ring)
    have h2 : (∑ l ∈ range (d + 1), 64 ^ l * F.a l t) =
        (∑ l ∈ range d, 64 ^ (l + 1) * F.up (l + 1) t) +
          ∑ l ∈ range d, 64 ^ (l + 1) * F.down l t := by
      have e : ∀ l ∈ range (d + 1), 64 ^ l * F.a l t =
          64 ^ l * F.up l t + 64 ^ (l + 1) * F.down l t := by
        intro l hl
        rw [F.hsplit l t (by have := mem_range.mp hl; omega) htt]; ring
      rw [sum_congr rfl e, sum_add_distrib, sum_range_succ' (fun l => 64 ^ l * F.up l t),
        sum_range_succ (fun l => 64 ^ (l + 1) * F.down l t), F.hup_root t htt,
        F.hdown_leaf t htt]
      simp
    rw [h1, h2]; ring

theorem hpar7 (d : ℕ) (hd : 7 ≤ d) (t : ℕ) (ht1 : 1 ≤ t) (ht : t ≤ tf7 d) :
    ∀ l, l % 2 ≠ t % 2 → (flowSizes7 d hd).a l t = 0 := by
  intro l hl
  show flowA7 d hd l t = 0
  by_cases h1 : t = 1
  · subst h1
    unfold flowA7
    rw [if_neg (by omega), if_pos rfl, if_neg (by omega)]
  · have h2 : 2 ≤ t := by omega
    have hc := cast_flowA7 d hd l t h2 ht
    rw [allocation_inactive _ _ _ (by
      show ¬(t ≤ tf7 d ∧ alpha7 d t ≤ l ∧ l ≤ omega7 d t ∧ l % 2 = t % 2)
      omega)] at hc
    exact_mod_cast hc

theorem total_mass7 (d : ℕ) (hd : 7 ≤ d) (t : ℕ) (ht : t ≤ tf7 d) :
    (∑ l ∈ range (d + 1), (64 : ℚ) ^ l * (flowA7 d hd l t : ℚ)) = 64 ^ d := by
  have h := total_mass (flowSizes7 d hd) t ht
  have h' : (∑ l ∈ range (d + 1), 64 ^ l * flowA7 d hd l t) = 64 ^ d := h
  exact_mod_cast congrArg (fun n : ℕ => (n : ℚ)) h'

theorem hwires7 (d : ℕ) (hd : 7 ≤ d) (t : ℕ) (ht2 : 2 ≤ t) (ht : t ≤ tf7 d) (i : ℕ)
    (hα : alpha7 d t ≤ i) (hω : i < omega7 d t) (hpar : i % 2 = t % 2) :
    (∑ l ∈ Finset.Ioc i d, (64 : ℚ) ^ (l - i - 1) * (flowA7 d hd l t : ℚ)) =
      ((64 : ℚ) ^ d / 64 ^ i - capacity d i t) / 64 := by
  have hid : i ≤ d := by have := omega7_lt_d d t hd ht; omega
  have htot : (∑ j ∈ range (d + 1), (64 : ℚ) ^ j *
      allocation d j t) = ((64 ^ d : ℕ) : ℚ) := by
    have hpow0 : ((64 ^ d : ℕ) : ℚ) = 64 ^ d := by
      norm_num
    rw [hpow0, ← total_mass7 d hd t ht]
    apply sum_congr rfl
    intro l _
    rw [cast_flowA7 d hd l t ht2 ht]
  have hL := lemma31_of_total d hd t ht htot i hα hω.le hpar
  have hsplit : (∑ j ∈ Finset.Icc i d, (64 : ℚ) ^ (j - i) *
      allocation d j t) =
      allocation d i t +
        64 * ∑ l ∈ Finset.Ioc i d, (64 : ℚ) ^ (l - i - 1) * (flowA7 d hd l t : ℚ) := by
    rw [Finset.Icc_eq_cons_Ioc hid, sum_cons, mul_sum]
    simp only [Nat.sub_self, pow_zero, one_mul]
    congr 1
    apply sum_congr rfl
    intro l hl
    have hl' := (Finset.mem_Ioc.mp hl).1
    rw [cast_flowA7 d hd l t ht2 ht]
    obtain ⟨m, hm⟩ : ∃ m, l - i = m + 1 := ⟨l - i - 1, by omega⟩
    rw [hm, show m + 1 - 1 = m by omega, pow_succ]; ring
  have hact : t ≤ tf7 d ∧ alpha7 d t ≤ i ∧ i ≤ omega7 d t ∧ i % 2 = t % 2 :=
    ⟨ht, hα, hω.le, hpar⟩
  have hQ : capacityRatio ≠ 0 := capacityRatio_pos.ne'
  have hpow : ((64 ^ d : ℕ) : ℚ) = 64 ^ d := by
    norm_num
  change (∑ j ∈ Finset.Icc i d, (64 : ℚ) ^ (j - i) *
      allocation d j t) =
      if i = alpha7 d t then ((64 ^ d : ℕ) : ℚ) / 64 ^ i
      else ((64 ^ d : ℕ) : ℚ) / 64 ^ i - capacity d i t / capacityRatio
    at hL
  by_cases hi : i = alpha7 d t
  · rw [if_pos hi] at hL
    rw [alloc_top d hact hi] at hsplit
    rw [hpow] at hL
    linarith
  · rw [if_neg hi, hpow] at hL
    rw [alloc_mid d hact hi (by show i ≠ omega7 d t; omega)] at hsplit
    have : (1 - 1 / capacityRatio) * capacity d i t =
        capacity d i t - capacity d i t / capacityRatio := by
      field_simp
    rw [this] at hsplit
    linarith

def delta2_7 (c : ℚ) : ℚ := (1 / 64 : Rat) / ((4096 : Rat) * (64 : ℚ) ^ 2) * c

theorem delta2_7_eq (c : ℚ) : delta2_7 c = c / 2 ^ 30 := by
  unfold delta2_7; norm_num; ring

/-- Descending top node. -/
theorem tau_top_desc (d : ℕ) (hd : 7 ≤ d) (t : ℕ) (ht2 : 2 ≤ t) (ht : t < tf7 d) (i : ℕ)
    (hact : t ≤ tf7 d ∧ alpha7 d t ≤ i ∧ i ≤ omega7 d t ∧ i % 2 = t % 2)
    (hα : i = alpha7 d t) (hs : alpha7 d t < alpha7 d (t + 1)) :
    (flowUp7 d hd i t : ℚ) = 0 ∧
      (flowDown7 d hd i t : ℚ) = capacity d i t / 64 := by
  constructor
  · have h := (cast_flowUp7 d hd i t ht2 ht).1
    rw [flowUp_top_desc d hact hα hs] at h
    exact h
  · rw [cast_flowDown7 d hd i t ht2 ht,
      flowDown_top_desc d hact hα hs]

/-- Rising top node. -/
theorem tau_top_rise (d : ℕ) (hd : 7 ≤ d) (t : ℕ) (ht2 : 2 ≤ t) (ht : t < tf7 d) (i : ℕ)
    (hact : t ≤ tf7 d ∧ alpha7 d t ≤ i ∧ i ≤ omega7 d t ∧ i % 2 = t % 2)
    (hα : i = alpha7 d t) (hs : alpha7 d (t + 1) < alpha7 d t) :
    (flowUp7 d hd i t : ℚ) = (1 / 64 : Rat) * capacity d i t / ((4096 : Rat) * 64) ∧
      (flowDown7 d hd i t : ℚ) = capacity d i t / 64 - delta2_7 (capacity d i t) := by
  have hns : ¬ alpha7 d t < alpha7 d (t + 1) := by omega
  have hωi : i ≠ omega7 d t := by
    have := alpha7_lt_omega7 d hd t ht2 ht
    omega
  constructor
  · rw [(cast_flowUp7 d hd i t ht2 ht).1,
      flowUp_top_rise d hact hα hns]
  · rw [cast_flowDown7 d hd i t ht2 ht,
      flowDown_mid d hact (fun _ => hns) hωi]
    unfold delta2_7
    ring

/-- Interior node. -/
theorem tau_mid (d : ℕ) (hd : 7 ≤ d) (t : ℕ) (ht2 : 2 ≤ t) (ht : t < tf7 d) (i : ℕ)
    (hact : t ≤ tf7 d ∧ alpha7 d t ≤ i ∧ i ≤ omega7 d t ∧ i % 2 = t % 2)
    (hα : i ≠ alpha7 d t) (hω : i ≠ omega7 d t) :
    (flowUp7 d hd i t : ℚ) =
        (4095 : Rat) * capacity d i t / capacityRatio ∧
      (flowDown7 d hd i t : ℚ) = capacity d i t / 64 - delta2_7 (capacity d i t) := by
  constructor
  · rw [(cast_flowUp7 d hd i t ht2 ht).1,
      flowUp_mid d hact hα (fun h => absurd h hω)]
  · rw [cast_flowDown7 d hd i t ht2 ht,
      flowDown_mid d hact (fun h => absurd h hα) hω]
    unfold delta2_7
    ring

/-- Descending bottom node. -/
theorem tau_bot_desc (d : ℕ) (hd : 7 ≤ d) (t : ℕ) (ht2 : 2 ≤ t) (ht : t < tf7 d) (i : ℕ)
    (hact : t ≤ tf7 d ∧ alpha7 d t ≤ i ∧ i ≤ omega7 d t ∧ i % 2 = t % 2)
    (hα : i ≠ alpha7 d t) (hω : i = omega7 d t) (hs : omega7 d t < omega7 d (t + 1)) :
    (flowUp7 d hd i t : ℚ) =
        (4095 : Rat) * capacity d i t / capacityRatio ∧
      (flowDown7 d hd i t : ℚ) + delta2_7 (capacity d i t) = (64 : ℚ) ^ (d - i - 1) := by
  constructor
  · rw [(cast_flowUp7 d hd i t ht2 ht).1,
      flowUp_mid d hact hα (fun _ => hs)]
  · obtain ⟨g, h, hgh, hdg, hh, -, -, hdown⟩ := val_bot_desc d hd t ht2 ht i hact hα hω hs
    have hc := capacity_eq_pow d i t (7 + h) (by omega)
    have hb := omega7_bounds d t ht2
    have hle : 64 ^ (h + 2) ≤ 64 ^ g := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [hdown, hc, delta2_7_eq, Nat.cast_sub hle, show d - i - 1 = g by omega]
    push_cast
    rw [pow_add, pow_add]
    ring

theorem slackCoeff7_nonneg : 0 ≤ slackCoeff := by
  unfold slackCoeff; norm_num

/-- Rising top node slack inequality. -/
theorem slack_top_rise (c : ℚ) (hc : 0 ≤ c) :
    ((64 : ℚ) - 1) * (delta2_7 c + invMu * siblingFactor * c) -
        ((1 / 64 : Rat) * c / ((4096 : Rat) * 64)) / 2 ≤
      ((64 : ℚ) - 1) * (invMu * siblingFactor * c) +
        slackCoeff * c := by
  rw [delta2_7_eq]
  unfold slackCoeff
  norm_num
  linarith

/-- Interior node slack equality. -/
theorem slack_mid (c : ℚ) :
    ((64 : ℚ) - 1) * (delta2_7 c + invMu * siblingFactor * c) -
        ((4095 : Rat) * c / capacityRatio) / 2 =
      ((64 : ℚ) - 1) * (invMu * siblingFactor * c) +
        slackCoeff * c := by
  unfold delta2_7 slackCoeff capacityRatio
  ring

end Chvatal
