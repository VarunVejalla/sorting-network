module

public import AKS.Chvatal.FlowSizes7
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

/-- What the Lemma 4.1/4.2/4.4 arguments need to know about a node with capacity `c`, `a` wires,
`π` up and `τ` down per child, for a "deficit" `Δ` (`Δ = 0` at a top-descending node, `Δ = c/2^30`
at every other sending node). -/
structure NodeFacts (c a π τ Δ : ℚ) : Prop where
  a_le : a ≤ c
  nonneg : 0 ≤ Δ
  up_le : π ≤ 64 * Δ
  half : π / 2 ≤ 63 * Δ
  slack : 63 * Δ - π / 2 ≤ slackCoeff * c

/-- Facts of a sending node, from its `NodeShape`.  Besides `NodeFacts`: either `π = 0` (a
top-descending node, at level `0` or with `c ≤ 2^30`) or `π ≥ 4095 c/2^36`; and the source of the
Lemma 4.1 bound on keys below a child: either an ordinary interior stage with `c/64 ≤ τ + Δ`, or
the trivial bound `64^(d-i-1) ≤ τ + Δ`. -/
theorem NodeShape.facts {d t i a u n : ℕ} (h : NodeShape d t i a u n) (hn : 0 < n) :
    ∃ Δ : ℚ, NodeFacts (capacity d i t) a u n Δ ∧
      ((u = 0 ∧ (i = 0 ∨ capacity d i t ≤ 2 ^ 30)) ∨ 4095 * capacity d i t / 2 ^ 36 ≤ u) ∧
      ((Inner d t i ∧ capacity d i t / 64 ≤ n + Δ) ∨ (64 : ℚ) ^ (d - i - 1) ≤ n + Δ) := by
  cases h with
  | off => omega
  | topDesc g e hi h0 =>
    rw [capacity_eq_pow d i t (g + 1) (by omega)]
    have hX : (0 : ℚ) < 64 ^ g := by positivity
    have h5 : g ≤ 4 → ((64 ^ (g + 1) : ℕ) : ℚ) ≤ 2 ^ 30 := fun h => by
      have : 64 ^ (g + 1) ≤ 64 ^ 5 := Nat.pow_le_pow_right (by norm_num) (by omega)
      exact_mod_cast this.trans (by norm_num)
    refine ⟨0, ⟨?_, ?_, ?_, ?_, ?_⟩, Or.inl ⟨rfl, h0.imp id h5⟩, Or.inl ⟨hi, ?_⟩⟩ <;>
      push_cast <;> norm_num [pow_succ, slackCoeff]
  | topRise f e h0 =>
    rw [capacity_eq_pow d i t (6 + f) (by omega)]
    have hX : (0 : ℚ) < 64 ^ f := by positivity
    refine ⟨64 ^ (1 + f), ⟨?_, ?_, ?_, ?_, ?_⟩, Or.inr ?_, ?_⟩ <;> push_cast <;>
      norm_num [pow_add, slackCoeff] <;> try linarith
    rcases h0 with hi | ⟨rfl, rfl⟩
    · exact Or.inl ⟨hi, by linarith⟩
    · right; rw [show d - 1 - 1 = 5 + f by omega]; norm_num [pow_add]; linarith
  | mid g e hi =>
    rw [capacity_eq_pow d i t (7 + g) (by omega)]
    have hX : (0 : ℚ) < 64 ^ g := by positivity
    have hle : 64 ^ (1 + g) ≤ 64 ^ (7 + g) := Nat.pow_le_pow_right (by norm_num) (by omega)
    refine ⟨64 ^ (2 + g), ⟨?_, ?_, ?_, ?_, ?_⟩, Or.inr ?_, Or.inl ⟨hi, ?_⟩⟩ <;>
      push_cast [Nat.cast_sub hle] <;> norm_num [pow_add, slackCoeff] <;> linarith
  | botDesc g h hgh hg e hd =>
    rw [capacity_eq_pow d i t (7 + h) (by omega), show d - i - 1 = g by omega]
    have hX : (0 : ℚ) < 64 ^ h := by positivity
    have hle : 64 ^ (h + 1) ≤ 64 ^ (g + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have hle2 : 64 ^ (h + 2) ≤ 64 ^ g := Nat.pow_le_pow_right (by norm_num) (by omega)
    have hg' : (64 : ℚ) ^ g ≤ 64 ^ 6 * 64 ^ h := by
      rw [← pow_add]; exact pow_le_pow_right₀ (by norm_num) (by omega)
    refine ⟨64 ^ (h + 2), ⟨?_, ?_, ?_, ?_, ?_⟩, Or.inr ?_, Or.inr ?_⟩ <;>
      push_cast [Nat.cast_sub hle, Nat.cast_sub hle2] <;> norm_num [pow_add, slackCoeff] <;>
      linarith [(by positivity : (0 : ℚ) < 64 ^ (h + 1))]
  | botRise => omega

/-- **Classification of sending nodes** (`1 ≤ t < t_f`): `NodeShape` (the single case split on node
types) gives `NodeFacts`, the fringe dichotomy and the source of the Lemma 4.1 bound. -/
theorem node_facts (d : ℕ) (hd : 7 ≤ d) (t l : ℕ) (ht1 : 1 ≤ t) (ht : t < tf7 d)
    (hdown : 0 < (flowSizes7 d hd).down l t) :
    ∃ Δ : ℚ, NodeFacts (capacity d l t) ((flowSizes7 d hd).a l t : ℕ)
        ((flowSizes7 d hd).up l t : ℕ) ((flowSizes7 d hd).down l t : ℕ) Δ ∧
      ((flowSizes7 d hd).up l t = 0 ∧ (l = 0 ∨ capacity d l t ≤ 2 ^ 30) ∨
        4095 * capacity d l t / 2 ^ 36 ≤ ((flowSizes7 d hd).up l t : ℕ)) ∧
      (Inner d t l ∧ capacity d l t / 64 ≤ ((flowSizes7 d hd).down l t : ℕ) + Δ ∨
        (64 : ℚ) ^ (d - l - 1) ≤ ((flowSizes7 d hd).down l t : ℕ) + Δ) :=
  (node_shape d hd t l ht1 ht).facts hdown

end Chvatal
