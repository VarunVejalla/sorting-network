module

public import AKS.Chvatal.FlowTableB
public import AKS.Chvatal.NodeGeom
public import AKS.Chvatal.Wires31
public import AKS.Chvatal.RealBlocks

@[expose] public section

/-! # Regression: the current (uniform, equal-block) table satisfies `FlowFacts`

`uniformB d hd : FlowTableB d (tf7 d)` is the per-level table `flowSizes7` viewed per bag
(`a t b = flowA7 b.l t`, `down t b j = flowDown7 b.l t` for all `j`), and
`flowFacts_current` shows `FlowFacts (uniformB d hd) (capacity d) (d - 6) 1 slackCoeff
(4095 / 2^36) (2^30)`.  Nothing downstream is changed. -/

namespace Chvatal

open Finset

section SubtreeSum

variable {br d : ℕ}

/-- A level-dependent sum over a subtree. -/
theorem sum_subtreeBags (hbr : 1 ≤ br) (w : KBag br d) (g : ℕ → ℚ) :
    ∑ z ∈ subtreeBags br d hbr w, g z.l =
      ∑ h ∈ Finset.range (d - w.l + 1), (br : ℚ) ^ h * g (w.l + h) := by
  unfold subtreeBags
  rw [Finset.sum_biUnion (fun h _ h' _ hne => descendants_disjoint hbr w hne)]
  refine Finset.sum_congr rfl fun h hh => ?_
  have hh' : w.l + h ≤ d := by have := Finset.mem_range.1 hh; have := w.hl; omega
  rw [Finset.sum_congr rfl (fun z hz => by rw [(mem_descendants hbr w h z).1 hz |>.1])]
  rw [Finset.sum_const, descendants_card hbr w h hh', nsmul_eq_mul]
  push_cast; rfl

end SubtreeSum

/-- The uniform table `flowSizes7`, viewed as a per-bag table with equal blocks. -/
def uniformB (d : ℕ) (hd : 7 ≤ d) : FlowTableB d (tf7 d) where
  a := fun t b => flowA7 d hd b.l t
  up := fun t b => flowUp7 d hd b.l t
  down := fun t b _ => flowDown7 d hd b.l t
  ha_root := by simp [flowA7, KBag.root]
  ha_init := by
    intro b hb
    have hl : b.l ≠ 0 := by
      intro h0
      apply hb
      have hx := b.hx
      rw [h0] at hx
      exact KBag.ext h0 (by simpa using hx)
    simp [flowA7, hl]
  hup_even := fun t b ht => (flowSizes7 d hd).hup_even b.l t ht
  hup_root := fun t ht => (flowSizes7 d hd).hup_root t ht
  hdown_leaf := fun t b _ ht hb => by
    rw [hb]; exact (flowSizes7 d hd).hdown_leaf t ht
  hsplit := fun t b ht => by
    show flowA7 d hd b.l t = flowUp7 d hd b.l t + ∑ _j : Fin 64, flowDown7 d hd b.l t
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
    exact flowSizes7_split d hd b.l t ht
  hcons := fun t b ht => by
    have h := flowSizes7_cons d hd b.l t ht
    show flowA7 d hd b.l (t + 1) =
      (if 1 ≤ b.l then flowDown7 d hd b.parent.l t else 0) +
      (if hh : b.l < d then ∑ j : Fin 64, flowUp7 d hd (b.child j j.isLt hh).l t else 0)
    have e1 : b.parent.l = b.l - 1 := rfl
    have e2 : ∀ (hh : b.l < d) (j : Fin 64), (b.child j j.isLt hh).l = b.l + 1 := fun _ _ => rfl
    simp only [e1, e2, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
    exact h

namespace FlowTableB

/-- Deficit of the uniform table: depends only on the level. -/
theorem deficit_uniform (d : ℕ) (hd : 7 ≤ d) (t : ℕ) (z : KBag 64 d) :
    (uniformB d hd).deficit t z = (64 : ℚ) ^ (d - z.l) -
      ∑ h ∈ Finset.range (d - z.l + 1), (64 : ℚ) ^ h * (flowA7 d hd (z.l + h) t : ℚ) := by
  unfold deficit
  have := sum_subtreeBags (by norm_num : 1 ≤ 64) z (fun l => (flowA7 d hd l t : ℚ))
  rw [show (∑ y ∈ subtreeBags 64 d (by norm_num) z, (((uniformB d hd).a t y : ℕ) : ℚ)) =
    ∑ y ∈ subtreeBags 64 d (by norm_num) z, (flowA7 d hd y.l t : ℚ) from rfl, this]
  push_cast; rfl

end FlowTableB

section Resid

variable {d : ℕ}

/-- Number of `i < j` in `Fin 64`, plus number of `i > j`, is `63`. -/
theorem card_lt_add_card_gt (j : Fin 64) :
    (Finset.univ.filter (fun i : Fin 64 => i < j)).card +
      (Finset.univ.filter (fun i : Fin 64 => j < i)).card = 63 := by
  revert j; decide +kernel

/-- Core inequality turning `θ_i ≤ Δ` into the residual bound. -/
theorem resid_le_of_theta (th : Fin 64 → ℚ) (Δ p : ℚ) (hΔ : 0 ≤ Δ) (hp0 : 0 ≤ p)
    (hth : ∀ i, th i ≤ Δ) (hhalf : p ≤ 63 * Δ) (j : Fin 64) :
    max 0 ((∑ i with i < j, th i) - p) + max 0 ((∑ i with j < i, th i) - p) ≤ 63 * Δ - p := by
  have h1 : (∑ i with i < j, th i) ≤ ((Finset.univ.filter (fun i : Fin 64 => i < j)).card : ℚ) * Δ := by
    have := Finset.sum_le_card_nsmul (Finset.univ.filter (fun i : Fin 64 => i < j)) th Δ
      (fun i _ => hth i)
    simpa [nsmul_eq_mul] using this
  have h2 : (∑ i with j < i, th i) ≤ ((Finset.univ.filter (fun i : Fin 64 => j < i)).card : ℚ) * Δ := by
    have := Finset.sum_le_card_nsmul (Finset.univ.filter (fun i : Fin 64 => j < i)) th Δ
      (fun i _ => hth i)
    simpa [nsmul_eq_mul] using this
  have hc : ((Finset.univ.filter (fun i : Fin 64 => i < j)).card : ℚ) +
      ((Finset.univ.filter (fun i : Fin 64 => j < i)).card : ℚ) = 63 := by
    exact_mod_cast card_lt_add_card_gt j
  have c1 : (0 : ℚ) ≤ ((Finset.univ.filter (fun i : Fin 64 => i < j)).card : ℚ) * Δ :=
    mul_nonneg (Nat.cast_nonneg _) hΔ
  have c2 : (0 : ℚ) ≤ ((Finset.univ.filter (fun i : Fin 64 => j < i)).card : ℚ) * Δ :=
    mul_nonneg (Nat.cast_nonneg _) hΔ
  have hsum : ((Finset.univ.filter (fun i : Fin 64 => i < j)).card : ℚ) * Δ +
      ((Finset.univ.filter (fun i : Fin 64 => j < i)).card : ℚ) * Δ = 63 * Δ := by
    rw [← add_mul, hc]
  rcases max_cases (0 : ℚ) ((∑ i with i < j, th i) - p) with ⟨e1, _⟩ | ⟨e1, _⟩ <;>
  rcases max_cases (0 : ℚ) ((∑ i with j < i, th i) - p) with ⟨e2, _⟩ | ⟨e2, _⟩ <;>
  · rw [e1, e2]; linarith

end Resid

/-- Per-child deficit bound for the uniform table: every child has `G ≤ τ + Δ`. -/
theorem uniform_deficit_le (d : ℕ) (hd : 7 ≤ d) (t : ℕ) (ht : t < tf7 d)
    (q : KBag 64 d) (hq : q.l < d) (Δ : ℚ)
    (hMs : Inner d t q.l ∧ capacity d q.l t / 64 ≤ (flowDown7 d hd q.l t : ℕ) + Δ ∨
      (64 : ℚ) ^ (d - q.l - 1) ≤ (flowDown7 d hd q.l t : ℕ) + Δ) (i : Fin 64) :
    (uniformB d hd).deficit t (q.child i i.isLt hq) ≤ (flowDown7 d hd q.l t : ℚ) + Δ := by
  rw [FlowTableB.deficit_uniform]
  have hl : (q.child i i.isLt hq).l = q.l + 1 := rfl
  rw [hl]
  rcases hMs with ⟨⟨ht2, hα, hω, hpar⟩, h⟩ | h
  · have hw := hwires7 d hd t ht2 ht.le q.l hα hω hpar
    have hsub : ∑ h ∈ Finset.range (d - (q.l + 1) + 1), (64 : ℚ) ^ h *
        (flowA7 d hd (q.l + 1 + h) t : ℚ) =
        ∑ l ∈ Finset.Ioc q.l d, (64 : ℚ) ^ (l - q.l - 1) * (flowA7 d hd l t : ℚ) := by
      rw [show Finset.Ioc q.l d = Finset.Ico (q.l + 1) (d + 1) by ext x; simp,
        Finset.sum_Ico_eq_sum_range, show d + 1 - (q.l + 1) = d - (q.l + 1) + 1 by omega]
      refine Finset.sum_congr rfl fun h _ => ?_
      rw [show q.l + 1 + h - q.l - 1 = h by omega]
    rw [hsub, hw]
    have e1 : (64 : ℚ) ^ (d - (q.l + 1)) = (64 : ℚ) ^ d / 64 ^ q.l / 64 := by
      have h64 : (64 : ℚ) ^ d = 64 ^ (d - (q.l + 1)) * 64 ^ (q.l + 1) := by
        rw [← pow_add]; congr 1; omega
      rw [h64, pow_succ]
      field_simp
    rw [e1]
    linarith
  · have hnn : 0 ≤ ∑ h ∈ Finset.range (d - (q.l + 1) + 1), (64 : ℚ) ^ h *
        (flowA7 d hd (q.l + 1 + h) t : ℚ) := by positivity
    rw [show d - q.l - 1 = d - (q.l + 1) by omega] at h
    linarith

/-- **Regression theorem.**  The current uniform (equal-block) table satisfies `FlowFacts` with
`η = 1`, `rT = slackCoeff`, `upFrac = 4095/2^36`, `topCap = 2^30`, `lam = d - 6`. -/
theorem flowFacts_current (d : ℕ) (hd : 7 ≤ d) :
    FlowFacts (uniformB d hd) (capacity d) (d - 6) 1 slackCoeff (4095 / 2 ^ 36) (2 ^ 30) where
  parity := fun t b ht1 ht hb => hpar7 d hd t ht1 ht b.l hb
  a_le := fun t b ht1 ht hs => by
    have hdown : 0 < flowDown7 d hd b.l t := by
      by_contra h0
      have : flowDown7 d hd b.l t = 0 := by omega
      simp [uniformB, this] at hs
    obtain ⟨Δ, hF, -, -⟩ := node_facts d hd t b.l ht1 ht hdown
    simpa [uniformB] using hF.a_le
  resid := fun t b hb j ht1 ht hj => by
    have hdown : 0 < flowDown7 d hd b.l t := hj
    obtain ⟨Δ, hF, -, hMs⟩ := node_facts d hd t b.l ht1 ht hdown
    have hth : ∀ i : Fin 64, (uniformB d hd).theta t b hb i ≤ Δ := fun i => by
      unfold FlowTableB.theta
      have := uniform_deficit_le d hd t ht b hb Δ hMs i
      show (uniformB d hd).deficit t (b.child i i.isLt hb) - ((flowDown7 d hd b.l t : ℕ) : ℚ) ≤ Δ
      linarith
    have key := resid_le_of_theta (fun i => (uniformB d hd).theta t b hb i) Δ
      (((uniformB d hd).up t b : ℚ) / 2) hF.nonneg (by positivity) hth
      (by simpa [uniformB] using hF.half) j
    have hs : 63 * Δ - (((uniformB d hd).up t b : ℚ) / 2) ≤ slackCoeff * capacity d b.l t := by
      simpa [uniformB] using hF.slack
    unfold FlowTableB.residAt
    linarith
  fringe := fun t b ht1 ht hs => by
    have hdown : 0 < flowDown7 d hd b.l t := by
      by_contra h0
      have : flowDown7 d hd b.l t = 0 := by omega
      simp [uniformB, this] at hs
    obtain ⟨Δ, -, hlow, -⟩ := node_facts d hd t b.l ht1 ht hdown
    rcases hlow with ⟨h1, h2⟩ | h
    · exact Or.inl ⟨h1, h2⟩
    · right
      show 4095 / 2 ^ 36 * capacity d b.l t ≤ ((flowUp7 d hd b.l t : ℕ) : ℚ)
      have h' : 4095 * capacity d b.l t / 2 ^ 36 ≤ ((flowUp7 d hd b.l t : ℕ) : ℚ) := h
      linarith
  geom := fun t b ht1 ht hs hbig => by
    have hdown : 0 < flowDown7 d hd b.l t := by
      by_contra h0
      have : flowDown7 d hd b.l t = 0 := by omega
      simp [uniformB, this] at hs
    obtain ⟨G⟩ := nodeGeom_exists d hd b.l t hdown hbig ht
    refine ⟨⟨G.m, G.n, G.f, fun _ => G.b, ?_, G.ha, G.hup, fun _ => G.hdown, G.hm1, G.hm2, G.hn,
      G.hf⟩⟩
    simpa using G.hm
  root := by
    refine ⟨by simp [uniformB, flowUp7, KBag.root], fun j => ?_⟩
    simp [uniformB, flowDown7, KBag.root]
  one := fun b hb => by simp [uniformB, flowA7, hb]
  final := fun b => by
    simp only [uniformB]
    rw [flowA7_tf d hd b.l]
    by_cases h : b.l = d - 6
    · rw [if_pos h, if_pos h, show d - (d - 6) = 6 by omega]
    · rw [if_neg h, if_neg h]

end Chvatal
