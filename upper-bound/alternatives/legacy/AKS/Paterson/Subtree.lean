module

public import AKS.Paterson.Interior
public import AKS.Bags.Subtree

/-! # Subtree rank balance from the Paterson invariant

The inherited finite-tree geometric-series argument is reused with separate
invariant and decay parameters, an arbitrary placement, and explicit parity.
No Seiferas capacity or scheduler constraints are assumed.
-/

@[expose] public section

namespace Paterson.Bags

open Finset

theorem subtree_intrusion (p : Params) (k : ℕ) (root : ℚ) (hr : 0 ≤ root)
    (pl : Placement k)
    (perm : Fin (2 ^ k) → Fin (2 ^ k))
    (t : ℕ)
    (b : Bag k)
    (hempty : ∀ c : Bag k, b.l ≤ c.l → (t + c.l) % 2 ≠ 0 → pl.regs c = ∅)
    (ih : ∀ (b : Bag k) (j : ℕ), 1 ≤ j →
      (b.strangers j perm (pl.regs b) : ℚ) ≤
      p.mu * p.delta ^ (j - 1) * capacity p root t b.l)
    (hparity : (t + b.l) % 2 ≠ 0) :
    (((subregs pl b).filter
        (fun r ↦ ¬b.Native r perm)).card : ℚ) ≤
    2 * p.mu * p.delta * p.A / (1 - (2 * p.delta * p.A) ^ 2) * capacity p root t b.l := by
  set cap_b := capacity p root t b.l
  -- Strategy: bound non-native items per descendant bag, sum over the tree.
  -- By filter_not_native_le_strangers + IH: at descendant c (distance d from b):
  --   |(pl.regs c).filter(¬b.Native)| ≤ γ · ε^d · cap(c.l) = γ · (εA)^d · cap_b
  -- Wrong-parity levels are empty (bagCard_odd_eq_zero).
  -- At odd distance d: 2^d descendants, each contributing ≤ γ·(εA)^d·cap_b.
  --   Total = γ · (2εA)^d · cap_b.
  -- Even distances (including d=0): empty regs → 0 contribution.
  -- Sum over odd d: γ · cap_b · Σ_{m} (2εA)^(2m+1) ≤ 2γεA/(1-(2εA)²) · cap_b.

  -- Helper: capacity factors
  have cap_factor : ∀ d, capacity p root t (b.l + d) = p.A ^ d * cap_b := by
    intro d; induction d with
    | zero => simp [cap_b]
    | succ n ih_n =>
      rw [show b.l + (n + 1) = (b.l + n) + 1 by omega, capacity_level_succ, ih_n]; ring

  -- Helper: per-descendant-bag bound
  have per_bag : ∀ (c : Bag k), b.l ≤ c.l → c.x / 2 ^ (c.l - b.l) = b.x →
      (((pl.regs c).filter (fun r ↦ ¬b.Native r perm)).card : ℚ) ≤
      p.mu * (p.delta * p.A) ^ (c.l - b.l) * cap_b := by
    intro c hle hdesc
    calc (((pl.regs c).filter (fun r ↦ ¬b.Native r perm)).card : ℚ)
        ≤ ↑(c.strangers (c.l - b.l + 1) perm (pl.regs c)) := by
          exact_mod_cast filter_not_native_le_strangers b c perm (pl.regs c) hle hdesc
      _ ≤ p.mu * p.delta ^ (c.l - b.l) * capacity p root t c.l := by
          have h := ih c (c.l - b.l + 1) (by omega)
          rwa [show c.l - b.l + 1 - 1 = c.l - b.l by omega] at h
      _ = p.mu * (p.delta * p.A) ^ (c.l - b.l) * cap_b := by
          rw [show c.l = b.l + (c.l - b.l) by omega, cap_factor,
              show b.l + (c.l - b.l) - b.l = c.l - b.l by omega]
          rw [mul_pow]; ring

  -- Helper: wrong-parity bags have empty regs
  have parity_empty : ∀ l, b.l ≤ l → (t + l) % 2 ≠ 0 → ∀ (c : Bag k), c.l = l →
      (pl.regs c).card = 0 := by
    intro l hbl hpar c hcl
    rw [hempty c (hcl ▸ hbl) (hcl ▸ hpar), card_empty]

  -- Abbreviations
  set eA := p.delta * p.A
  have heA_pos : (0 : ℚ) < eA := mul_pos p.delta_pos (by linarith [p.A_gt_one])
  have h4eA2 : 4 * eA ^ 2 < 1 := by
    show 4 * (p.delta * p.A) ^ 2 < 1
    calc 4 * (p.delta * p.A) ^ 2 = (2 * p.delta * p.A) ^ 2 := by ring
      _ < 1 := by convert p.geometric using 1 <;> ring
  have h1m4 : (0 : ℚ) < 1 - 4 * eA ^ 2 := by linarith
  have hcap_nn : (0 : ℚ) ≤ cap_b := capacity_nonneg p hr t b.l
  -- Child descent lemmas
  have left_desc : ∀ (c : Bag k), b.l ≤ c.l → c.x / 2 ^ (c.l - b.l) = b.x →
      ∀ (hck : c.l < k), (c.left hck).x / 2 ^ ((c.left hck).l - b.l) = b.x := by
    intro c _ hdesc hck
    show 2 * c.x / 2 ^ (c.l + 1 - b.l) = b.x
    rw [show c.l + 1 - b.l = (c.l - b.l) + 1 from by omega, pow_succ,
        Nat.mul_comm (2 ^ (c.l - b.l)) 2, ← Nat.div_div_eq_div_mul,
        Nat.mul_div_cancel_left _ (by omega : 0 < 2)]
    exact hdesc
  have right_desc : ∀ (c : Bag k), b.l ≤ c.l → c.x / 2 ^ (c.l - b.l) = b.x →
      ∀ (hck : c.l < k), (c.right hck).x / 2 ^ ((c.right hck).l - b.l) = b.x := by
    intro c _ hdesc hck
    show (2 * c.x + 1) / 2 ^ (c.l + 1 - b.l) = b.x
    rw [show c.l + 1 - b.l = (c.l - b.l) + 1 from by omega, pow_succ,
        Nat.mul_comm (2 ^ (c.l - b.l)) 2, ← Nat.div_div_eq_div_mul]
    have : (2 * c.x + 1) / 2 = c.x := by omega
    rw [this]; exact hdesc
  -- Main claim: for wrong-parity descendant cur at distance d = cur.l - b.l,
  -- F(cur) ≤ 2γ·eA^(d+1)/(1-4eA²)·cap_b.
  -- Specializing at cur = b (d = 0) gives the target (after ring).
  suffices hmain : ∀ (n : ℕ) (cur : Bag k),
      k - cur.l = n →
      b.l ≤ cur.l → cur.x / 2 ^ (cur.l - b.l) = b.x →
      (t + cur.l) % 2 ≠ 0 →
      (((subregs pl cur).filter (fun r ↦ ¬b.Native r perm)).card : ℚ) ≤
      2 * p.mu * eA ^ (cur.l - b.l + 1) / (1 - 4 * eA ^ 2) * cap_b by
    have h := hmain (k - b.l) b (by omega) le_rfl (by simp) hparity
    simp only [show b.l - b.l = 0 by omega] at h
    calc (((subregs pl b).filter (fun r ↦ ¬b.Native r perm)).card : ℚ) ≤
          2 * p.mu * eA ^ (0 + 1) / (1 - 4 * eA ^ 2) * cap_b := h
      _ = 2 * p.mu * p.delta * p.A / (1 - (2 * p.delta * p.A) ^ 2) * cap_b := by ring
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih_n =>
  intro cur hn hle hdesc hpar
  -- Case 1: cur.l ≥ k (leaf) → subregs = regs, empty by parity
  by_cases hck : cur.l < k
  · -- Case 2: cur.l < k → decompose
    -- regs(cur) empty by wrong parity
    have hregs_empty : (pl.regs cur).card = 0 := parity_empty cur.l hle hpar cur rfl
    have hregs_filter : ((pl.regs cur).filter (fun r ↦ ¬b.Native r perm)).card = 0 := by
      rw [← Nat.le_zero, ← hregs_empty]; exact Finset.card_filter_le _ _
    -- Children
    let cl := cur.left hck
    let cr := cur.right hck
    let d := cur.l - b.l
    have hcl_l : cl.l = cur.l + 1 := rfl
    have hcr_l : cr.l = cur.l + 1 := rfl
    have hcl_le : b.l ≤ cl.l := by omega
    have hcr_le : b.l ≤ cr.l := by omega
    have hcl_desc := left_desc cur hle hdesc hck
    have hcr_desc := right_desc cur hle hdesc hck
    -- Children's regs bound by per_bag
    have hcl_pb := per_bag cl hcl_le hcl_desc
    have hcr_pb := per_bag cr hcr_le hcr_desc
    rw [show cl.l - b.l = d + 1 from by omega] at hcl_pb
    rw [show cr.l - b.l = d + 1 from by omega] at hcr_pb
    -- Bound each child's subregs by: per_bag(child) + child's subtree
    -- For each child ch (right parity): F(ch) ≤ per_bag(ch) + F(ch.left) + F(ch.right)
    -- Grandchildren are wrong parity → bounded by IH (if they exist)
    by_cases hck2 : cl.l < k
    · -- Case 2b: grandchildren exist
      have hcrk : cr.l < k := by rw [hcr_l, ← hcl_l]; exact hck2
      -- Grandchildren (wrong parity, level cur.l + 2)
      have hgc_par : (t + (cur.l + 2)) % 2 ≠ 0 := by omega
      have hgc_n : k - (cur.l + 2) < n := by omega
      -- IH bound for each grandchild
      have hgc_bound : ∀ (gc : Bag k), gc.l = cur.l + 2 →
          b.l ≤ gc.l → gc.x / 2 ^ (gc.l - b.l) = b.x →
          (((subregs pl gc).filter (fun r ↦ ¬b.Native r perm)).card : ℚ) ≤
          2 * p.mu * eA ^ (d + 2 + 1) / (1 - 4 * eA ^ 2) * cap_b := by
        intro gc hgcl hgcle hgcdesc
        have hgcpar : (t + gc.l) % 2 ≠ 0 := by rw [hgcl]; exact hgc_par
        have := ih_n _ hgc_n gc (by omega) hgcle hgcdesc hgcpar
        rwa [show gc.l - b.l = d + 2 from by omega] at this
      -- Grandchild level lemmas (omega can't see through Bag projections)
      have hcll_l : (cl.left hck2).l = cur.l + 2 := by show cl.l + 1 = cur.l + 2; omega
      have hclr_l : (cl.right hck2).l = cur.l + 2 := by show cl.l + 1 = cur.l + 2; omega
      have hcrl_l : (cr.left hcrk).l = cur.l + 2 := by show cr.l + 1 = cur.l + 2; omega
      have hcrr_l : (cr.right hcrk).l = cur.l + 2 := by show cr.l + 1 = cur.l + 2; omega
      have hgc_le : cur.l + 2 ≥ b.l := by omega
      have h_cll := hgc_bound (cl.left hck2) hcll_l (hcll_l ▸ hgc_le)
        (left_desc cl hcl_le hcl_desc hck2)
      have h_clr := hgc_bound (cl.right hck2) hclr_l (hclr_l ▸ hgc_le)
        (right_desc cl hcl_le hcl_desc hck2)
      have h_crl := hgc_bound (cr.left hcrk) hcrl_l (hcrl_l ▸ hgc_le)
        (left_desc cr hcr_le hcr_desc hcrk)
      have h_crr := hgc_bound (cr.right hcrk) hcrr_l (hcrr_l ▸ hgc_le)
        (right_desc cr hcr_le hcr_desc hcrk)
      -- Bound each child's subregs
      have h_cl : (((subregs pl cl).filter (fun r ↦ ¬b.Native r perm)).card : ℚ) ≤
          p.mu * eA ^ (d + 1) * cap_b +
          2 * (2 * p.mu * eA ^ (d + 2 + 1) / (1 - 4 * eA ^ 2) * cap_b) := by
        rw [subregs_filter_card_split' pl cl hck2]; push_cast; linarith [hcl_pb, h_cll, h_clr]
      have h_cr : (((subregs pl cr).filter (fun r ↦ ¬b.Native r perm)).card : ℚ) ≤
          p.mu * eA ^ (d + 1) * cap_b +
          2 * (2 * p.mu * eA ^ (d + 2 + 1) / (1 - 4 * eA ^ 2) * cap_b) := by
        rw [subregs_filter_card_split' pl cr hcrk]; push_cast; linarith [hcr_pb, h_crl, h_crr]
      -- Assemble and simplify
      -- LHS = 0 + F(cl) + F(cr) ≤ 2*(per_bag + 2*IH)
      -- = 2γeA^(d+1)cap + 4·2γeA^(d+3)/(1-4eA²)cap
      -- Key identity: 2x + 4eA²·(2x/(1-4eA²)) = 2x/(1-4eA²)
      rw [subregs_filter_card_split' pl cur hck]; push_cast
      calc (↑((pl.regs cur).filter (fun r ↦ ¬b.Native r perm)).card : ℚ) +
            ↑((subregs pl cl).filter (fun r ↦ ¬b.Native r perm)).card +
            ↑((subregs pl cr).filter (fun r ↦ ¬b.Native r perm)).card
          ≤ 0 + (p.mu * eA ^ (d + 1) * cap_b +
              2 * (2 * p.mu * eA ^ (d + 2 + 1) / (1 - 4 * eA ^ 2) * cap_b)) +
            (p.mu * eA ^ (d + 1) * cap_b +
              2 * (2 * p.mu * eA ^ (d + 2 + 1) / (1 - 4 * eA ^ 2) * cap_b)) := by
            have := hregs_filter; push_cast [this]; linarith [h_cl, h_cr]
        _ = 2 * p.mu * eA ^ (d + 1) * cap_b +
            4 * eA ^ 2 * (2 * p.mu * eA ^ (d + 1) / (1 - 4 * eA ^ 2) * cap_b) := by ring
        _ = 2 * p.mu * eA ^ (d + 1) / (1 - 4 * eA ^ 2) * cap_b := by
            field_simp [ne_of_gt h1m4]; ring
    · -- Case 2a: cur.l + 1 = k → children are leaves (subregs = regs)
      have hcl_leaf : ¬cl.l < k := hck2
      have hcr_leaf : ¬cr.l < k := by rw [hcr_l, ← hcl_l]; exact hck2
      -- subregs(child) = regs(child) since child.l ≥ k
      rw [subregs_filter_card_split' pl cur hck, subregs, dif_neg hcl_leaf, subregs, dif_neg hcr_leaf]
      push_cast
      calc (↑((pl.regs cur).filter (fun r ↦ ¬b.Native r perm)).card : ℚ) +
            ↑((pl.regs cl).filter (fun r ↦ ¬b.Native r perm)).card +
            ↑((pl.regs cr).filter (fun r ↦ ¬b.Native r perm)).card
          ≤ 0 + p.mu * eA ^ (d + 1) * cap_b + p.mu * eA ^ (d + 1) * cap_b := by
            have := hregs_filter; push_cast [this]; linarith [hcl_pb, hcr_pb]
        _ = 2 * p.mu * eA ^ (d + 1) * cap_b := by ring
        _ ≤ 2 * p.mu * eA ^ (d + 1) / (1 - 4 * eA ^ 2) * cap_b := by
            rw [show 2 * p.mu * eA ^ (d + 1) / (1 - 4 * eA ^ 2) * cap_b =
              2 * p.mu * eA ^ (d + 1) * cap_b / (1 - 4 * eA ^ 2) from by ring,
              le_div_iff₀ h1m4]
            have hnn : (0 : ℚ) ≤ 2 * p.mu * eA ^ (d + 1) * cap_b :=
              mul_nonneg (mul_nonneg (by linarith [p.mu_pos]) (pow_nonneg heA_pos.le _)) hcap_nn
            exact mul_le_of_le_one_right hnn (by nlinarith [sq_nonneg eA])
  · -- Case 1: cur.l ≥ k → subregs = regs, empty by parity
    have hcur_leaf : ¬cur.l < k := hck
    rw [subregs, dif_neg hcur_leaf]
    have hregs_empty : (pl.regs cur).card = 0 := parity_empty cur.l hle hpar cur rfl
    have hfilt0 : ((pl.regs cur).filter (fun r ↦ ¬b.Native r perm)).card = 0 := by
      rw [← Nat.le_zero, ← hregs_empty]; exact Finset.card_filter_le _ _
    simp only [hfilt0, Nat.cast_zero]
    exact mul_nonneg (div_nonneg (mul_nonneg (by linarith [p.mu_pos]) (pow_nonneg heA_pos.le _))
      h1m4.le) hcap_nn


end Paterson.Bags
