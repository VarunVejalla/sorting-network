module

public import AKS.Paterson.DeepPurity

/-! # Descendant ownership and the retained deep region -/

@[expose] public section

namespace Paterson.Bags

open Finset BigOperators

theorem mem_subregs_of_desc {k : ℕ} (pl : Placement k)
    (b c : Bag k) (hle : b.l ≤ c.l) (hdesc : c.x / 2 ^ (c.l - b.l) = b.x)
    {r : Fin (2 ^ k)} (hr : r ∈ pl.regs c) :
    r ∈ subregs pl b := by
  unfold subregs
  split
  case isTrue h =>
    -- b.l < k: subregs = pl.regs b ∪ subregs(left) ∪ subregs(right)
    rcases eq_or_lt_of_le hle with heq | hlt
    · -- c.l = b.l, so c = b
      have hcb : c = b := by
        have : c.l - b.l = 0 := by omega
        rw [this, pow_zero, Nat.div_one] at hdesc
        exact Bag.ext heq.symm hdesc
      subst hcb
      exact Finset.mem_union_left _ (Finset.mem_union_left _ hr)
    · -- c.l > b.l: c is in left or right subtree
      set d := c.l - b.l
      have hd1 : d ≥ 1 := by omega
      -- c.x / 2^(d-1) is either 2*b.x or 2*b.x + 1
      have hdiv : c.x / 2 ^ (d - 1) = 2 * b.x + c.x / 2 ^ (d - 1) % 2 := by
        have key : c.x / 2 ^ (d - 1) / 2 = b.x := by
          rw [Nat.div_div_eq_div_mul,
              show 2 ^ (d - 1) * 2 = 2 ^ d from by
                rw [← pow_succ, show d - 1 + 1 = d from by omega]]
          exact hdesc
        have := Nat.div_add_mod (c.x / 2 ^ (d - 1)) 2
        omega
      by_cases hbit : c.x / 2 ^ (d - 1) % 2 = 0
      · -- Left subtree
        have hdesc_left : c.x / 2 ^ (c.l - (b.left h).l) = (b.left h).x := by
          show c.x / 2 ^ (c.l - (b.l + 1)) = 2 * b.x
          rw [show c.l - (b.l + 1) = d - 1 from by omega]
          omega
        exact Finset.mem_union_left _
          (Finset.mem_union_right _
            (mem_subregs_of_desc pl (b.left h) c (by show b.l + 1 ≤ c.l; omega)
              hdesc_left hr))
      · -- Right subtree
        have hdesc_right : c.x / 2 ^ (c.l - (b.right h).l) = (b.right h).x := by
          show c.x / 2 ^ (c.l - (b.l + 1)) = 2 * b.x + 1
          rw [show c.l - (b.l + 1) = d - 1 from by omega]
          omega
        exact Finset.mem_union_right _
          (mem_subregs_of_desc pl (b.right h) c (by show b.l + 1 ≤ c.l; omega)
            hdesc_right hr)
  case isFalse h =>
    -- b.l ≥ k (leaf): c = b
    have heql : c.l = b.l := by have := c.hl; omega
    have hcb : c = b := by
      have : c.l - b.l = 0 := by omega
      rw [this, pow_zero, Nat.div_one] at hdesc
      exact Bag.ext heql hdesc
    subst hcb; exact hr
termination_by c.l - b.l
decreasing_by all_goals show c.l - (b.l + 1) < c.l - b.l; omega

def deepRegisters {k : ℕ} (pl : StoredPlacement k) (hk : 6 ≤ k) : Finset (Fin (2 ^ k)) :=
  univ.biUnion fun x : Fin 64 ↦ subregs pl.collapse ⟨6, x.val, hk, by simpa using x.isLt⟩

theorem deepRegisters_card {root : ℚ} (hr : 0 ≤ root) {k t : ℕ} (hk : 6 ≤ k)
    (hc : fastParams.minCapacity ≤ capacity fastParams root t 0)
    (pl : StoredPlacement k) (ha : AllocationInvariant root t pl) (hp : t % 2 = 0) :
    (deepRegisters pl hk).card = 64 * subtreeTotal root k t 6 := by
  unfold deepRegisters
  rw [card_biUnion]
  · have hp6 : (t + 6) % 2 = 0 := by omega
    have hs (x : Fin 64) :
        (subregs pl.collapse (⟨6, x.val, hk, by simpa using x.isLt⟩ : Bag k)).card =
          subtreeTotal root k t 6 := by
      have h := allocated_subtree_card hr hc pl ha
        (⟨6, x.val, hk, by simpa using x.isLt⟩ : Bag k) (by change 1 ≤ 6; omega)
      simpa only [subtreeContent, if_pos hp6] using h
    simp only [hs, sum_const, card_univ, Fintype.card_fin, Nat.nsmul_eq_mul]
  · intro x _ y _ hxy
    apply subregs_disjoint' pl.collapse
    · intro heq
      exact hxy (Fin.ext (congrArg Bag.x heq))
    · rfl

theorem mem_deepRegisters_of_owner {k : ℕ} (pl : StoredPlacement k) (hk : 6 ≤ k)
    (b : Bag k) (hb : 6 ≤ b.l) {i : Fin (2 ^ k)} (hi : i ∈ pl.regs b) :
    i ∈ deepRegisters pl hk := by
  let c := b.ancestor (b.l - 6)
  have hcl : c.l = 6 := by change b.l - (b.l - 6) = 6; omega
  have hcx : c.x < 64 := by have := c.hx; simpa only [hcl] using this
  have hm : i ∈ subregs pl.collapse c := by
    apply mem_subregs_of_desc pl.collapse c b (by rw [hcl]; exact hb)
    · change b.x / 2 ^ (b.l - c.l) = b.x / 2 ^ (b.l - 6)
      rw [hcl]
    · rw [pl.collapse_regs_of_pos b (by omega)]
      exact hi
  refine mem_biUnion.mpr ⟨⟨c.x, hcx⟩, mem_univ _, ?_⟩
  have heq : (⟨6, c.x, hk, by simpa using hcx⟩ : Bag k) = c := Bag.ext hcl.symm rfl
  simpa only [heq] using hm

theorem deepRegisters_disjoint_upper {root : ℚ} {k t : ℕ} (hk : 6 ≤ k)
    (pl : StoredPlacement k) (ha : AllocationInvariant root t pl) (hp : t % 2 = 0) :
    Disjoint (deepRegisters pl hk) (upperRegisters pl (by omega)) := by
  rw [disjoint_left]
  intro i hd hu
  obtain ⟨x, _, hx⟩ := mem_biUnion.mp hd
  obtain ⟨c, hc, _, hi⟩ := mem_subregs_exists_bag' pl.collapse
    (⟨6, x.val, hk, by simpa using x.isLt⟩ : Bag k) hx
  have hcl : 6 ≤ c.l := hc
  rw [pl.collapse_regs_of_pos c (by omega)] at hi
  have hout : i ∉ upperRegisters pl (by omega) := by
    intro hiU
    rcases mem_union.mp hiU with hi024 | hi4
    · rcases mem_union.mp hi024 with hi02 | hi2
      · rcases mem_union.mp hi02 with hic | hir
        · exact disjoint_left.mp (pl.cold_disjoint c) hic hi
        · exact disjoint_left.mp (pl.disjoint c (Bag.root k)
            (by intro h; have := congrArg Bag.l h; change c.l = 0 at this; omega)) hi hir
      · obtain ⟨y, _, hy⟩ := mem_biUnion.mp hi2
        exact disjoint_left.mp (pl.disjoint c _
          (by intro h; have := congrArg Bag.l h; change c.l = 2 at this; omega)) hi hy
    · obtain ⟨y, _, hy⟩ := mem_biUnion.mp hi4
      exact disjoint_left.mp (pl.disjoint c _
        (by intro h; have := congrArg Bag.l h; change c.l = 4 at this; omega)) hi hy
  exact hout hu

theorem upper_deep_complete {root : ℚ} {k t : ℕ} (hk : 6 ≤ k)
    (pl : StoredPlacement k) (ha : AllocationInvariant root t pl) (hp : t % 2 = 0) :
    upperRegisters pl (by omega) ∪ deepRegisters pl hk = univ := by
  apply eq_univ_of_forall
  intro i
  by_cases hu : i ∈ upperRegisters pl (by omega)
  · exact mem_union_left _ hu
  · obtain ⟨b, hb, hi⟩ := outside_upper_has_deep_owner (by omega) pl ha hp hu
    exact mem_union_right _ (mem_deepRegisters_of_owner pl hk b hb hi)

end Paterson.Bags
