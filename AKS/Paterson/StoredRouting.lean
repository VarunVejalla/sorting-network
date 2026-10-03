module

public import AKS.Paterson.StoredStage
public import AKS.Paterson.Subtree

/-! # Connecting storage-aware ownership to interior register flow -/

@[expose] public section

namespace Paterson.Bags.StoredPlacement

open Finset

/-- The inherited geometric descendant bound applies below the root with
storage present. Only descendant parity is needed; the stored wires packaged
at the root need not satisfy the root's empty-level parity convention. -/
theorem subtree_intrusion_stored {k : ℕ} (pl : StoredPlacement k)
    (root : ℚ) (hr : 0 ≤ root) (t : ℕ)
    (w : Fin (2 ^ k) → Fin (2 ^ k))
    (hempty : ∀ c : Bag k, 1 ≤ c.l → (t + c.l) % 2 ≠ 0 → pl.regs c = ∅)
    (hinv : Invariant fastParams (fun c ↦ capacity fastParams root t c.l) pl.regs w)
    (b : Bag k) (hb : 1 ≤ b.l) (hp : (t + b.l) % 2 ≠ 0) :
    (((subregs pl.collapse b).filter (fun i ↦ ¬ b.Native i w)).card : ℚ) ≤
      2 * fastParams.mu * fastParams.delta * fastParams.A /
        (1 - (2 * fastParams.delta * fastParams.A) ^ 2) * capacity fastParams root t b.l := by
  apply subtree_intrusion fastParams k root hr pl.collapse w t b
  · intro c hc hp
    rw [pl.collapse_regs_of_pos c (hb.trans hc)]
    exact hempty c (hb.trans hc) hp
  · exact pl.collapse_invariant _ (fun c ↦ capacity_nonneg _ hr _ _) w hinv
  · exact hp

/-- Away from the root the explicit storage routing is exactly the register
flow used by the already checked interior invariant proof. -/
theorem route_regs_of_pos {k : ℕ} (pl : StoredPlacement k) (f : Bag k → ℕ)
    (feed : Finset (Fin (2 ^ k)))
    (hleaf : ∀ b : Bag k, ¬ b.l < k → (pl.regs b).card / 2 ≤ f b)
    (b : Bag k) (hb : 1 ≤ b.l) :
    (pl.route f feed).regs b = stageRegs (fun c ↦ split (pl.regs c) (f c)) b := by
  ext i
  constructor
  · intro hi
    have hdest := (pl.route f feed).mem_regs b i |>.mp hi
    cases ho : pl.owner i with
    | none =>
      have hroute := pl.route_from_cold f feed ((pl.mem_cold i).mpr ho)
      rw [hroute] at hdest
      split_ifs at hdest with hfeed
      · have h := congrArg Bag.l (Option.some.inj hdest)
        change 0 = b.l at h
        omega
    | some c =>
      have hc := (pl.mem_regs c i).mpr ho
      rcases split_covers (pl.regs c) (f c) hc with hp | hl | hr
      · rw [pl.route_to_parent f feed c hp] at hdest
        by_cases hcl : c.l = 0
        · simp only [hcl, ite_true] at hdest
          contradiction
        · rw [if_neg hcl] at hdest
          have heq := Option.some.inj hdest
          have hk : c.parent.l < k := by have := c.hl; simp [Bag.parent]; omega
          rw [← heq]
          simp only [stageRegs, dif_pos hk, mem_union]
          left
          by_cases he : c.x % 2 = 0
          · rw [Bag.parent_left_eq c (by omega) he hk]
            exact Or.inl hp
          · rw [Bag.parent_right_eq c (by omega) he hk]
            exact Or.inr hp
      · by_cases hk : c.l < k
        · rw [pl.route_to_left f feed c hk hl] at hdest
          have heq := Option.some.inj hdest
          rw [← heq]
          simp only [stageRegs, mem_union]
          right
          rw [if_neg (show (c.left hk).l ≠ 0 by change c.l + 1 ≠ 0; omega),
            if_pos (Bag.left_x_mod c hk), Bag.left_parent_eq]
          exact hl
        · have hempty := (split_leaf _ _ (hleaf c hk)).1
          simp only [hempty, notMem_empty] at hl
      · by_cases hk : c.l < k
        · rw [pl.route_to_right f feed c hk hr] at hdest
          have heq := Option.some.inj hdest
          rw [← heq]
          simp only [stageRegs, mem_union]
          right
          rw [if_neg (show (c.right hk).l ≠ 0 by change c.l + 1 ≠ 0; omega),
            if_neg (Bag.right_x_mod c hk), Bag.right_parent_eq]
          exact hr
        · have hempty := (split_leaf _ _ (hleaf c hk)).2
          simp only [hempty, notMem_empty] at hr
  · intro hi
    simp only [stageRegs, mem_union] at hi
    rcases hi with hchildren | hparent
    · by_cases hk : b.l < k
      · rw [dif_pos hk] at hchildren
        apply (pl.route f feed).mem_regs b i |>.mpr
        rcases mem_union.mp hchildren with hl | hr
        · rw [pl.route_to_parent f feed (b.left hk) hl,
            if_neg (show (b.left hk).l ≠ 0 by change b.l + 1 ≠ 0; omega),
            Bag.left_parent_eq]
        · rw [pl.route_to_parent f feed (b.right hk) hr,
            if_neg (show (b.right hk).l ≠ 0 by change b.l + 1 ≠ 0; omega),
            Bag.right_parent_eq]
      · simp only [dif_neg hk, notMem_empty] at hchildren
    · rw [if_neg (show b.l ≠ 0 by omega)] at hparent
      have hk : b.parent.l < k := by have := b.hl; simp [Bag.parent]; omega
      apply (pl.route f feed).mem_regs b i |>.mpr
      by_cases he : b.x % 2 = 0
      · rw [if_pos he] at hparent
        rw [pl.route_to_left f feed b.parent hk hparent,
          Bag.parent_left_eq b hb he hk]
      · rw [if_neg he] at hparent
        rw [pl.route_to_right f feed b.parent hk hparent,
          Bag.parent_right_eq b hb he hk]

/-- At the root, storage replaces the missing parent. Root fringes go into
storage rather than being retained in the root bag. -/
theorem route_root_regs {k : ℕ} (pl : StoredPlacement k) (f : Bag k → ℕ)
    (feed : Finset (Fin (2 ^ k))) (hfeed : feed ⊆ pl.cold)
    (hleaf : ∀ b : Bag k, ¬ b.l < k → (pl.regs b).card / 2 ≤ f b) :
    (pl.route f feed).regs (Bag.root k) = feed ∪
      (if h : 0 < k then
        (split (pl.regs ((Bag.root k).left h)) (f ((Bag.root k).left h))).toParent ∪
        (split (pl.regs ((Bag.root k).right h)) (f ((Bag.root k).right h))).toParent
      else ∅) := by
  ext i
  constructor
  · intro hi
    have hdest := (pl.route f feed).mem_regs (Bag.root k) i |>.mp hi
    cases ho : pl.owner i with
    | none =>
      have hroute := pl.route_from_cold f feed ((pl.mem_cold i).mpr ho)
      rw [hroute] at hdest
      by_cases hf : i ∈ feed
      · exact mem_union_left _ hf
      · simp only [hf, ite_false] at hdest
        contradiction
    | some c =>
      have hc := (pl.mem_regs c i).mpr ho
      rcases split_covers (pl.regs c) (f c) hc with hp | hl | hr
      · rw [pl.route_to_parent f feed c hp] at hdest
        by_cases hcl : c.l = 0
        · simp only [hcl, ite_true] at hdest
          contradiction
        · rw [if_neg hcl] at hdest
          have heq := Option.some.inj hdest
          have hlevel := congrArg Bag.l heq
          have hk : 0 < k := by have := c.hl; simp [Bag.parent, Bag.root] at hlevel; omega
          have hcp : c.parent.l < k := by rw [heq]; exact hk
          apply mem_union_right
          rw [dif_pos hk]
          by_cases he : c.x % 2 = 0
          · have hchild := Bag.parent_left_eq c (by omega) he hcp
            have hchild' : (Bag.root k).left hk = c := by simpa only [heq] using hchild
            exact mem_union_left _ (hchild'.symm ▸ hp)
          · have hchild := Bag.parent_right_eq c (by omega) he hcp
            have hchild' : (Bag.root k).right hk = c := by simpa only [heq] using hchild
            exact mem_union_right _ (hchild'.symm ▸ hp)
      · by_cases hk : c.l < k
        · rw [pl.route_to_left f feed c hk hl] at hdest
          have h := congrArg Bag.l (Option.some.inj hdest)
          change c.l + 1 = 0 at h
          omega
        · have hempty := (split_leaf _ _ (hleaf c hk)).1
          simp only [hempty, notMem_empty] at hl
      · by_cases hk : c.l < k
        · rw [pl.route_to_right f feed c hk hr] at hdest
          have h := congrArg Bag.l (Option.some.inj hdest)
          change c.l + 1 = 0 at h
          omega
        · have hempty := (split_leaf _ _ (hleaf c hk)).2
          simp only [hempty, notMem_empty] at hr
  · intro hi
    apply (pl.route f feed).mem_regs (Bag.root k) i |>.mpr
    rcases mem_union.mp hi with hf | hc
    · rw [pl.route_from_cold f feed (hfeed hf), if_pos hf]
    · by_cases hk : 0 < k
      · rw [dif_pos hk] at hc
        rcases mem_union.mp hc with hl | hr
        · rw [pl.route_to_parent f feed ((Bag.root k).left hk) hl,
            if_neg (show ((Bag.root k).left hk).l ≠ 0 by change 1 ≠ 0; omega), Bag.left_parent_eq]
        · rw [pl.route_to_parent f feed ((Bag.root k).right hk) hr,
            if_neg (show ((Bag.root k).right hk).l ≠ 0 by change 1 ≠ 0; omega), Bag.right_parent_eq]
      · simp only [dif_neg hk, notMem_empty] at hc

end Paterson.Bags.StoredPlacement
