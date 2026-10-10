module

public import AKS.Paterson.DescendantRegisters

/-! # Uniform assigned prefix counts in the retained deep subtrees -/

@[expose] public section

namespace Paterson.Bags

open Finset BigOperators

def assignedPrefix {k : ℕ} (pl : StoredPlacement k) (L q : ℕ) (i : Fin (2 ^ k)) : Prop :=
  match pl.owner i with
  | none => False
  | some b => (b.ancestor (b.l - L)).x < q

instance {k : ℕ} (pl : StoredPlacement k) (L q : ℕ) : DecidablePred (assignedPrefix pl L q) :=
  fun i ↦ by unfold assignedPrefix; split <;> infer_instance

def deepPrefixRegisters {k : ℕ} (pl : StoredPlacement k) (hk : 6 ≤ k)
    (cutoff : ℕ) : Finset (Fin (2 ^ k)) :=
  (univ.filter (fun x : Fin 64 ↦ x.val < cutoff)).biUnion
    fun x ↦ subregs pl.collapse ⟨6, x.val, hk, by simpa using x.isLt⟩

theorem assignedPrefix_on_subtree {k L : ℕ} (pl : StoredPlacement k) (hk : 6 ≤ k)
    (hL : L ≤ 6) (q : ℕ) (x : Fin 64) {i : Fin (2 ^ k)}
    (hi : i ∈ subregs pl.collapse (⟨6, x.val, hk, by simpa using x.isLt⟩ : Bag k)) :
    assignedPrefix pl L q i ↔ x.val < q * 2 ^ (6 - L) := by
  obtain ⟨c, hc, hdesc, hmem⟩ := mem_subregs_exists_bag' pl.collapse
    (⟨6, x.val, hk, by simpa using x.isLt⟩ : Bag k) hi
  have hcl : 6 ≤ c.l := hc
  rw [pl.collapse_regs_of_pos c (by omega)] at hmem
  have ho := (pl.mem_regs c i).mp hmem
  simp only [assignedPrefix, ho]
  change c.x / 2 ^ (c.l - L) < q ↔ x.val < q * 2 ^ (6 - L)
  change c.x / 2 ^ (c.l - 6) = x.val at hdesc
  rw [show c.l - L = (c.l - 6) + (6 - L) by omega, pow_add,
    ← Nat.div_div_eq_div_mul, hdesc]
  exact Nat.div_lt_iff_lt_mul (by positivity)

theorem deep_filter_assignedPrefix {k L : ℕ} (pl : StoredPlacement k) (hk : 6 ≤ k)
    (hL : L ≤ 6) (q : ℕ) :
    (deepRegisters pl hk).filter (assignedPrefix pl L q) =
      deepPrefixRegisters pl hk (q * 2 ^ (6 - L)) := by
  ext i
  constructor
  · intro hi
    obtain ⟨hiD, hiQ⟩ := mem_filter.mp hi
    obtain ⟨x, _, hx⟩ := mem_biUnion.mp hiD
    exact mem_biUnion.mpr ⟨x, mem_filter.mpr ⟨mem_univ _,
      (assignedPrefix_on_subtree pl hk hL q x hx).mp hiQ⟩, hx⟩
  · intro hi
    obtain ⟨x, hx, hiD⟩ := mem_biUnion.mp hi
    exact mem_filter.mpr ⟨mem_biUnion.mpr ⟨x, mem_univ _, hiD⟩,
      (assignedPrefix_on_subtree pl hk hL q x hiD).mpr (mem_filter.mp hx).2⟩

theorem deepPrefixRegisters_card {root : ℚ} (hr : 0 ≤ root) {k t : ℕ} (hk : 6 ≤ k)
    (hc : fastParams.minCapacity ≤ capacity fastParams root t 0)
    (pl : StoredPlacement k) (ha : AllocationInvariant root t pl) (hp : t % 2 = 0)
    (cutoff : ℕ) (hcut : cutoff ≤ 64) :
    (deepPrefixRegisters pl hk cutoff).card = cutoff * subtreeTotal root k t 6 := by
  unfold deepPrefixRegisters
  rw [card_biUnion]
  · have hp6 : (t + 6) % 2 = 0 := by omega
    have hs (x : Fin 64) :
        (subregs pl.collapse (⟨6, x.val, hk, by simpa using x.isLt⟩ : Bag k)).card =
          subtreeTotal root k t 6 := by
      have h := allocated_subtree_card hr hc pl ha
        (⟨6, x.val, hk, by simpa using x.isLt⟩ : Bag k) (by change 1 ≤ 6; omega)
      simpa only [subtreeContent, if_pos hp6] using h
    simp only [hs, sum_const, Nat.nsmul_eq_mul, card_filter_val_lt _ _ hcut]
  · intro x _ y _ hxy
    apply subregs_disjoint' pl.collapse
    · intro heq
      exact hxy (Fin.ext (congrArg Bag.x heq))
    · rfl

theorem coarse_cutoff_le64 {L q : ℕ} (hL : L ≤ 6) (hq : q ≤ 2 ^ L) :
    q * 2 ^ (6 - L) ≤ 64 := by
  calc q * 2 ^ (6 - L) ≤ 2 ^ L * 2 ^ (6 - L) := Nat.mul_le_mul_right _ hq
    _ = 64 := by rw [← pow_add, Nat.add_sub_of_le hL]; norm_num

theorem assigned_deep_prefix_card {root : ℚ} (hr : 0 ≤ root) {k t L : ℕ} (hk : 6 ≤ k)
    (hc : fastParams.minCapacity ≤ capacity fastParams root t 0)
    (pl : StoredPlacement k) (ha : AllocationInvariant root t pl) (hp : t % 2 = 0)
    (hL : L ≤ 6) (q : ℕ) (hq : q ≤ 2 ^ L) :
    ((deepRegisters pl hk).filter (assignedPrefix pl L q)).card =
      (q * 2 ^ (6 - L)) * subtreeTotal root k t 6 := by
  rw [deep_filter_assignedPrefix pl hk hL q]
  exact deepPrefixRegisters_card hr hk hc pl ha hp _ (coarse_cutoff_le64 hL hq)

end Paterson.Bags
