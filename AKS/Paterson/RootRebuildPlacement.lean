module

public import AKS.Paterson.RootPrefixCoordinates

/-! # Positional ownership for rebuilding the upper four levels

The original deep bags retain their registers. Each of the sixteen sorted
upper bins reserves a level-four segment and one quarter of a level-two bag.
All remaining upper registers become cold storage. The construction uses no
input ranks. Allocation and rank preservation are proved separately.
-/

@[expose] public section

namespace Paterson.Bags

open Finset

def registerOrdinal {k : ℕ} (U : Finset (Fin (2 ^ k))) (i : Fin (2 ^ k)) : ℕ :=
  (U.filter (fun j ↦ j < i)).card

theorem registerOrdinal_enum {k : ℕ} (U : Finset (Fin (2 ^ k))) (i : Fin U.card) :
    registerOrdinal U (U.orderEmbOfFin rfl i) = i.val := by
  unfold registerOrdinal
  rw [filter_regs_card]
  have hfilter : univ.filter (fun j ↦ U.orderEmbOfFin rfl j < U.orderEmbOfFin rfl i) =
      univ.filter (fun j : Fin U.card ↦ j.val < i.val) := by
    ext j
    simp only [mem_filter, mem_univ, true_and, OrderEmbedding.lt_iff_lt]
    rfl
  rw [hfilter, card_filter_val_lt _ _ i.isLt.le]

theorem registerOrdinal_lt {k : ℕ} (U : Finset (Fin (2 ^ k)))
    {i : Fin (2 ^ k)} (hi : i ∈ U) : registerOrdinal U i < U.card := by
  have hi' : i ∈ Set.range (U.orderEmbOfFin rfl) := by
    rw [range_orderEmbOfFin]; exact hi
  obtain ⟨j, rfl⟩ := hi'
  rw [registerOrdinal_enum]
  exact j.isLt

def rebuildUpper {k : ℕ} (pl : StoredPlacement k) (hk : 5 ≤ k)
    (n2 n4 : ℕ) : StoredPlacement k where
  owner i :=
    if i ∈ upperRegisters pl hk then
      let a := registerOrdinal (upperRegisters pl hk) i
      let width := (upperRegisters pl hk).card / 16
      let x := a / width
      if hx : x < 16 then
        if a % width < n4 then
          some ⟨4, x, by omega, by simpa using hx⟩
        else if a % width < n4 + n2 / 4 then
          some ⟨2, x / 4, by omega, by change x / 4 < 4; omega⟩
        else none
      else none
    else pl.owner i

theorem rebuildUpper_owner_outside {k : ℕ} (pl : StoredPlacement k) (hk : 5 ≤ k)
    (n2 n4 : ℕ) {i : Fin (2 ^ k)} (hi : i ∉ upperRegisters pl hk) :
    (rebuildUpper pl hk n2 n4).owner i = pl.owner i := by
  simp only [rebuildUpper, if_neg hi]

theorem rebuildUpper_owner_inside {k : ℕ} (pl : StoredPlacement k) (hk : 5 ≤ k)
    (n2 n4 : ℕ) {i : Fin (2 ^ k)} (hi : i ∈ upperRegisters pl hk) :
    (rebuildUpper pl hk n2 n4).owner i = none ∨
      ∃ b, (rebuildUpper pl hk n2 n4).owner i = some b ∧ (b.l = 2 ∨ b.l = 4) := by
  simp only [rebuildUpper, if_pos hi]
  split_ifs <;> simp

theorem rebuildUpper_deep_regs {root : ℚ} {k t : ℕ} (hk : 6 ≤ k)
    (pl : StoredPlacement k) (ha : AllocationInvariant root t pl) (hp : t % 2 = 0)
    (n2 n4 : ℕ) (b : Bag k) (hb : 6 ≤ b.l) :
    (rebuildUpper pl (by omega) n2 n4).regs b = pl.regs b := by
  ext i
  by_cases hi : i ∈ upperRegisters pl (by omega)
  · have hnew : i ∉ (rebuildUpper pl (by omega) n2 n4).regs b := by
      intro hn
      have ho := (StoredPlacement.mem_regs _ b i).mp hn
      rcases rebuildUpper_owner_inside pl (by omega) n2 n4 hi with he | ⟨c, he, hc⟩
      · rw [he] at ho; cases ho
      · have hcb := Option.some.inj (he.symm.trans ho)
        subst c
        omega
    have hold : i ∉ pl.regs b := by
      intro ho
      exact disjoint_left.mp (deepRegisters_disjoint_upper hk pl ha hp)
        (mem_deepRegisters_of_owner pl hk b hb ho) hi
    simp only [hnew, hold]
  · simp only [StoredPlacement.mem_regs,
      rebuildUpper_owner_outside pl (by omega) n2 n4 hi]

end Paterson.Bags
