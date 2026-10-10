module

public import AKS.Kahale.RelativeOrderCode
public import AKS.Kahale.FiniteEntropy
public import Mathlib.Data.List.Basic

/-! # Insertion codes preserve the joint rank-set/rank fibers

The ordinal has a fixed codomain `ℕ`, allowing entropy comparisons between
different rank sets. Distinctness of the inserted rank is explicit.
-/

@[expose] public section

namespace Kahale

def insertionOrdinal {α : Type*} [LinearOrder α] (rest : Finset α) (a : α) : ℕ :=
  (insert a rest).sort.idxOf a

theorem insertion_pair_eq_iff {α : Type*} [LinearOrder α]
    (rest other : Finset α) (a b : α) (ha : a ∉ rest) (hb : b ∉ other) :
    (insert a rest, insertionOrdinal rest a) = (insert b other, insertionOrdinal other b) ↔
      (rest, a) = (other, b) := by
  constructor
  · intro h
    have hs : insert a rest = insert b other := congrArg Prod.fst h
    have hi : insertionOrdinal rest a = insertionOrdinal other b := congrArg Prod.snd h
    unfold insertionOrdinal at hi
    rw [hs] at hi
    have hm : a ∈ (insert b other).sort := by
      have ha' : a ∈ insert b other := hs ▸ Finset.mem_insert_self a rest
      simpa using ha'
    have hab : a = b := (List.idxOf_inj hm).mp hi
    subst b
    have he := congrArg (fun s : Finset α ↦ s.erase a) hs
    have hr : rest = other := by simpa [ha, hb] using he
    exact Prod.ext hr rfl
  · intro h
    have hr : rest = other := congrArg Prod.fst h
    have hab : a = b := congrArg Prod.snd h
    rw [hr, hab]

theorem entropy_insertion_eq_rankSet_rank {Ω α : Type*} [LinearOrder α]
    (source : Finset Ω) (rest : Ω → Finset α) (rank : Ω → α)
    (outside : ∀ x ∈ source, rank x ∉ rest x) :
    finiteEntropy source (fun x ↦ (insert (rank x) (rest x), insertionOrdinal (rest x) (rank x))) =
      finiteEntropy source (fun x ↦ (rest x, rank x)) := by
  apply finiteEntropy_eq_of_sameFibers
  intro x hx y hy
  exact insertion_pair_eq_iff (rest y) (rest x) (rank y) (rank x) (outside y hy) (outside x hx)

end Kahale
