module

public import AKS.Paterson.StoredBalance
public import AKS.Paterson.AllocatedSubtree

/-! # Native cohorts and threshold decomposition for actual rank inputs -/

@[expose] public section

namespace Paterson.Bags

open Finset

theorem native_cohort_card {k : ℕ} (b : Bag k)
    (w : Fin (2 ^ k) → Fin (2 ^ k)) (hw : Function.Injective w) :
    (univ.filter (fun i ↦ b.Native i w)).card = b.size := by
  have hh : (univ.filter (fun i ↦ (w i).val < b.hi)).card = b.hi := by
    rw [bijection_count_val_lt w hw, card_filter_val_lt _ _ (bag_hi_le b)]
  have hl : (univ.filter (fun i ↦ (w i).val < b.lo)).card = b.lo := by
    rw [bijection_count_val_lt w hw,
      card_filter_val_lt _ _ (b.lo_lt_hi.le.trans (bag_hi_le b))]
  have hpart : univ.filter (fun i ↦ (w i).val < b.hi) =
      univ.filter (fun i ↦ (w i).val < b.lo) ∪ univ.filter (fun i ↦ b.Native i w) := by
    ext i
    simp only [mem_filter, mem_univ, true_and, mem_union, Bag.native_iff]
    have := b.lo_lt_hi
    omega
  have hd : Disjoint (univ.filter (fun i ↦ (w i).val < b.lo))
      (univ.filter (fun i ↦ b.Native i w)) := by
    rw [disjoint_filter]
    intro i _ hi hn
    rw [Bag.native_iff] at hn
    omega
  rw [hpart, card_union_of_disjoint hd, hl] at hh
  have hwidth : b.hi = b.lo + b.size := by
    simp only [Bag.hi, Bag.lo, Nat.add_mul, Nat.one_mul]
  omega

theorem size_eq_nativeWidth {k : ℕ} (b : Bag k) : (b.size : ℚ) = nativeWidth k b.l := by
  rw [Bag.size, bagSize, Nat.cast_div_charZero (Nat.pow_dvd_pow 2 b.hl)]
  simp [nativeWidth]

def WrongSide {k : ℕ} (b : Bag k) (w : Fin (2 ^ k) → Fin (2 ^ k)) (i : Fin (2 ^ k)) : Prop :=
  if b.x % 2 = 0 then b.hi ≤ (w i).val else (w i).val < b.lo

instance {k : ℕ} (b : Bag k) (w : Fin (2 ^ k) → Fin (2 ^ k)) :
    DecidablePred (WrongSide b w) := fun i ↦ inferInstanceAs
      (Decidable (if b.x % 2 = 0 then b.hi ≤ (w i).val else (w i).val < b.lo))

theorem wrongSide_cover {k : ℕ} (b : Bag k) (hb : 1 ≤ b.l)
    (w : Fin (2 ^ k) → Fin (2 ^ k)) (i : Fin (2 ^ k)) (hi : WrongSide b w i) :
    (b.sibling hb).Native i w ∨ b.parent.Strange 1 i w := by
  have ha : b.ancestor 0 = b := by apply Bag.ext <;> simp [Bag.ancestor]
  have hs : b.Strange 1 i w := by
    simp only [Bag.Strange, Nat.reduceEqDiff, false_or, Nat.sub_self, ha]
    rw [Bag.native_iff]
    unfold WrongSide at hi
    split_ifs at hi <;> omega
  rcases (b.one_strange_decomp hb i w).mp hs with hp | hn
  · exact Or.inr hp
  · exact Or.inl hn.2

end Paterson.Bags
