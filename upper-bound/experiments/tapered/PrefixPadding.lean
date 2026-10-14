import AKS.Sort.Shrink
import AKS.Sort.Monotone
import Mathlib.Tactic

namespace Tapered945

/-- Natural-key execution under identity suffix padding. Unlike the Boolean
restriction lemma, this preserves each live rank exactly. -/
theorem restrictWires_exec_nat_foldl {n m : Nat} (hm : m ≤ n)
    (cs : List (Comparator n)) (wn : Fin n → Nat) (wm : Fin m → Nat)
    (hlo : ∀ i : Fin m, wn ⟨i.val, by omega⟩ = wm i)
    (hsmall : ∀ i, wm i < m)
    (hhi : ∀ i : Fin n, m ≤ i.val → wn i = i.val) :
    (∀ i : Fin m, cs.foldl (fun acc c => c.apply acc) wn ⟨i.val, by omega⟩ =
      (cs.filterMap (restrictFilter m)).foldl (fun acc c => c.apply acc) wm i) ∧
    (∀ i : Fin m,
      (cs.filterMap (restrictFilter m)).foldl (fun acc c => c.apply acc) wm i < m) ∧
    (∀ i : Fin n, m ≤ i.val → cs.foldl (fun acc c => c.apply acc) wn i = i.val) := by
  induction cs generalizing wn wm with
  | nil => exact ⟨hlo, hsmall, hhi⟩
  | cons c cs ih =>
    have hc := c.h
    rw [Fin.lt_def] at hc
    simp only [List.foldl_cons, List.filterMap_cons]
    by_cases hi : c.i.val < m <;> by_cases hj : c.j.val < m
    · simp only [restrictFilter, hi, hj, dite_true, List.foldl_cons]
      have h1 : wn c.i = wm ⟨c.i.val, hi⟩ := hlo ⟨c.i.val, hi⟩
      have h2 : wn c.j = wm ⟨c.j.val, hj⟩ := hlo ⟨c.j.val, hj⟩
      refine ih _ _ (fun k => ?_) (fun k => ?_) (fun k hk => ?_)
      · have := hlo k
        simp only [Comparator.apply, Fin.ext_iff, h1, h2]
        split_ifs <;> simp_all
      · have hki := hsmall ⟨c.i.val, hi⟩
        have hkj := hsmall ⟨c.j.val, hj⟩
        have hk := hsmall k
        simp only [Comparator.apply, Fin.ext_iff]
        split_ifs <;> omega
      · have := hhi k hk
        simp only [Comparator.apply, Fin.ext_iff]
        split_ifs <;> first | assumption | omega
    · simp only [restrictFilter, hi, hj, dite_true, dite_false]
      have h2 := hhi c.j (by omega)
      have h1 : wn c.i = wm ⟨c.i.val, hi⟩ := hlo ⟨c.i.val, hi⟩
      have hlt : wn c.i < wn c.j := by rw [h1, h2]; have := hsmall ⟨c.i.val, hi⟩; omega
      refine ih _ _ (fun k => ?_) hsmall (fun k hk => ?_)
      · have := hlo k
        have := k.isLt
        simp only [Comparator.apply, Fin.ext_iff, min_eq_left hlt.le, max_eq_right hlt.le]
        split_ifs <;> simp_all
      · have := hhi k hk
        simp only [Comparator.apply, Fin.ext_iff, min_eq_left hlt.le, max_eq_right hlt.le]
        split_ifs <;> simp_all
    · omega
    · simp only [restrictFilter, hi, dite_false]
      have h1 := hhi c.i (by omega)
      have h2 := hhi c.j (by omega)
      have hlt : wn c.i ≤ wn c.j := by rw [h1, h2]; omega
      refine ih _ _ (fun k => ?_) hsmall (fun k hk => ?_)
      · have := hlo k
        have := k.isLt
        simp only [Comparator.apply, Fin.ext_iff, min_eq_left hlt, max_eq_right hlt]
        split_ifs <;> simp_all
      · have := hhi k hk
        simp only [Comparator.apply, Fin.ext_iff, min_eq_left hlt, max_eq_right hlt]
        split_ifs <;> simp_all

/-- Extend live ranks by larger identity dummy ranks on the suffix. -/
def padNatRanks {m n : Nat} (v : Fin m → Nat) : Fin n → Nat :=
  fun i => if hi : i.val < m then v ⟨i.val, hi⟩ else i.val

theorem restrictWires_exec_padNatRanks {n m : Nat} (hm : m ≤ n)
    (net : ComparatorNetwork n) (v : Fin m → Nat) (hv : ∀ i, v i < m) :
    (∀ i : Fin m, net.exec (padNatRanks v) ⟨i.val, by omega⟩ =
      (net.restrictWires m hm).exec v i) ∧
    (∀ i : Fin m, (net.restrictWires m hm).exec v i < m) ∧
    (∀ i : Fin n, m ≤ i.val → net.exec (padNatRanks v) i = i.val) := by
  exact restrictWires_exec_nat_foldl hm net.comparators (padNatRanks v) v
    (fun i => by simp [padNatRanks, i.isLt]) hv
    (fun i hi => by simp [padNatRanks, show ¬ i.val < m by omega])

def padFinRanks {m n : Nat} (hm : m ≤ n) (p : Equiv.Perm (Fin m)) : Fin n → Fin n :=
  fun i => if hi : i.val < m then
    ⟨(p ⟨i.val, hi⟩).val, (p ⟨i.val, hi⟩).isLt.trans_le hm⟩ else i

theorem padFinRanks_bijective {m n : Nat} (hm : m ≤ n) (p : Equiv.Perm (Fin m)) :
    Function.Bijective (padFinRanks hm p) := by
  constructor
  · intro i j heq
    have heqv := congrArg Fin.val heq
    by_cases hi : i.val < m <;> by_cases hj : j.val < m
    · simp only [padFinRanks, dif_pos hi, dif_pos hj] at heqv
      have hp : (⟨i.val, hi⟩ : Fin m) = ⟨j.val, hj⟩ :=
        p.injective (Fin.ext heqv)
      exact Fin.ext (congrArg (Fin.val : Fin m → Nat) hp)
    · simp only [padFinRanks, dif_pos hi, dif_neg hj] at heqv
      have := (p ⟨i.val, hi⟩).isLt
      omega
    · simp only [padFinRanks, dif_neg hi, dif_pos hj] at heqv
      have := (p ⟨j.val, hj⟩).isLt
      omega
    · simpa only [padFinRanks, dif_neg hi, dif_neg hj] using heq
  · intro y
    by_cases hy : y.val < m
    · let x := p.symm ⟨y.val, hy⟩
      have hx : x.val < m := x.isLt
      refine ⟨⟨x.val, hx.trans_le hm⟩, ?_⟩
      apply Fin.ext
      simp only [padFinRanks, dif_pos hx]
      exact congrArg Fin.val (p.apply_symm_apply ⟨y.val, hy⟩)
    · exact ⟨y, by simp [padFinRanks, hy]⟩

/-- A genuine padded permutation, so semantic separator results stated for
permutation inputs can be instantiated without a new premise. -/
noncomputable def padRankPerm {m n : Nat} (hm : m ≤ n) (p : Equiv.Perm (Fin m)) :
    Equiv.Perm (Fin n) := Equiv.ofBijective (padFinRanks hm p) (padFinRanks_bijective hm p)

theorem padRankPerm_val {m n : Nat} (hm : m ≤ n) (p : Equiv.Perm (Fin m)) :
    (fun i => (padRankPerm hm p i).val) = padNatRanks (fun i => (p i).val) := by
  funext i
  simp only [padRankPerm, Equiv.ofBijective_apply, padFinRanks, padNatRanks]
  split <;> rfl

/-- Transfer actual rank-valued execution from a padded rectangle to its
restricted live wires. Dummy output positions retain their identity ranks. -/
theorem restrictWires_exec_padRankPerm {n m : Nat} (hm : m ≤ n)
    (net : ComparatorNetwork n) (p : Equiv.Perm (Fin m)) :
    (∀ i : Fin m, (net.exec (padRankPerm hm p) ⟨i.val, by omega⟩).val =
      ((net.restrictWires m hm).exec p i).val) ∧
    (∀ i : Fin n, m ≤ i.val → (net.exec (padRankPerm hm p) i).val = i.val) := by
  have hn := net.exec_comp_monotone
    (show Monotone (Fin.val : Fin n → Nat) from fun _ _ h => h) (padRankPerm hm p)
  have hmexec := (net.restrictWires m hm).exec_comp_monotone
    (show Monotone (Fin.val : Fin m → Nat) from fun _ _ h => h) p
  have hpad := restrictWires_exec_padNatRanks hm net (fun i => (p i).val)
    (fun i => (p i).isLt)
  constructor
  · intro i
    have hl := congrFun hn ⟨i.val, by omega⟩
    have hr := congrFun hmexec i
    dsimp only [Function.comp_def] at hl hr
    rw [padRankPerm_val] at hl
    exact hl.trans ((hpad.1 i).trans hr.symm)
  · intro i hi
    have h := congrFun hn i
    dsimp only [Function.comp_def] at h
    rw [padRankPerm_val] at h
    exact h.trans (hpad.2.2 i hi)

/-- Any rank-event predicate that excludes identity dummy ranks has exactly
the same count before and after padding/restriction. Boundary crossing
predicates at live cuts are direct instances. -/
theorem padding_rank_event_card {n m : Nat} (hm : m ≤ n)
    (net : ComparatorNetwork n) (p : Equiv.Perm (Fin m))
    (event : Nat → Nat → Prop) [DecidableRel event]
    (hdummy : ∀ i, m ≤ i → ¬ event i i) :
    (Finset.univ.filter fun i : Fin n =>
      event i.val (net.exec (padRankPerm hm p) i).val).card =
    (Finset.univ.filter fun i : Fin m =>
      event i.val ((net.restrictWires m hm).exec p i).val).card := by
  have h := restrictWires_exec_padRankPerm hm net p
  symm
  apply Finset.card_bij (fun i _ => (⟨i.val, i.isLt.trans_le hm⟩ : Fin n))
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    rw [h.1 i]
    exact hi
  · intro i _ j _ hij
    exact Fin.ext (congrArg (Fin.val : Fin n → Nat) hij)
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
    have hilive : i.val < m := by
      by_contra hn
      have him : m ≤ i.val := by omega
      rw [h.2 i him] at hi
      exact hdummy i.val him hi
    refine ⟨⟨i.val, hilive⟩, ?_, rfl⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [← h.1 ⟨i.val, hilive⟩]
    exact hi

theorem padding_boundary_high_card {n m : Nat} (hm : m ≤ n)
    (net : ComparatorNetwork n) (p : Equiv.Perm (Fin m)) (cut : Nat) :
    (Finset.univ.filter fun i : Fin n =>
      cut ≤ (net.exec (padRankPerm hm p) i).val ∧ i.val < cut).card =
    (Finset.univ.filter fun i : Fin m =>
      cut ≤ ((net.restrictWires m hm).exec p i).val ∧ i.val < cut).card := by
  exact padding_rank_event_card hm net p (fun wire rank => cut ≤ rank ∧ wire < cut)
    (by intro i hi; omega)

theorem padding_boundary_low_card {n m : Nat} (hm : m ≤ n)
    (net : ComparatorNetwork n) (p : Equiv.Perm (Fin m)) (cut : Nat) :
    (Finset.univ.filter fun i : Fin n =>
      (net.exec (padRankPerm hm p) i).val < cut ∧ cut ≤ i.val).card =
    (Finset.univ.filter fun i : Fin m =>
      ((net.restrictWires m hm).exec p i).val < cut ∧ cut ≤ i.val).card := by
  exact padding_rank_event_card hm net p (fun wire rank => rank < cut ∧ cut ≤ wire)
    (by intro i hi; omega)

end Tapered945
