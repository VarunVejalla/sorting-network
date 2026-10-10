module

public import AKS.Sort.Depth

/-! # Reordering time-labelled comparators without changing execution

Comparators whose chronological order disagrees with their assigned times
must be disjoint. This permits gathering equal times into parallel layers.
-/

@[expose] public section

namespace Kahale

theorem comparator_commutes {n : ℕ} {α : Type*} [LinearOrder α]
    (c d : Comparator n) (hn : ¬c.overlaps d) (v : Fin n → α) :
    c.apply (d.apply v) = d.apply (c.apply v) := by
  unfold Comparator.overlaps at hn
  push_neg at hn
  obtain ⟨h₁, h₂, h₃, h₄⟩ := hn
  have hci : c.j ≠ c.i := ne_of_gt c.h
  have hdi : d.j ≠ d.i := ne_of_gt d.h
  funext i
  by_cases hi : i = c.i
  · subst i
    simp [Comparator.apply, h₁, h₂, h₃, h₄, hci, hdi,
      h₁.symm, h₂.symm, h₃.symm, h₄.symm]
  · by_cases hj : i = c.j
    · subst i
      simp [Comparator.apply, h₁, h₂, h₃, h₄, hci, hdi,
        h₁.symm, h₂.symm, h₃.symm, h₄.symm]
    · by_cases hd : i = d.i
      · subst i
        simp [Comparator.apply, h₁, h₂, h₃, h₄, hci, hdi,
          h₁.symm, h₂.symm, h₃.symm, h₄.symm]
      · by_cases he : i = d.j
        · subst i
          simp [Comparator.apply, h₁, h₂, h₃, h₄, hci, hdi,
            h₁.symm, h₂.symm, h₃.symm, h₄.symm]
        · simp [Comparator.apply, hi, hj, hd, he]

theorem comparator_commutes_list {n : ℕ} {α : Type*} [LinearOrder α]
    (c : Comparator n) (cs : List (Comparator n)) (hn : ∀ d ∈ cs, ¬c.overlaps d)
    (v : Fin n → α) :
    (ComparatorNetwork.mk cs).exec (c.apply v) = c.apply ((ComparatorNetwork.mk cs).exec v) := by
  induction cs generalizing v with
  | nil => rfl
  | cons d cs ih =>
    change (ComparatorNetwork.mk cs).exec (d.apply (c.apply v)) =
      c.apply ((ComparatorNetwork.mk cs).exec (d.apply v))
    rw [← comparator_commutes c d (hn d List.mem_cons_self)]
    exact ih (fun e he ↦ hn e (List.mem_cons_of_mem d he)) _

def DependencyOrdered {n : ℕ} (cs : List (Comparator n × ℕ)) : Prop :=
  cs.Pairwise (fun a b ↦ a.2 ≥ b.2 → ¬a.1.overlaps b.1)

theorem timed_exec_partition {n : ℕ} {α : Type*} [LinearOrder α]
    (cs : List (Comparator n × ℕ)) (hp : DependencyOrdered cs) (v : Fin n → α) :
    (ComparatorNetwork.mk (cs.map Prod.fst)).exec v =
      (ComparatorNetwork.mk ((cs.filter (fun a ↦ a.2 ≠ 0)).map Prod.fst)).exec
        ((ComparatorNetwork.mk ((cs.filter (fun a ↦ a.2 = 0)).map Prod.fst)).exec v) := by
  induction cs generalizing v with
  | nil => rfl
  | cons a cs ih =>
    obtain ⟨hh, ht⟩ := List.pairwise_cons.mp hp
    by_cases ha : a.2 = 0
    · simp only [List.filter_cons, decide_eq_true_eq, if_pos ha,
        if_neg (not_not.mpr ha), List.map_cons]
      exact ih ht (a.1.apply v)
    · have hc : ∀ c ∈ (cs.filter (fun a ↦ a.2 = 0)).map Prod.fst, ¬a.1.overlaps c := by
        intro c hc
        obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hc
        obtain ⟨hb, he⟩ := List.mem_filter.mp hb
        have hz : b.2 = 0 := of_decide_eq_true he
        exact hh b hb (by omega)
      simp only [List.filter_cons, decide_eq_true_eq, if_pos ha, if_neg ha, List.map_cons]
      change (ComparatorNetwork.mk (cs.map Prod.fst)).exec (a.1.apply v) =
        (ComparatorNetwork.mk ((cs.filter (fun a ↦ a.2 ≠ 0)).map Prod.fst)).exec
          (a.1.apply ((ComparatorNetwork.mk ((cs.filter (fun a ↦ a.2 = 0)).map Prod.fst)).exec v))
      rw [ih ht, comparator_commutes_list a.1 _ hc]

def timedLayers {n : ℕ} : ℕ → List (Comparator n × ℕ) → List (List (Comparator n))
  | 0, _ => []
  | d + 1, cs => ((cs.filter (fun a ↦ a.2 = 0)).map Prod.fst) ::
      timedLayers d ((cs.filter (fun a ↦ a.2 ≠ 0)).map (fun a ↦ (a.1, a.2 - 1)))

theorem timedLayers_length {n : ℕ} (d : ℕ) (cs : List (Comparator n × ℕ)) :
    (timedLayers d cs).length = d := by
  induction d generalizing cs <;> simp [timedLayers, *]

theorem dependencyOrdered_shift {n : ℕ} (cs : List (Comparator n × ℕ))
    (hp : DependencyOrdered cs) :
    DependencyOrdered ((cs.filter (fun a ↦ a.2 ≠ 0)).map (fun a ↦ (a.1, a.2 - 1))) := by
  rw [DependencyOrdered, List.pairwise_map]
  apply (hp.filter _).imp_of_mem
  intro a b ha hb hab hle
  have hza : a.2 ≠ 0 := of_decide_eq_true (List.mem_filter.mp ha).2
  have hzb : b.2 ≠ 0 := of_decide_eq_true (List.mem_filter.mp hb).2
  exact hab (by dsimp only at hle; omega)

theorem timedLayers_parallel {n : ℕ} (d : ℕ) (cs : List (Comparator n × ℕ))
    (hp : DependencyOrdered cs) : ∀ layer ∈ timedLayers d cs, IsParallelLayer layer := by
  induction d generalizing cs with
  | zero => simp [timedLayers]
  | succ d ih =>
    intro layer hl
    simp only [timedLayers, List.mem_cons] at hl
    rcases hl with rfl | hl
    · rw [IsParallelLayer, List.pairwise_map]
      apply (hp.filter _).imp_of_mem
      intro a b ha hb hab
      have hza : a.2 = 0 := of_decide_eq_true (List.mem_filter.mp ha).2
      have hzb : b.2 = 0 := of_decide_eq_true (List.mem_filter.mp hb).2
      exact hab (by omega)
    · exact ih _ (dependencyOrdered_shift cs hp) layer hl

theorem timedLayers_exec {n : ℕ} {α : Type*} [LinearOrder α]
    (d : ℕ) (cs : List (Comparator n × ℕ)) (hp : DependencyOrdered cs)
    (hb : ∀ a ∈ cs, a.2 < d) (v : Fin n → α) :
    (ComparatorNetwork.mk (timedLayers d cs).flatten).exec v =
      (ComparatorNetwork.mk (cs.map Prod.fst)).exec v := by
  induction d generalizing cs v with
  | zero =>
    have he : cs = [] := List.eq_nil_iff_forall_not_mem.mpr (by intro a ha; have := hb a ha; omega)
    subst cs
    rfl
  | succ d ih =>
    have hb' : ∀ a ∈ (cs.filter (fun a ↦ a.2 ≠ 0)).map (fun a ↦ (a.1, a.2 - 1)), a.2 < d := by
      intro a ha
      obtain ⟨b, hbmem, rfl⟩ := List.mem_map.mp ha
      obtain ⟨hbmem, hne⟩ := List.mem_filter.mp hbmem
      have hnb : b.2 ≠ 0 := of_decide_eq_true hne
      have hbb := hb b hbmem
      dsimp only
      omega
    change (ComparatorNetwork.mk (((cs.filter (fun a ↦ a.2 = 0)).map Prod.fst) ++
      (timedLayers d ((cs.filter (fun a ↦ a.2 ≠ 0)).map (fun a ↦ (a.1, a.2 - 1)))).flatten)).exec v = _
    rw [ComparatorNetwork.exec_append, ih _ (dependencyOrdered_shift cs hp) hb']
    simp only [List.map_map, Function.comp_def]
    exact (timed_exec_partition cs hp v).symm

end Kahale
