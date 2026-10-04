module

public import AKS.Kahale.TimedExecution

/-! # The greedy critical-path depth admits an equivalent parallel execution -/

@[expose] public section

namespace Kahale

def stampComparators {n : ℕ} : List (Comparator n) → ((Fin n → ℕ) × ℕ) →
    List (Comparator n × ℕ)
  | [], _ => []
  | c :: cs, state => (c, max (state.1 c.i) (state.1 c.j)) ::
      stampComparators cs (depthStep state c)

theorem stampComparators_fst {n : ℕ} (cs : List (Comparator n)) (state : (Fin n → ℕ) × ℕ) :
    (stampComparators cs state).map Prod.fst = cs := by
  induction cs generalizing state <;> simp [stampComparators, *]

theorem depthStep_clock_mono {n : ℕ} (state : (Fin n → ℕ) × ℕ) (c : Comparator n) (i : Fin n) :
    state.1 i ≤ (depthStep state c).1 i := by
  have h₁ := le_max_left (state.1 c.i) (state.1 c.j)
  have h₂ := le_max_right (state.1 c.i) (state.1 c.j)
  simp only [depthStep, Function.update_apply]
  split_ifs <;> subst_vars <;> omega

theorem stampComparators_touch_clock {n : ℕ} (cs : List (Comparator n))
    (state : (Fin n → ℕ) × ℕ) (a : Comparator n × ℕ) (ha : a ∈ stampComparators cs state)
    (i : Fin n) (hi : a.1.i = i ∨ a.1.j = i) : state.1 i ≤ a.2 := by
  induction cs generalizing state with
  | nil => simp [stampComparators] at ha
  | cons c cs ih =>
    simp only [stampComparators, List.mem_cons] at ha
    rcases ha with rfl | ha
    · rcases hi with hi | hi
      · simpa only [← hi] using le_max_left (state.1 c.i) (state.1 c.j)
      · simpa only [← hi] using le_max_right (state.1 c.i) (state.1 c.j)
    · exact (depthStep_clock_mono state c i).trans (ih (depthStep state c) ha)

theorem stampComparators_ordered {n : ℕ} (cs : List (Comparator n)) (state : (Fin n → ℕ) × ℕ) :
    DependencyOrdered (stampComparators cs state) := by
  induction cs generalizing state with
  | nil => simp [stampComparators, DependencyOrdered]
  | cons c cs ih =>
    apply List.pairwise_cons.mpr
    refine ⟨?_, ih _⟩
    intro b hb hge hn
    have hbad (i : Fin n) (hi : i = c.i ∨ i = c.j) (ht : b.1.i = i ∨ b.1.j = i) : False := by
      have hh := stampComparators_touch_clock cs (depthStep state c) b hb i ht
      have he : (depthStep state c).1 i = max (state.1 c.i) (state.1 c.j) + 1 := by
        rcases hi with rfl | rfl <;> simp [depthStep, Function.update_apply]
      rw [he] at hh
      change max (state.1 c.i) (state.1 c.j) ≥ b.2 at hge
      omega
    rcases hn with hn | hn | hn | hn
    · exact hbad c.i (Or.inl rfl) (Or.inl hn.symm)
    · exact hbad c.i (Or.inl rfl) (Or.inr hn.symm)
    · exact hbad c.j (Or.inr rfl) (Or.inl hn.symm)
    · exact hbad c.j (Or.inr rfl) (Or.inr hn.symm)

theorem stampComparators_bound {n : ℕ} (cs : List (Comparator n)) (state : (Fin n → ℕ) × ℕ) :
    ∀ a ∈ stampComparators cs state, a.2 < (cs.foldl depthStep state).2 := by
  induction cs generalizing state with
  | nil => simp [stampComparators]
  | cons c cs ih =>
    intro a ha
    simp only [stampComparators, List.mem_cons] at ha
    rcases ha with rfl | ha
    · have hm := foldl_dm_le cs (depthStep state c).1 (depthStep state c).2
      rw [Prod.mk.eta] at hm
      have ht : max (state.1 c.i) (state.1 c.j) + 1 ≤ (depthStep state c).2 :=
        le_max_right _ _
      change max (state.1 c.i) (state.1 c.j) < (cs.foldl depthStep (depthStep state c)).2
      omega
    · exact ih (depthStep state c) a ha

def greedyLayers {n : ℕ} (net : ComparatorNetwork n) : List (List (Comparator n)) :=
  timedLayers net.depth (stampComparators net.comparators (fun _ ↦ 0, 0))

theorem greedyLayers_length {n : ℕ} (net : ComparatorNetwork n) :
    (greedyLayers net).length = net.depth := timedLayers_length _ _

theorem greedyLayers_parallel {n : ℕ} (net : ComparatorNetwork n) :
    ∀ cs ∈ greedyLayers net, IsParallelLayer cs :=
  timedLayers_parallel _ _ (stampComparators_ordered _ _)

theorem greedyLayers_exec {n : ℕ} {α : Type*} [LinearOrder α]
    (net : ComparatorNetwork n) (v : Fin n → α) :
    (ComparatorNetwork.mk (greedyLayers net).flatten).exec v = net.exec v := by
  unfold greedyLayers ComparatorNetwork.depth
  rw [timedLayers_exec _ _ (stampComparators_ordered _ _) (stampComparators_bound _ _),
    stampComparators_fst]

end Kahale
