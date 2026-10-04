module

public import AKS.Paterson.RootChildAllocation

/-! # Parallel networks on two disjoint fixed register sets -/

@[expose] public section

namespace Paterson.Bags

open Finset

def parallelOnSets {k m : ℕ} (S : Fin 2 → Finset (Fin (2 ^ k)))
    (hS : ∀ s, (S s).card = m) (nets : Fin 2 → ComparatorNetwork m) : ComparatorNetwork (2 ^ k) :=
  ⟨([0, 1] : List (Fin 2)).flatMap fun s ↦
    ((nets s).scatterEmbed (2 ^ k) ((S s).orderEmbOfFin (hS s))).comparators⟩

theorem scattered_comparator_mem {k m : ℕ} (S : Finset (Fin (2 ^ k))) (hS : S.card = m)
    (net : ComparatorNetwork m) (c : Comparator (2 ^ k))
    (hc : c ∈ (net.scatterEmbed (2 ^ k) (S.orderEmbOfFin hS)).comparators) :
    c.i ∈ S ∧ c.j ∈ S := by
  obtain ⟨d, _, rfl⟩ := List.mem_map.mp hc
  exact ⟨orderEmbOfFin_mem S hS d.i, orderEmbOfFin_mem S hS d.j⟩

theorem parallelOnSets_depth_le {k m d : ℕ} (S : Fin 2 → Finset (Fin (2 ^ k)))
    (hS : ∀ s, (S s).card = m) (nets : Fin 2 → ComparatorNetwork m)
    (hdis : Disjoint (S 0) (S 1)) (hd : ∀ s, (nets s).depth ≤ d) :
    (parallelOnSets S hS nets).depth ≤ d := by
  apply depth_flatMap_disjoint
  · intro s _
    exact (depth_scatterEmbed_le _ _ _).trans (hd s)
  · apply List.pairwise_cons.mpr
    constructor
    · intro s hs
      have he : s = 1 := List.mem_singleton.mp hs
      subst s
      intro c hc e he
      have hcS := scattered_comparator_mem (S 0) (hS 0) (nets 0) c hc
      have heS := scattered_comparator_mem (S 1) (hS 1) (nets 1) e he
      have hne {a b : Fin (2 ^ k)} (ha : a ∈ S 0) (hb : b ∈ S 1) : a ≠ b :=
        fun hab ↦ disjoint_left.mp hdis ha (hab ▸ hb)
      exact ⟨⟨hne hcS.1 heS.1, hne hcS.1 heS.2⟩,
        ⟨hne hcS.2 heS.1, hne hcS.2 heS.2⟩⟩
    · simp

theorem parallelOnSets_exec_inside {k m : ℕ} (S : Fin 2 → Finset (Fin (2 ^ k)))
    (hS : ∀ s, (S s).card = m) (nets : Fin 2 → ComparatorNetwork m)
    (hdis : Disjoint (S 0) (S 1)) (w : Fin (2 ^ k) → Fin (2 ^ k))
    (s : Fin 2) (j : Fin m) :
    (parallelOnSets S hS nets).exec w ((S s).orderEmbOfFin (hS s) j) =
      (nets s).exec (w ∘ (S s).orderEmbOfFin (hS s)) j := by
  have houtside (a b : Fin 2) (hab : Disjoint (S a) (S b)) (v : Fin (2 ^ k) → Fin (2 ^ k))
      (l : Fin m) :
      ((nets b).scatterEmbed (2 ^ k) ((S b).orderEmbOfFin (hS b))).exec v
        ((S a).orderEmbOfFin (hS a) l) = v ((S a).orderEmbOfFin (hS a) l) := by
    apply ComparatorNetwork.scatterEmbed_exec_outside
    rw [range_orderEmbOfFin]
    exact fun h ↦ disjoint_left.mp hab (orderEmbOfFin_mem (S a) (hS a) l) h
  unfold parallelOnSets
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
  rw [ComparatorNetwork.exec_append]
  fin_cases s <;> dsimp only
  · change ((nets 1).scatterEmbed (2 ^ k) ((S 1).orderEmbOfFin (hS 1))).exec
      (((nets 0).scatterEmbed (2 ^ k) ((S 0).orderEmbOfFin (hS 0))).exec w)
      ((S 0).orderEmbOfFin (hS 0) j) = (nets 0).exec (w ∘ (S 0).orderEmbOfFin (hS 0)) j
    rw [houtside 0 1 hdis, ComparatorNetwork.scatterEmbed_exec_inside]
  · change ((nets 1).scatterEmbed (2 ^ k) ((S 1).orderEmbOfFin (hS 1))).exec
      (((nets 0).scatterEmbed (2 ^ k) ((S 0).orderEmbOfFin (hS 0))).exec w)
      ((S 1).orderEmbOfFin (hS 1) j) = (nets 1).exec (w ∘ (S 1).orderEmbOfFin (hS 1)) j
    rw [ComparatorNetwork.scatterEmbed_exec_inside]
    have hview :
        (((nets 0).scatterEmbed (2 ^ k) ((S 0).orderEmbOfFin (hS 0))).exec w) ∘
          (S 1).orderEmbOfFin (hS 1) = w ∘ (S 1).orderEmbOfFin (hS 1) := by
      funext l
      exact houtside 1 0 hdis.symm w l
    rw [hview]

end Paterson.Bags
