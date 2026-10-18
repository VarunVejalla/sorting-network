import RaggedTreeRoute

namespace Tapered945

open Chvatal

def rootUpSource {d : Nat} (hd : 1 ≤ d) : Option (Fin 64) → KBag 64 d
  | none => KBag.root 64 d
  | some j => (KBag.root 64 d).child j.val j.isLt (by exact hd)

theorem rootUpSource_injective {d : Nat} (hd : 1 ≤ d) :
    Function.Injective (rootUpSource hd) := by
  intro p q heq
  cases p with
  | none =>
    cases q with
    | none => rfl
    | some j =>
      have hl := congrArg KBag.l heq
      simp [rootUpSource, KBag.root, KBag.child] at hl
  | some i =>
    cases q with
    | none =>
      have hl := congrArg KBag.l heq
      simp [rootUpSource, KBag.root, KBag.child] at hl
    | some j =>
      have hx := congrArg KBag.x heq
      simp [rootUpSource, KBag.root, KBag.child] at hx
      exact congrArg some (Fin.ext hx)

theorem raggedTreeDestination_root_iff {d : Nat} (hd : 1 ≤ d)
    (b : KBag 64 d) (p : Option (Fin 64)) :
    raggedTreeDestination b p = KBag.root 64 d ↔
      p = none ∧ ∃ j : Option (Fin 64), b = rootUpSource hd j := by
  cases p with
  | none =>
    constructor
    · intro heq
      have hl : b.l - 1 = 0 := congrArg KBag.l heq
      refine ⟨rfl, ?_⟩
      by_cases hb : b.l = 0
      · refine ⟨none, ?_⟩
        have hx := b.hx
        simp only [hb, pow_zero] at hx
        apply KBag.ext <;> simp [rootUpSource, KBag.root] <;> omega
      · have hbpos : 1 ≤ b.l := by omega
        have hc := KBag.parent_child b hbpos (by norm_num : 1 ≤ 64)
          (by change b.l - 1 < d; omega)
        change b.parent (by norm_num) = KBag.root 64 d at heq
        have hrootChild : (KBag.root 64 d).child (b.x % 64)
            (Nat.mod_lt _ (by norm_num)) (by exact hd) = b := by
          simpa only [heq] using hc
        exact ⟨some ⟨b.x % 64, Nat.mod_lt _ (by norm_num)⟩, hrootChild.symm⟩
    · rintro ⟨_, j, rfl⟩
      cases j with
      | none => simp [raggedTreeDestination, rootUpSource, KBag.root, KBag.parent]
      | some j => exact raggedTreeDestination_child_up _ (by exact hd) j
  | some j =>
    constructor
    · intro heq
      by_cases hb : b.l < d
      · rw [raggedTreeDestination_down b j hb] at heq
        have hl := congrArg KBag.l heq
        simp [KBag.child, KBag.root] at hl
      · have hbr : b = KBag.root 64 d := by
          simpa [raggedTreeDestination, hb] using heq
        have hl : b.l = 0 := congrArg KBag.l hbr
        omega
    · rintro ⟨h, _⟩
      cases h

theorem routeRaggedWires_root_card {d : Nat} (hd : 1 ≤ d)
    (P : RaggedWirePartition d) (splits : ∀ b, RaggedWireSplit (P.sets b)) :
    (routeRaggedWires P.sets splits raggedTreeDestination (KBag.root 64 d)).card =
      (splits (KBag.root 64 d)).up +
        ∑ j : Fin 64, (splits ((KBag.root 64 d).child j.val j.isLt (by exact hd))).up := by
  classical
  let ports := fun j : Option (Fin 64) => raggedWirePort (splits (rootUpSource hd j)) none
  have hsets : routeRaggedWires P.sets splits raggedTreeDestination (KBag.root 64 d) =
      Finset.univ.biUnion ports := by
    ext w
    rw [mem_routeRaggedWires]
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨b, p, hb, hw⟩
      obtain ⟨rfl, j, rfl⟩ := (raggedTreeDestination_root_iff hd b p).mp hb
      exact ⟨j, hw⟩
    · rintro ⟨j, hw⟩
      exact ⟨rootUpSource hd j, none,
        (raggedTreeDestination_root_iff hd _ none).mpr ⟨rfl, j, rfl⟩, hw⟩
  have hdisj : (↑(Finset.univ : Finset (Option (Fin 64))) : Set _).PairwiseDisjoint ports := by
    intro i hi j hj hij
    apply Finset.disjoint_of_subset_left (raggedWirePort_subset _ _)
    apply Finset.disjoint_of_subset_right (raggedWirePort_subset _ _)
    exact P.disjoint _ _ (fun he => hij (rootUpSource_injective hd he))
  rw [hsets, Finset.card_biUnion hdisj]
  simp [ports, raggedWirePort_card, Fintype.sum_option, rootUpSource]

end Tapered945
