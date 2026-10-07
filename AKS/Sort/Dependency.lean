import AKS.Sort.Depth

/-! # Input dependency cones and necessary conditions for repair

Sources are graph ancestors, not minimal Boolean supports. They give a
kernel-checked fan-in bound in the repository's critical-path depth model.
-/

namespace SortingRepair

open Finset

def sourceStep {n : ℕ} (S : Fin n → Finset (Fin n)) (c : Comparator n)
    (k : Fin n) : Finset (Fin n) :=
  if k = c.i ∨ k = c.j then S c.i ∪ S c.j else S k

def sources {n : ℕ} (net : ComparatorNetwork n) : Fin n → Finset (Fin n) :=
  net.comparators.foldl sourceStep (fun i => {i})

private theorem sourceStep_card {n : ℕ} (S : Fin n → Finset (Fin n))
    (wt : Fin n → ℕ) (dm : ℕ) (h : ∀ k, (S k).card ≤ 2 ^ wt k)
    (c : Comparator n) :
    ∀ k, (sourceStep S c k).card ≤ 2 ^ (depthStep (wt, dm) c).1 k := by
  intro k
  have hu : (S c.i ∪ S c.j).card ≤ 2 ^ (max (wt c.i) (wt c.j) + 1) := by
    calc
      _ ≤ (S c.i).card + (S c.j).card := card_union_le _ _
      _ ≤ 2 ^ wt c.i + 2 ^ wt c.j := Nat.add_le_add (h _) (h _)
      _ ≤ 2 ^ max (wt c.i) (wt c.j) + 2 ^ max (wt c.i) (wt c.j) :=
        Nat.add_le_add (Nat.pow_le_pow_right (by decide) (le_max_left _ _))
          (Nat.pow_le_pow_right (by decide) (le_max_right _ _))
      _ = _ := by rw [pow_succ]; omega
  have hc : c.i ≠ c.j := ne_of_lt c.h
  by_cases hi : k = c.i
  · subst k
    simpa [sourceStep, depthStep, Function.update_apply, hc] using hu
  · by_cases hj : k = c.j
    · subst k
      simpa [sourceStep, depthStep, Function.update_apply] using hu
    · simpa [sourceStep, depthStep, Function.update_apply, hi, hj] using h k

private theorem sourceFold_card {n : ℕ} (cs : List (Comparator n))
    (S : Fin n → Finset (Fin n)) (wt : Fin n → ℕ) (dm : ℕ)
    (h : ∀ k, (S k).card ≤ 2 ^ wt k) :
    ∀ k, (cs.foldl sourceStep S k).card ≤
      2 ^ (cs.foldl depthStep (wt, dm)).1 k := by
  induction cs generalizing S wt dm with
  | nil => exact h
  | cons c cs ih =>
    simpa only [List.foldl_cons, Prod.mk.eta] using
      ih (sourceStep S c) (depthStep (wt, dm) c).1 (depthStep (wt, dm) c).2
        (sourceStep_card S wt dm h c)

theorem sources_card_le_depth {n : ℕ} (net : ComparatorNetwork n) (k : Fin n) :
    (sources net k).card ≤ 2 ^ net.depth := by
  have h := sourceFold_card net.comparators (fun i => {i}) (fun _ => 0) 0
    (by intro i; simp) k
  have hw := wt_le_running_max net.comparators (fun _ => 0) 0 (by simp) k
  exact h.trans (Nat.pow_le_pow_right (by decide) hw)

private def functionStep {n : ℕ} (F : Fin n → (Fin n → Bool) → Bool)
    (c : Comparator n) (k : Fin n) (x : Fin n → Bool) : Bool :=
  c.apply (fun i => F i x) k

private theorem functionFold_eval {n : ℕ} (cs : List (Comparator n))
    (F : Fin n → (Fin n → Bool) → Bool) (x : Fin n → Bool) :
    (fun k => cs.foldl functionStep F k x) =
      (ComparatorNetwork.mk cs).exec (fun k => F k x) := by
  induction cs generalizing F with
  | nil => rfl
  | cons c cs ih =>
    simpa only [List.foldl_cons, ComparatorNetwork.exec, functionStep] using
      ih (functionStep F c)

private theorem functionFold_support {n : ℕ} (cs : List (Comparator n))
    (F : Fin n → (Fin n → Bool) → Bool) (S : Fin n → Finset (Fin n))
    (h : ∀ k x y, (∀ i ∈ S k, x i = y i) → F k x = F k y) :
    ∀ k x y, (∀ i ∈ cs.foldl sourceStep S k, x i = y i) →
      cs.foldl functionStep F k x = cs.foldl functionStep F k y := by
  induction cs generalizing F S with
  | nil => exact h
  | cons c cs ih =>
    apply ih (functionStep F c) (sourceStep S c)
    intro k x y hxy
    by_cases hi : k = c.i
    · subst k
      have ha := h c.i x y (fun i hm => hxy i (by simp [sourceStep, hm]))
      have hb := h c.j x y (fun i hm => hxy i (by simp [sourceStep, hm]))
      simp [functionStep, Comparator.apply, ha, hb]
    · by_cases hj : k = c.j
      · subst k
        have ha := h c.i x y (fun i hm => hxy i (by simp [sourceStep, hm]))
        have hb := h c.j x y (fun i hm => hxy i (by simp [sourceStep, hm]))
        simp [functionStep, Comparator.apply, hi, ha, hb]
      · have hk := h k x y (by simpa [sourceStep, hi, hj] using hxy)
        simpa [functionStep, Comparator.apply, hi, hj] using hk

theorem exec_eq_of_agree_sources {n : ℕ} (net : ComparatorNetwork n)
    (k : Fin n) (x y : Fin n → Bool)
    (h : ∀ i ∈ sources net k, x i = y i) : net.exec x k = net.exec y k := by
  have hs := functionFold_support net.comparators (fun k x => x k) (fun i => {i})
    (by intro k x y hxy; exact hxy k (mem_singleton_self k)) k x y h
  have hx := congrFun (functionFold_eval net.comparators (fun k x => x k) x) k
  have hy := congrFun (functionFold_eval net.comparators (fun k x => x k) y) k
  exact hx.symm.trans (hs.trans hy)

/-- Every single-coordinate pivotal witness forces that coordinate into the
backward cone. The witnesses can belong to a restricted reachable-state set. -/
theorem pivotal_mem_sources {n : ℕ} (net : ComparatorNetwork n) (k i : Fin n)
    (x y : Fin n → Bool) (hxy : ∀ j, j ≠ i → x j = y j)
    (hd : net.exec x k ≠ net.exec y k) : i ∈ sources net k := by
  by_contra hi
  apply hd
  apply exec_eq_of_agree_sources
  intro j hj
  exact hxy j (by intro he; subst j; exact hi hj)

theorem pivotal_card_le_depth {n : ℕ} (net : ComparatorNetwork n) (k : Fin n)
    (I : Finset (Fin n))
    (h : ∀ i ∈ I, ∃ x y : Fin n → Bool,
      (∀ j, j ≠ i → x j = y j) ∧ net.exec x k ≠ net.exec y k) :
    I.card ≤ 2 ^ net.depth := by
  apply (card_le_card ?_).trans (sources_card_le_depth net k)
  intro i hi
  obtain ⟨x, y, hxy, hd⟩ := h i hi
  exact pivotal_mem_sources net k i x y hxy hd

/-- Disjoint sets of possible changes must each meet the output cone. This
allows packet-count witnesses that change a chunk rather than a single bit. -/
theorem disjoint_changes_le_depth {n t : ℕ} (net : ComparatorNetwork n) (k : Fin n)
    (blocks : Fin t → Finset (Fin n))
    (hdis : ∀ a b, a ≠ b → Disjoint (blocks a) (blocks b))
    (h : ∀ a, ∃ x y : Fin n → Bool,
      (∀ i, i ∉ blocks a → x i = y i) ∧ net.exec x k ≠ net.exec y k) :
    t ≤ 2 ^ net.depth := by
  classical
  have hex : ∀ a, ∃ i : Fin n, i ∈ sources net k ∧ i ∈ blocks a := by
    intro a
    obtain ⟨x, y, hxy, hd⟩ := h a
    by_contra he
    push_neg at he
    apply hd
    apply exec_eq_of_agree_sources
    intro i hi
    exact hxy i (he i hi)
  choose f hf using hex
  let g : Fin t → ↥(sources net k) := fun a => ⟨f a, (hf a).1⟩
  have hg : Function.Injective g := by
    intro a b he
    by_contra hab
    have hv : f a = f b := congrArg Subtype.val he
    exact Finset.disjoint_left.mp (hdis a b hab) (hf a).2 (hv ▸ (hf b).2)
  have hc := Fintype.card_le_of_injective g hg
  simp only [Fintype.card_fin, Fintype.card_coe] at hc
  exact hc.trans (sources_card_le_depth net k)

/-- The same obstruction applies to repair on a restricted reachable-state
family, with an arbitrary specified target bit. -/
theorem repair_pivotal_card_le_depth {n : ℕ} (net : ComparatorNetwork n) (k : Fin n)
    (C : Set (Fin n → Bool)) (target : (Fin n → Bool) → Bool)
    (hrepair : ∀ x ∈ C, net.exec x k = target x) (I : Finset (Fin n))
    (h : ∀ i ∈ I, ∃ x ∈ C, ∃ y ∈ C,
      (∀ j, j ≠ i → x j = y j) ∧ target x ≠ target y) :
    I.card ≤ 2 ^ net.depth := by
  apply pivotal_card_le_depth net k I
  intro i hi
  obtain ⟨x, hx, y, hy, hxy, hd⟩ := h i hi
  refine ⟨x, y, hxy, ?_⟩
  rw [hrepair x hx, hrepair y hy]
  exact hd

end SortingRepair
