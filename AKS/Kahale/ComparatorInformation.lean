module

public import AKS.Kahale.FiniteEntropy
public import AKS.Kahale.ComparatorBoundary
public import Mathlib.Tactic.Ring

/-! # Exact comparator information gain

The theorem uses actual multiplicities of the uniform input source. It is an
identity, not a quantitative amortized bound or a nonnegativity theorem.
-/

@[expose] public section

namespace Kahale

def untouchedRanks {n : ℕ} (c : Comparator n) (v : Fin n → Fin n) :
    Fin n → Option (Fin n) := fun k ↦
  if k = c.i ∨ k = c.j then none else some (v k)

theorem untouchedRanks_eq_iff {n : ℕ} (c : Comparator n)
    (v w : Fin n → Fin n) :
    untouchedRanks c v = untouchedRanks c w ↔
      ∀ k, k ≠ c.i → k ≠ c.j → v k = w k := by
  constructor
  · intro h k hi hj
    simpa [untouchedRanks, hi, hj] using congrFun h k
  · intro h
    funext k
    by_cases hk : k = c.i ∨ k = c.j
    · simp [untouchedRanks, hk]
    · have hi := (not_or.mp hk).1
      have hj := (not_or.mp hk).2
      simp [untouchedRanks, hi, hj, h k hi hj]

theorem entropy_comparator_output_eq_untouched {α : Type*} {n : ℕ}
    (source : Finset α) (f : α → Fin n → Fin n) (c : Comparator n)
    (hinj : ∀ x ∈ source, Function.Injective (f x)) :
    finiteEntropy source (fun x ↦ c.apply (f x)) =
      finiteEntropy source (fun x ↦ untouchedRanks c (f x)) := by
  classical
  apply finiteEntropy_eq_of_sameFibers
  intro x hx y hy
  constructor
  · intro h
    apply (untouchedRanks_eq_iff c (f y) (f x)).mpr
    intro k hi hj
    simpa [Comparator.apply, hi, hj] using congrFun h k
  · intro h
    exact comparator_output_of_untouched_ranks c (f y) (f x) (hinj y hy) (hinj x hx)
      ((untouchedRanks_eq_iff c (f y) (f x)).mp h)

theorem entropy_input_eq_untouched_and_rank {α : Type*} {n : ℕ}
    (source : Finset α) (f : α → Fin n → Fin n) (c : Comparator n)
    (hinj : ∀ x ∈ source, Function.Injective (f x)) :
    finiteEntropy source f =
      finiteEntropy source (fun x ↦ (untouchedRanks c (f x), f x c.i)) := by
  classical
  apply finiteEntropy_eq_of_sameFibers
  intro x hx y hy
  constructor
  · intro h; rw [h]
  · intro h
    have ht := (untouchedRanks_eq_iff c (f y) (f x)).mp (congrArg Prod.fst h)
    have ha : f y c.i = f x c.i := congrArg Prod.snd h
    apply permutation_eq_of_agree_except_one (f y) (f x) (hinj y hy) (hinj x hx) c.j
    intro k hj
    by_cases hi : k = c.i
    · subst k; exact ha
    · exact ht k hi hj

noncomputable def orientationEntropy {α : Type*} {n : ℕ}
    (source : Finset α) (f : α → Fin n → Fin n) (c : Comparator n) : ℝ :=
  finiteEntropy source (fun x ↦ (coordinateRankSet (untouchedRanks c (f x)), f x c.i)) -
    finiteEntropy source (fun x ↦ coordinateRankSet (untouchedRanks c (f x)))

noncomputable def untouchedCoupling {α : Type*} {n : ℕ}
    (source : Finset α) (f : α → Fin n → Fin n) (c : Comparator n) : ℝ :=
  finiteEntropy source (fun x ↦ untouchedRanks c (f x)) +
    finiteEntropy source (fun x ↦ (coordinateRankSet (untouchedRanks c (f x)), f x c.i)) -
    finiteEntropy source (fun x ↦ coordinateRankSet (untouchedRanks c (f x))) -
    finiteEntropy source (fun x ↦ (untouchedRanks c (f x), f x c.i))

theorem comparator_information_identity {α : Type*} {n : ℕ}
    (source : Finset α) (f : α → Fin n → Fin n) (c : Comparator n)
    (hinj : ∀ x ∈ source, Function.Injective (f x)) :
    finiteEntropy source f - finiteEntropy source (fun x ↦ c.apply (f x)) =
      orientationEntropy source f c - untouchedCoupling source f c := by
  rw [entropy_input_eq_untouched_and_rank source f c hinj,
    entropy_comparator_output_eq_untouched source f c hinj]
  unfold orientationEntropy untouchedCoupling
  ring

end Kahale
