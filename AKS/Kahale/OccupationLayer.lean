module

public import AKS.Kahale.FaceTransport

/-! # Occupation polarization and a conditional face-coalescence budget

The occupation drop is proved for actual finite Boolean signals. The energy
budget takes the face-count update and spectral nonnegativity as explicit
hypotheses; no Johnson-graph spectral theorem or height tradeoff is asserted.
-/

@[expose] public section

namespace Kahale

open Finset BigOperators

def boolPopulation {ι : Type*} [Fintype ι] (v : ι → Bool) : ℝ :=
  ∑ x, if v x then 1 else 0

def occupationVariance (mass ones : ℝ) : ℝ := ones * (mass - ones)

def occupationEnergy (wires mass unresolved variance : ℝ) : ℝ :=
  2 * mass * unresolved - wires * variance

theorem boolPopulation_left_split {ι : Type*} [Fintype ι]
    (v w : ι → Bool) :
    boolPopulation v = boolPopulation (fun x => v x && !w x) +
      boolPopulation (fun x => v x && w x) := by
  unfold boolPopulation
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x _
  cases hv : v x <;> cases hw : w x <;> simp [hv, hw]

theorem boolPopulation_right_split {ι : Type*} [Fintype ι]
    (v w : ι → Bool) :
    boolPopulation w = boolPopulation (fun x => !v x && w x) +
      boolPopulation (fun x => v x && w x) := by
  unfold boolPopulation
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x _
  cases hv : v x <;> cases hw : w x <;> simp [hv, hw]

theorem boolPopulation_join_split {ι : Type*} [Fintype ι]
    (v w : ι → Bool) :
    boolPopulation (fun x => v x || w x) =
      boolPopulation (fun x => v x && !w x) +
      boolPopulation (fun x => !v x && w x) +
      boolPopulation (fun x => v x && w x) := by
  unfold boolPopulation
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x _
  cases hv : v x <;> cases hw : w x <;> simp [hv, hw]

theorem occupationVariance_cell_drop (mass a b t : ℝ) :
    occupationVariance mass (a + t) + occupationVariance mass (b + t) -
      (occupationVariance mass t + occupationVariance mass (a + b + t)) =
        2 * a * b := by
  unfold occupationVariance
  ring

/-- Actual occupation polarization at an AND/OR comparator. -/
theorem occupationVariance_bool_drop {ι : Type*} [Fintype ι]
    (mass : ℝ) (v w : ι → Bool) :
    occupationVariance mass (boolPopulation v) +
      occupationVariance mass (boolPopulation w) -
      (occupationVariance mass (boolPopulation (fun x => v x && w x)) +
       occupationVariance mass (boolPopulation (fun x => v x || w x))) =
        2 * boolPopulation (fun x => v x && !w x) *
          boolPopulation (fun x => !v x && w x) := by
  rw [boolPopulation_left_split v w, boolPopulation_right_split v w,
    boolPopulation_join_split v w]
  exact occupationVariance_cell_drop _ _ _ _

/-- Summing the actual gate identity; disjointness is needed when interpreting
this pair sum as the variance of a full wire layer. -/
theorem occupationVariance_layer_drop {ι γ : Type*} [Fintype ι] [Fintype γ]
    (mass : ℝ) (v w : γ → ι → Bool) :
    (∑ e, (occupationVariance mass (boolPopulation (v e)) +
      occupationVariance mass (boolPopulation (w e)))) -
    (∑ e, (occupationVariance mass (boolPopulation (fun x => v e x && w e x)) +
      occupationVariance mass (boolPopulation (fun x => v e x || w e x)))) =
    2 * ∑ e, (boolPopulation (fun x => v e x && !w e x) *
      boolPopulation (fun x => !v e x && w e x)) := by
  rw [← Finset.sum_sub_distrib, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e _
  simpa only [mul_assoc] using occupationVariance_bool_drop mass (v e) (w e)

theorem occupationEnergy_layer_update (n mass r r' g g' kills products : ℝ)
    (hr : r' = r - kills) (hg : g' = g - 2 * products) :
    occupationEnergy n mass r' g' =
      occupationEnergy n mass r g - 2 * mass * kills + 2 * n * products := by
  rw [hr, hg]
  unfold occupationEnergy
  ring

/-- A genuine inequality, conditional on the global spectral constraint. -/
theorem occupationEnergy_coalescence_budget (n mass r r' g g' kills products : ℝ)
    (hr : r' = r - kills) (hg : g' = g - 2 * products)
    (hspectral : 0 ≤ occupationEnergy n mass r' g') :
    2 * mass * kills ≤ occupationEnergy n mass r g + 2 * n * products := by
  have h := occupationEnergy_layer_update n mass r r' g g' kills products hr hg
  linarith

end Kahale
