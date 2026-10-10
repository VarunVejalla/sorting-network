module

public import AKS.Kahale.HistoryInnovation

/-! # Joint observations in a nested hierarchy

Coarse observations and their synchronous histories are deterministic maps
of finer observations. Collecting them jointly adds no Shannon entropy.
This does not rule out weighted or nonlinear inequalities between scales.
-/

@[expose] public section

namespace Kahale

open Finset BigOperators

theorem entropy_refinement_joint {Ω β γ : Type*}
    [DecidableEq β] [DecidableEq γ] (source : Finset Ω)
    (fine : Ω → β) (coarsen : β → γ) :
    finiteEntropy source (fun x ↦ (fine x, coarsen (fine x))) =
      finiteEntropy source fine := by
  apply finiteEntropy_eq_of_sameFibers
  intro x hx y hy
  constructor
  · exact congrArg Prod.fst
  · intro h
    exact Prod.ext h (congrArg coarsen h)

theorem observationHistory_coarsen {β γ δ : Type*}
    (observe : ℕ → β → γ) (coarsen : γ → δ) (d : ℕ) (x : β) :
    observationHistory (fun t y ↦ coarsen (observe t y)) d x =
      (observationHistory observe d x).map coarsen := by
  induction d with
  | zero => rfl
  | succ d ih => simp only [observationHistory, List.map_cons, ih]

theorem entropy_joint_hierarchy_history {Ω β γ δ : Type*}
    [DecidableEq γ] [DecidableEq δ]
    (source : Finset Ω) (input : Ω → β) (observe : ℕ → β → γ)
    (coarsen : γ → δ) (d : ℕ) :
    finiteEntropy source (fun x ↦
      (observationHistory observe d (input x),
       observationHistory (fun t y ↦ coarsen (observe t y)) d (input x))) =
      historyEntropy source input observe d := by
  simp_rw [observationHistory_coarsen]
  exact entropy_refinement_joint source
    (fun x ↦ observationHistory observe d (input x)) (List.map coarsen)

/-- The exact layer ledger retains conditional information lost inside blocks.
Here `old` is determined by `input`, and `new` by `output`; the displayed
expressions are respectively innovation, residual dependence, and
conditional internal loss. No sign or slot bound is included. -/
theorem partition_layer_ledger (input output old new joint oldOutput : ℝ) :
    (input - output) + (new - old) =
      (joint - old) - (joint + output - new - oldOutput) +
        (input - oldOutput) := by ring

/-- General history-bank accounting; the joint entropies and their difference
remain explicit until a layer reconstruction theorem is supplied. -/
theorem layer_history_bank_ledger
    (input output past next beforeJoint afterJoint : ℝ) :
    let beforeBank := past + input - beforeJoint
    let afterBank := next + output - afterJoint
    input - output + (afterBank - beforeBank) =
      (next - past) + (beforeJoint - afterJoint) := by
  dsimp only
  ring

/-- Pure crossing specialization under preservation of joint entropy. -/
theorem joint_layer_history_bank_update
    (input output past next beforeJoint afterJoint : ℝ)
    (preserved : afterJoint = beforeJoint) :
    let beforeBank := past + input - beforeJoint
    let afterBank := next + output - afterJoint
    input - output + (afterBank - beforeBank) = next - past := by
  dsimp only
  rw [preserved]
  ring

/-- A hierarchy reorganizes the gain into conditional losses between levels.
The end-level loss is explicit; this alone gives no strict capacity saving. -/
theorem hierarchy_gain_telescope (loss : ℕ → ℝ) (levels : ℕ) :
    ∑ j ∈ Finset.range levels, (loss j - loss (j + 1)) =
      loss 0 - loss levels := bank_telescope loss levels

theorem hierarchy_deficit_identity (loss slots : ℕ → ℝ) (levels : ℕ)
    (leafLoss : loss levels = 0) :
    (∑ j ∈ Finset.range levels, slots j) - loss 0 =
      ∑ j ∈ Finset.range levels, (slots j - (loss j - loss (j + 1))) := by
  rw [Finset.sum_sub_distrib, hierarchy_gain_telescope, leafLoss]
  ring

end Kahale
