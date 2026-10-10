module

public import AKS.Kahale.EntropyMonotonicity
public import AKS.Kahale.AmortizedAccounting

/-! # Fresh innovation conditioned on the complete observation history

The history is written newest first. Its entropy increments count only fresh
information. The bound is generally leading order, not a subleading reserve
or a proof that comparators waste a positive fraction of their capacity.
-/

@[expose] public section

namespace Kahale

open Finset BigOperators

def observationHistory {β γ : Type*} (observe : ℕ → β → γ) : ℕ → β → List γ
  | 0, x => [observe 0 x]
  | d + 1, x => observe (d + 1) x :: observationHistory observe d x

noncomputable def historyEntropy {Ω β γ : Type*} [DecidableEq γ]
    (source : Finset Ω) (input : Ω → β) (observe : ℕ → β → γ) (d : ℕ) : ℝ :=
  finiteEntropy source (fun x ↦ observationHistory observe d (input x))

theorem historyEntropy_initial {Ω β γ : Type*} [DecidableEq γ]
    (source : Finset Ω) (input : Ω → β) (observe : ℕ → β → γ) :
    historyEntropy source input observe 0 =
      finiteEntropy source (fun x ↦ observe 0 (input x)) := by
  apply finiteEntropy_eq_of_sameFibers
  intro x hx y hy
  simp [observationHistory]

theorem history_innovation_nonneg {Ω β γ : Type*} [DecidableEq γ]
    (source : Finset Ω) (input : Ω → β) (observe : ℕ → β → γ) (d : ℕ) :
    0 ≤ historyEntropy source input observe (d + 1) -
      historyEntropy source input observe d := by
  have h := finiteEntropy_comp_le source
    (fun x ↦ observationHistory observe (d + 1) (input x)) List.tail
  simp only [observationHistory] at h
  exact sub_nonneg.mpr h

theorem historyEntropy_le_input {Ω β γ : Type*} [DecidableEq β] [DecidableEq γ]
    (source : Finset Ω) (input : Ω → β) (observe : ℕ → β → γ) (d : ℕ) :
    historyEntropy source input observe d ≤ finiteEntropy source input :=
  finiteEntropy_comp_le source input (observationHistory observe d)

theorem history_innovation_telescope {Ω β γ : Type*} [DecidableEq γ]
    (source : Finset Ω) (input : Ω → β) (observe : ℕ → β → γ) (d : ℕ) :
    (∑ t ∈ Finset.range d, (historyEntropy source input observe (t + 1) -
      historyEntropy source input observe t)) =
        historyEntropy source input observe d - historyEntropy source input observe 0 := by
  induction d with
  | zero => simp
  | succ d ih => rw [Finset.sum_range_succ, ih]; ring

/-- Conditioning innovation on the full history prevents recycled observations
from being charged as fresh input information. -/
theorem fresh_history_innovation_budget {Ω β γ : Type*}
    [DecidableEq β] [DecidableEq γ]
    (source : Finset Ω) (input : Ω → β) (observe : ℕ → β → γ) (d : ℕ) :
    (∑ t ∈ Finset.range d, (historyEntropy source input observe (t + 1) -
      historyEntropy source input observe t)) ≤
        finiteEntropy source input - finiteEntropy source (fun x ↦ observe 0 (input x)) := by
  rw [history_innovation_telescope, ← historyEntropy_initial source input observe]
  exact sub_le_sub_right (historyEntropy_le_input source input observe d) _

end Kahale
