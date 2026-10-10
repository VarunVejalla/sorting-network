module

public import AKS.Kahale.RankSetTransition

/-! # Exact history-bank update at a crossing comparator

The old history must determine the old rank set. No conditional information
inequality or quantitative layer saving is assumed or proved here.
-/

@[expose] public section

namespace Kahale

theorem crossing_history_joint_entropy {Ω β γ : Type*}
    [DecidableEq β] [DecidableEq γ]
    (source : Finset Ω) (rest : Ω → β) (ranks : β → Finset ℕ) (a b : Ω → ℕ)
    (past : Ω → γ) (decode : γ → Finset ℕ)
    (records : ∀ x ∈ source, decode (past x) = crossingRankSet rest ranks a x)
    (outside : ∀ x ∈ source, a x ∉ ranks (rest x)) :
    finiteEntropy source (fun x ↦ (past x, crossingInput rest a b x)) =
      finiteEntropy source (fun x ↦ (past x, crossingOutput rest a b x)) := by
  apply finiteEntropy_eq_of_sameFibers
  intro x hx y hy
  constructor
  · intro h
    have hp : past y = past x := congrArg Prod.fst h
    have hi : crossingInput rest a b y = crossingInput rest a b x := congrArg Prod.snd h
    have hr : rest y = rest x := congrArg Prod.fst hi
    have ha : a y = a x := congrArg (fun z ↦ z.2.1) hi
    have hb : b y = b x := congrArg (fun z ↦ z.2.2) hi
    simp only [crossingOutput, hp, hr, ha, hb]
  · intro h
    have hp : past y = past x := congrArg Prod.fst h
    have ho : crossingOutput rest a b y = crossingOutput rest a b x := congrArg Prod.snd h
    have hs : crossingRankSet rest ranks a y = crossingRankSet rest ranks a x := by
      rw [← records y hy, ← records x hx, hp]
    have hi := (crossing_reconstruction_fibers source rest ranks a b outside
      x hx y hy).mp (Prod.ext hs ho)
    exact Prod.ext hp hi

theorem crossing_extended_history_joint_entropy {Ω β γ : Type*}
    [DecidableEq β] [DecidableEq γ]
    (source : Finset Ω) (rest : Ω → β) (ranks : β → Finset ℕ) (a b : Ω → ℕ)
    (past : Ω → γ) :
    finiteEntropy source (fun x ↦
      ((past x, crossingRankSet rest ranks (fun z ↦ min (a z) (b z)) x),
        crossingOutput rest a b x)) =
      finiteEntropy source (fun x ↦ (past x, crossingOutput rest a b x)) := by
  apply finiteEntropy_eq_of_sameFibers
  intro x hx y hy
  constructor
  · intro h
    have hp : past y = past x := congrArg (fun z ↦ z.1.1) h
    have ho : crossingOutput rest a b y = crossingOutput rest a b x := congrArg Prod.snd h
    exact Prod.ext hp ho
  · intro h
    have hp : past y = past x := congrArg Prod.fst h
    have ho : crossingOutput rest a b y = crossingOutput rest a b x := congrArg Prod.snd h
    have hs : crossingRankSet rest ranks (fun z ↦ min (a z) (b z)) y =
        crossingRankSet rest ranks (fun z ↦ min (a z) (b z)) x :=
      congrArg (fun z ↦ insert z.2.1 (ranks z.1)) ho
    exact Prod.ext (Prod.ext hp hs) ho

/-- Gain plus change in the mutual-information history bank equals fresh
history entropy. This is an equality, not a bound on the right side. -/
theorem crossing_history_bank_update {Ω β γ : Type*}
    [DecidableEq β] [DecidableEq γ]
    (source : Finset Ω) (rest : Ω → β) (ranks : β → Finset ℕ) (a b : Ω → ℕ)
    (past : Ω → γ) (decode : γ → Finset ℕ)
    (records : ∀ x ∈ source, decode (past x) = crossingRankSet rest ranks a x)
    (outside : ∀ x ∈ source, a x ∉ ranks (rest x)) :
    let input := crossingInput rest a b
    let output := crossingOutput rest a b
    let next := fun x ↦ (past x, crossingRankSet rest ranks (fun z ↦ min (a z) (b z)) x)
    let beforeBank := finiteEntropy source past + finiteEntropy source input -
      finiteEntropy source (fun x ↦ (past x, input x))
    let afterBank := finiteEntropy source next + finiteEntropy source output -
      finiteEntropy source (fun x ↦ (next x, output x))
    finiteEntropy source input - finiteEntropy source output + (afterBank - beforeBank) =
      finiteEntropy source next - finiteEntropy source past := by
  dsimp only
  rw [crossing_history_joint_entropy source rest ranks a b past decode records outside,
    crossing_extended_history_joint_entropy source rest ranks a b past]
  ring

/-- For a fixed history, the right side is the conditional entropy loss.
Applying this to internal comparators still requires their block projection. -/
theorem fixed_history_bank_update {Ω β δ γ : Type*}
    [DecidableEq β] [DecidableEq δ] [DecidableEq γ]
    (source : Finset Ω) (input : Ω → β) (output : Ω → δ) (past : Ω → γ) :
    let beforeBank := finiteEntropy source past + finiteEntropy source input -
      finiteEntropy source (fun x ↦ (past x, input x))
    let afterBank := finiteEntropy source past + finiteEntropy source output -
      finiteEntropy source (fun x ↦ (past x, output x))
    finiteEntropy source input - finiteEntropy source output + (afterBank - beforeBank) =
      finiteEntropy source (fun x ↦ (past x, input x)) -
        finiteEntropy source (fun x ↦ (past x, output x)) := by
  dsimp only
  ring

end Kahale
