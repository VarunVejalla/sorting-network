module

public import AKS.Kahale.BoundaryTransfer
public import Lean.Elab.Tactic.Omega

/-! # A crossing comparison's rank-set transition ledger

Ranks use `ℕ`; the untouched data may have any decidable type. These are
exact identities, not bounds on innovation or an improved depth theorem.
-/

@[expose] public section

namespace Kahale

def crossingInput {Ω β : Type*} (rest : Ω → β) (a b : Ω → ℕ) (x : Ω) :=
  (rest x, (a x, b x))

def crossingOutput {Ω β : Type*} (rest : Ω → β) (a b : Ω → ℕ) (x : Ω) :=
  (rest x, (min (a x) (b x), max (a x) (b x)))

def crossingRankSet {Ω β : Type*} (rest : Ω → β) (ranks : β → Finset ℕ)
    (a : Ω → ℕ) (x : Ω) := insert (a x) (ranks (rest x))

theorem crossing_reconstruction_fibers {Ω β : Type*}
    (source : Finset Ω) (rest : Ω → β) (ranks : β → Finset ℕ) (a b : Ω → ℕ)
    (outside : ∀ x ∈ source, a x ∉ ranks (rest x))
    (x : Ω) (_hx : x ∈ source) (y : Ω) (hy : y ∈ source) :
    (crossingRankSet rest ranks a y, crossingOutput rest a b y) =
      (crossingRankSet rest ranks a x, crossingOutput rest a b x) ↔
    crossingInput rest a b y = crossingInput rest a b x := by
  constructor
  · intro h
    have hs : insert (a y) (ranks (rest y)) = insert (a x) (ranks (rest x)) :=
      congrArg Prod.fst h
    have ho : crossingOutput rest a b y = crossingOutput rest a b x :=
      congrArg Prod.snd h
    have hr : rest y = rest x := congrArg Prod.fst ho
    have hm : a y ∈ insert (a x) (ranks (rest x)) :=
      hs ▸ Finset.mem_insert_self (a y) (ranks (rest y))
    have ha : a y = a x := by
      rcases Finset.mem_insert.mp hm with he | he
      · exact he
      · exact False.elim (outside y hy (hr.symm ▸ he))
    have hmin : min (a y) (b y) = min (a x) (b x) :=
      congrArg (fun z ↦ z.2.1) ho
    have hmax : max (a y) (b y) = max (a x) (b x) :=
      congrArg (fun z ↦ z.2.2) ho
    have hb : b y = b x := by
      rw [ha] at hmin hmax
      rcases le_total (a x) (b y) with h₁ | h₁ <;>
        rcases le_total (a x) (b x) with h₂ | h₂
      all_goals simp only [min_eq_left, min_eq_right, max_eq_left, max_eq_right,
        h₁, h₂] at hmin hmax
      all_goals omega
    exact Prod.ext hr (Prod.ext ha hb)
  · intro h
    have hr : rest y = rest x := congrArg Prod.fst h
    have ha : a y = a x := congrArg (fun z ↦ z.2.1) h
    have hb : b y = b x := congrArg (fun z ↦ z.2.2) h
    simp only [crossingRankSet, crossingOutput, hr, ha, hb]

theorem crossing_reconstruction_entropy {Ω β : Type*} [DecidableEq β]
    (source : Finset Ω) (rest : Ω → β) (ranks : β → Finset ℕ) (a b : Ω → ℕ)
    (outside : ∀ x ∈ source, a x ∉ ranks (rest x)) :
    finiteEntropy source (fun x ↦
      (crossingRankSet rest ranks a x, crossingOutput rest a b x)) =
      finiteEntropy source (crossingInput rest a b) := by
  apply finiteEntropy_eq_of_sameFibers
  intro x hx y hy
  exact crossing_reconstruction_fibers source rest ranks a b outside x hx y hy

/-- Innovation is conditional entropy of the new rank set given the old.
The residual expression is conditional mutual information because the new
rank set is a deterministic function of the comparator output. -/
theorem crossing_rankSet_ledger {Ω β : Type*} [DecidableEq β]
    (source : Finset Ω) (rest : Ω → β) (ranks : β → Finset ℕ) (a b : Ω → ℕ)
    (outside : ∀ x ∈ source, a x ∉ ranks (rest x)) :
    let old := crossingRankSet rest ranks a
    let new := crossingRankSet rest ranks (fun x ↦ min (a x) (b x))
    let output := crossingOutput rest a b
    let joint := finiteEntropy source (fun x ↦ (old x, new x))
    (finiteEntropy source (crossingInput rest a b) - finiteEntropy source output) +
      (finiteEntropy source new - finiteEntropy source old) =
      (joint - finiteEntropy source old) -
        (joint + finiteEntropy source output - finiteEntropy source new -
          finiteEntropy source (fun x ↦ (old x, output x))) := by
  dsimp only
  rw [crossing_reconstruction_entropy source rest ranks a b outside]
  ring

/-- Complementary block coupling supplies no additional linear coordinate
beyond the rank-set entropy and the two relative-order entropies. -/
theorem complementary_block_ledger (whole left right rankSet : ℝ) :
    let orderLeft := left - rankSet
    let orderRight := right - rankSet
    let coupling := left + right - rankSet - whole
    whole = rankSet + orderLeft + orderRight - coupling := by
  dsimp only
  ring

theorem two_block_boundary_transfer {Ω ι κ α : Type*}
    [Fintype ι] [Fintype κ] [LinearOrder α]
    (source : Finset Ω) (left : Ω → ι → α) (right : Ω → κ → α)
    (a b a' b' : Ω → α)
    (ha : ∀ x ∈ source, a x ∉ coordinateRankSet (left x))
    (hb : ∀ x ∈ source, b x ∉ coordinateRankSet (right x))
    (ha' : ∀ x ∈ source, a' x ∉ coordinateRankSet (left x))
    (hb' : ∀ x ∈ source, b' x ∉ coordinateRankSet (right x)) :
    (blockRelativeEntropy source left a' - blockRelativeEntropy source left a) +
      (blockRelativeEntropy source right b' - blockRelativeEntropy source right b) =
    (insertionEntropy source left a' - insertionEntropy source left a) +
      (insertionEntropy source right b' - insertionEntropy source right b) -
    ((boundaryCoupling source left a' - boundaryCoupling source left a) +
      (boundaryCoupling source right b' - boundaryCoupling source right b)) := by
  rw [boundary_transfer_identity source left a a' ha ha',
    boundary_transfer_identity source right b b' hb hb']
  ring

end Kahale
