import D2CrossingToDisplacement

/-! Composition interface for a possible logarithmic rank-displacement proof.

Each `stage` is a map of wire positions and moves every key by at most `C`
ranks. The composite of `t` such stages then moves every key by at most
`t*C`. (The actual network maps will be bijections, but the estimate does not
need that fact.) This isolates global accounting from the construction-
specific proof that one actual D2 stage satisfies the local bound.
-/

namespace Chvatal.D2RankDisplacementComposition

def within (C : Nat) {n : Nat} (f : Fin n -> Fin n) : Prop :=
  forall p, (f p).val <= p.val + C /\ p.val <= (f p).val + C

theorem comp_within_add {n C D : Nat} {f g : Fin n -> Fin n}
    (hf : within C f) (hg : within D g) :
    within (C + D) (g ∘ f) := by
  intro p
  change (g (f p)).val ≤ p.val + (C + D) ∧
    p.val ≤ (g (f p)).val + (C + D)
  obtain ⟨hgf, hfg⟩ := hf p
  obtain ⟨hgg, hgg'⟩ := hg (f p)
  constructor <;> omega

def runStages {n : Nat} : List (Fin n -> Fin n) -> Fin n -> Fin n
  | [], p => p
  | stage :: stages, p => runStages stages (stage p)

theorem runStages_within {n C : Nat} (stages : List (Fin n -> Fin n))
    (hstage : forall stage, stage ∈ stages → within C stage) :
    within (stages.length * C) (runStages stages) := by
  induction stages with
  | nil =>
      intro p
      change p.val ≤ p.val + 0 * C ∧ p.val ≤ p.val + 0 * C
      omega
  | cons stage stages ih =>
      change within ((stages.length + 1) * C)
        (runStages stages ∘ stage)
      have hfirst : within C stage := hstage stage (by simp)
      have hrest : forall f, f ∈ stages → within C f := by
        intro f hf
        exact hstage f (by simp [hf])
      have htail : within (stages.length * C) (runStages stages) := ih hrest
      have hcomp := comp_within_add hfirst htail
      simpa [Nat.add_mul, Nat.one_mul, Nat.add_comm] using hcomp

theorem crossing_stages_run_within {n C : Nat}
    (stages : List (Fin n -> Fin n))
    (hLow : forall stage, stage ∈ stages → forall k p, k + C <= p →
      D2CrossingToDisplacement.lowKeysInSuffix stage k p = 0)
    (hHigh : forall stage, stage ∈ stages → forall k p, p + C < k →
      D2CrossingToDisplacement.highKeysInPrefix stage k p = 0) :
    within (stages.length * C) (runStages stages) := by
  apply runStages_within
  intro stage hmem p
  exact D2CrossingToDisplacement.pointwise_displacement_le stage
    (hLow stage hmem) (hHigh stage hmem) p

end Chvatal.D2RankDisplacementComposition
