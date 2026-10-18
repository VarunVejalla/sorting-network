import RaggedPrefixRoute

namespace Tapered945

open Chvatal

/-- Threshold populations, not merely total wire counts, are conserved by
the same physical split. All 64 child slots form one cohort. -/
theorem raggedWireSplit_threshold_conservation {n : Nat} {s : Finset (Fin n)}
    (split : RaggedWireSplit s) (good : Fin n → Prop) [DecidablePred good] :
    ((upSet s split.up).filter good).card +
      ∑ j : Fin 64, ((raggedDownSet s split.up split.widths j.val).filter good).card =
        (s.filter good).card := by
  have hcover := congrArg (fun z : Finset (Fin n) => (z.filter good).card)
    (raggedWireSplit_union split)
  dsimp only at hcover
  rw [Finset.filter_union, Finset.filter_biUnion] at hcover
  have hd : Disjoint ((upSet s split.up).filter good)
      ((Finset.range 64).biUnion fun j => (raggedDownSet s split.up split.widths j).filter good) := by
    rw [Finset.disjoint_biUnion_right]
    intro j hj
    exact Finset.disjoint_of_subset_left (Finset.filter_subset _ _)
      (Finset.disjoint_of_subset_right (Finset.filter_subset _ _)
        (raggedUpDown_disjoint split j (Finset.mem_range.mp hj)))
  have hp : (Finset.range 64 : Set Nat).PairwiseDisjoint
      (fun j => (raggedDownSet s split.up split.widths j).filter good) := by
    intro i hi j hj hne
    apply Finset.disjoint_of_subset_left (Finset.filter_subset _ _)
    apply Finset.disjoint_of_subset_right (Finset.filter_subset _ _)
    rcases lt_or_gt_of_ne hne with hij | hji
    · exact raggedDownSet_disjoint split hij
    · exact (raggedDownSet_disjoint split hji).symm
  rw [Finset.card_union_of_disjoint hd, Finset.card_biUnion hp] at hcover
  have hsum := Fin.sum_univ_eq_sum_range
    (fun j => ((raggedDownSet s split.up split.widths j).filter good).card) 64
  rw [hsum]
  exact hcover

/-- A whole up-port retains every threshold population exactly. This covers
the lower contraction and meeting sources without 64 separate rank errors. -/
theorem raggedWirePort_whole_up {n : Nat} {s : Finset (Fin n)}
    (split : RaggedWireSplit s) (hup : split.up = s.card) :
    raggedWirePort split none = s := by
  apply Finset.eq_of_subset_of_card_le (raggedWirePort_subset split none)
  rw [raggedWirePort_card, hup]

/-- A preceding expansion creates a threshold-specific cohort identity on
the actual execution, provided these are its physical child registers.
Local sorting of any of the children in the next stage cannot change it. -/
theorem ragged_expansion_threshold_cohort {d : Nat} (P : Nat → RaggedWirePartition d)
    (nets : Nat → (b : KBag 64 d) → (n : Nat) → ComparatorNetwork n)
    (v : Equiv.Perm (Fin (64 ^ d))) (t : Nat) (b : KBag 64 d) (hbd : b.l < d)
    (split : RaggedWireSplit ((P t).sets b))
    (hchild : ∀ j : Fin 64, (P (t + 1)).sets (b.child j.val j.isLt hbd) =
      raggedDownSet ((P t).sets b) split.up split.widths j.val)
    (cut : Nat) :
    (∑ j : Fin 64, (((raggedPlacement P nets v (t + 1)).regs
      (b.child j.val j.isLt hbd)).filter fun k => k.val < cut).card) +
      ((upSet ((P t).sets b) split.up).filter
        fun w => (raggedX P nets v (t + 1) w).val < cut).card =
      (((raggedPlacement P nets v t).regs b).filter fun k => k.val < cut).card := by
  simp only [raggedPlacement, Finset.filter_image,
    Finset.card_image_of_injective _ (raggedX_injective P nets v (t + 1)),
    Finset.card_image_of_injective _ (raggedX_injective P nets v t), hchild]
  rw [← ragged_stage_preserves_threshold_count P nets v t b cut]
  exact (Nat.add_comm _ _).trans
    (raggedWireSplit_threshold_conservation split
      (fun w => (raggedX P nets v (t + 1) w).val < cut))

/-- The source table in UB-23 supplies the cohort's physical child-set
equalities. Cardinal equality becomes set equality because the selected
parent port is physically included in that child register. -/
theorem candidate_expansion_child_sets {d t : Nat} (hd : 14 ≤ d)
    (ht0 : 1 ≤ t) (ht : t < candidateTerminalCutoff d) (P : RaggedWirePartition d)
    (H : CandidateActualCounts d t P) (b : KBag 64 d)
    (hb : candidateScheduledActive d t b) (hbottom : b.l = candidateOmega t)
    (hdepth : b.l + 2 < d) (j : Fin 64) :
    (candidateActualEvenStep hd t ht0 ht P H).sets (b.child j.val j.isLt (by omega)) =
      raggedDownSet (P.sets b) (candidateEvenFlowSplits hd t ht0 ht P H b).up
        ((candidateEvenFlowSplits hd t ht0 ht P H b).wireSplit (P.sets b)).widths j.val := by
  let F := candidateEvenFlowSplits hd t ht0 ht P H
  have hsub : raggedDownSet (P.sets b) (F b).up ((F b).wireSplit (P.sets b)).widths j.val ⊆
      (candidateActualEvenStep hd t ht0 ht P H).sets (b.child j.val j.isLt (by omega)) := by
    intro w hw
    change w ∈ routeRaggedWires P.sets (fun q => (F q).wireSplit (P.sets q))
      raggedTreeDestination (b.child j.val j.isLt (by omega))
    exact (mem_routeRaggedWires _ _ _ _ _).mpr
      ⟨b, some j, raggedTreeDestination_down b j (by omega), hw⟩
  apply (Finset.eq_of_subset_of_card_le hsub ?_).symm
  rw [candidate_expansion_child_exact hd ht0 ht P H b hb hbottom j hdepth]
  have hcard := raggedDownSet_card ((F b).wireSplit (P.sets b)) j.val j.isLt
  simp only [EvenFlowSplit.wireSplit_up, EvenFlowSplit.wireSplit_width] at hcard
  exact le_of_eq hcard.symm

/-- The bottom expansion cohort's threshold identity is instantiated on
the initialized candidate schedule. Its exact same chosen source flow is
used for all 64 children and every input/threshold. -/
theorem candidate_expansion_threshold_cohort {d t : Nat} (hd : 14 ≤ d)
    (ht0 : 1 ≤ t) (ht : t < candidateTerminalCutoff d)
    (nets : Nat → (b : KBag 64 d) → (n : Nat) → ComparatorNetwork n)
    (v : Equiv.Perm (Fin (64 ^ d))) (b : KBag 64 d)
    (hb : candidateScheduledActive d t b) (hbottom : b.l = candidateOmega t)
    (hdepth : b.l + 2 < d) (cut : Nat) :
    let P := candidateIntegerSchedule d hd
    let H := (candidate_integer_schedule_invariant d hd t ht0 ht.le).toCandidateActualCounts
    let F := candidateEvenFlowSplits hd t ht0 ht (P t) H
    (∑ j : Fin 64, (((raggedPlacement P nets v (t + 1)).regs
      (b.child j.val j.isLt (by omega))).filter fun k => k.val < cut).card) +
      ((upSet ((P t).sets b) (F b).up).filter
        fun w => (raggedX P nets v (t + 1) w).val < cut).card =
      (((raggedPlacement P nets v t).regs b).filter fun k => k.val < cut).card := by
  dsimp only
  let P := candidateIntegerSchedule d hd
  let H := (candidate_integer_schedule_invariant d hd t ht0 ht.le).toCandidateActualCounts
  let F := candidateEvenFlowSplits hd t ht0 ht (P t) H
  apply ragged_expansion_threshold_cohort P nets v t b (by omega)
    ((F b).wireSplit ((P t).sets b))
  intro j
  change (candidateIntegerSchedule d hd (t + 1)).sets _ = _
  rw [candidate_integer_schedule_step d hd t ht0 ht]
  exact candidate_expansion_child_sets hd ht0 ht (P t) H b hb hbottom hdepth j

end Tapered945
