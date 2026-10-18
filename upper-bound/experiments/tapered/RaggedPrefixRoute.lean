import ClippedPrefix
import FrontierIntegerSchedule

namespace Tapered945

open Chvatal

/-- Full-sort threshold count on the very same physical port cuts. In
particular the up-port consists of two disconnected intervals. -/
def clippedPortPrefix {n : Nat} {s : Finset (Fin n)}
    (split : RaggedWireSplit s) (H : Nat) : Option (Fin 64) → Int
  | none => Int.ofNat (min H (split.up / 2)) + Int.ofNat H -
      Int.ofNat (min H (s.card - split.up / 2))
  | some j => Int.ofNat (min H (slotHi split.up split.widths j.val)) -
      Int.ofNat (min H (slotLo split.up split.widths j.val))

def portPrefixCorrection {n : Nat} {s : Finset (Fin n)}
    (split : RaggedWireSplit s) (good : Fin n → Prop) [DecidablePred good] :
    Option (Fin 64) → Int
  | none => -(wirePrefixDeficit s good (split.up / 2) : Int) +
      wirePrefixDeficit s good (s.card - split.up / 2)
  | some j => (wirePrefixDeficit s good (slotLo split.up split.widths j.val) : Int) -
      wirePrefixDeficit s good (slotHi split.up split.widths j.val)

theorem raggedWirePort_prefix_eq_clipped {n : Nat} {s : Finset (Fin n)}
    (split : RaggedWireSplit s) (good : Fin n → Prop) [DecidablePred good]
    (port : Option (Fin 64)) :
    (((raggedWirePort split port).filter good).card : Int) =
      clippedPortPrefix split (s.filter good).card port +
        portPrefixCorrection split good port := by
  cases port with
  | none =>
    dsimp only [raggedWirePort, clippedPortPrefix, portPrefixCorrection]
    have h := wireUpCount_eq_clipped split good
    simp only [Int.ofNat_eq_natCast] at h ⊢
    omega
  | some j =>
    have hp := slotPrefix_mono split.widths (show j.val + 1 ≤ 64 by omega)
    rw [slotPrefix_succ] at hp
    have ht := split.conservation
    have h := wireBlockCount_eq_clipped s good
      (slotLo split.up split.widths j.val) (slotHi split.up split.widths j.val)
      (by dsimp [slotHi]; omega) (by dsimp [slotHi, slotLo]; omega)
    dsimp only [raggedWirePort, raggedDownSet, clippedPortPrefix, portPrefixCorrection]
    unfold wireBlockCount at h
    simp only [Int.ofNat_eq_natCast] at h ⊢
    omega

/-- Routing sums the actual threshold populations of the incoming ports.
Disjointness comes from physical ownership, without any key-rank premise. -/
theorem routeRaggedWires_filter_card
    {n : Nat} {B : Type*} [Fintype B] [DecidableEq B]
    (S : B → Finset (Fin n)) (splits : ∀ b, RaggedWireSplit (S b))
    (destination : B → Option (Fin 64) → B)
    (hsource : ∀ b c, b ≠ c → Disjoint (S b) (S c))
    (target : B) (good : Fin n → Prop) [DecidablePred good] :
    ((routeRaggedWires S splits destination target).filter good).card =
      ∑ x ∈ (Finset.univ : Finset (B × Option (Fin 64))).filter
        (fun x => destination x.1 x.2 = target),
          ((raggedWirePort (splits x.1) x.2).filter good).card := by
  classical
  let I := (Finset.univ : Finset (B × Option (Fin 64))).filter
    (fun x => destination x.1 x.2 = target)
  let port := fun x : B × Option (Fin 64) => (raggedWirePort (splits x.1) x.2).filter good
  have hroute : (routeRaggedWires S splits destination target).filter good = I.biUnion port := by
    ext w
    simp only [Finset.mem_filter, mem_routeRaggedWires, Finset.mem_biUnion,
      I, port, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨⟨b, p, hd, hw⟩, hg⟩
      exact ⟨(b, p), hd, hw, hg⟩
    · rintro ⟨⟨b, p⟩, hd, hw, hg⟩
      exact ⟨⟨b, p, hd, hw⟩, hg⟩
  have hdisj : (I : Set (B × Option (Fin 64))).PairwiseDisjoint port := by
    intro x hx y hy hxy
    apply Finset.disjoint_of_subset_left (Finset.filter_subset _ _)
    apply Finset.disjoint_of_subset_right (Finset.filter_subset _ _)
    by_cases hsrc : x.1 = y.1
    · have hport : x.2 ≠ y.2 := fun h => hxy (Prod.ext hsrc h)
      rw [← hsrc]
      exact raggedWirePort_disjoint (splits x.1) x.2 y.2 hport
    · exact Finset.disjoint_of_subset_left (raggedWirePort_subset _ _)
        (Finset.disjoint_of_subset_right (raggedWirePort_subset _ _) (hsource _ _ hsrc))
  rw [hroute, Finset.card_biUnion hdisj]

/-- All incoming nominal counts and shared endpoint corrections on one
coherent split table. This also covers roots and terminal self-routes. -/
theorem ragged_route_prefix_recurrence {d : Nat} (P : RaggedWirePartition d)
    (splits : ∀ b, RaggedWireSplit (P.sets b))
    (destination : KBag 64 d → Option (Fin 64) → KBag 64 d)
    (target : KBag 64 d) (good : Fin (64 ^ d) → Prop) [DecidablePred good] :
    ((((P.route splits destination).sets target).filter good).card : Int) =
      ∑ x ∈ (Finset.univ : Finset (KBag 64 d × Option (Fin 64))).filter
        (fun x => destination x.1 x.2 = target),
        (clippedPortPrefix (splits x.1) ((P.sets x.1).filter good).card x.2 +
          portPrefixCorrection (splits x.1) good x.2) := by
  have h := routeRaggedWires_filter_card P.sets splits destination P.disjoint target good
  change (((routeRaggedWires P.sets splits destination target).filter good).card : Int) = _
  rw [h, Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro x hx
  exact raggedWirePort_prefix_eq_clipped _ _ _

/-- Comparator stages preserve each source's key set even though the next
ownership partition may have different register sizes. -/
theorem ragged_stage_preserves_node_keys {d : Nat} (P : Nat → RaggedWirePartition d)
    (nets : Nat → (b : KBag 64 d) → (n : Nat) → ComparatorNetwork n)
    (v : Equiv.Perm (Fin (64 ^ d))) (t : Nat) (b : KBag 64 d) :
    ((P t).sets b).image (raggedX P nets v (t + 1)) =
      ((P t).sets b).image (raggedX P nets v t) := by
  apply Finset.eq_of_subset_of_card_le
  · intro k hk
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hk
    obtain ⟨c, rfl⟩ := exists_orderEmb_eq hw
    rw [raggedX, stageNet_exec_inside (P t).sets (P t).disjoint]
    obtain ⟨ρ, hρ⟩ := ComparatorNetwork.exec_eq_comp_perm
      (nets t b ((P t).sets b).card)
      (fun i => raggedX P nets v t (((P t).sets b).orderEmbOfFin rfl i))
    rw [hρ]
    exact Finset.mem_image_of_mem _ (Finset.orderEmbOfFin_mem _ rfl _)
  · rw [Finset.card_image_of_injective _ (raggedX_injective P nets v t),
      Finset.card_image_of_injective _ (raggedX_injective P nets v (t + 1))]

theorem ragged_stage_preserves_threshold_count {d : Nat} (P : Nat → RaggedWirePartition d)
    (nets : Nat → (b : KBag 64 d) → (n : Nat) → ComparatorNetwork n)
    (v : Equiv.Perm (Fin (64 ^ d))) (t : Nat) (b : KBag 64 d) (cut : Nat) :
    (((P t).sets b).filter fun w => (raggedX P nets v (t + 1) w).val < cut).card =
      (((P t).sets b).filter fun w => (raggedX P nets v t w).val < cut).card := by
  have h := congrArg (fun s : Finset (Fin (64 ^ d)) =>
    (s.filter fun k => k.val < cut).card) (ragged_stage_preserves_node_keys P nets v t b)
  simpa only [Finset.filter_image, Finset.card_image_of_injective _
    (raggedX_injective P nets v (t + 1)), Finset.card_image_of_injective _
    (raggedX_injective P nets v t)] using h

/-- Exact threshold recurrence for an actual routed comparator execution.
The nominal term uses the input threshold population; endpoint deficits
are measured on actual outputs of that same stage. -/
theorem ragged_execution_prefix_recurrence {d : Nat} (P : Nat → RaggedWirePartition d)
    (nets : Nat → (b : KBag 64 d) → (n : Nat) → ComparatorNetwork n)
    (v : Equiv.Perm (Fin (64 ^ d))) (t : Nat)
    (splits : ∀ b, RaggedWireSplit ((P t).sets b))
    (hrouted : P (t + 1) = (P t).route splits raggedTreeDestination)
    (target : KBag 64 d) (cut : Nat) :
    ((((raggedPlacement P nets v (t + 1)).regs target).filter
      fun k => k.val < cut).card : Int) =
      ∑ x ∈ (Finset.univ : Finset (KBag 64 d × Option (Fin 64))).filter
        (fun x => raggedTreeDestination x.1 x.2 = target),
        (clippedPortPrefix (splits x.1)
          ((((raggedPlacement P nets v t).regs x.1).filter fun k => k.val < cut).card) x.2 +
          portPrefixCorrection (splits x.1)
            (fun w => (raggedX P nets v (t + 1) w).val < cut) x.2) := by
  simp only [raggedPlacement, Finset.filter_image,
    Finset.card_image_of_injective _ (raggedX_injective P nets v (t + 1)),
    Finset.card_image_of_injective _ (raggedX_injective P nets v t)]
  rw [hrouted]
  rw [ragged_route_prefix_recurrence]
  apply Finset.sum_congr rfl
  intro x hx
  rw [ragged_stage_preserves_threshold_count P nets v t x.1 cut]

/-- UB-23's initialized schedule supplies the actual split table for the
rank recurrence at every stage, including bootstrap and the final meeting.
The table is chosen once, before the input or threshold. -/
theorem candidate_integer_prefix_recurrence (d : Nat) (hd : 14 ≤ d)
    (t : Nat) (ht : t < candidateTerminalCutoff d) :
    ∃ F : ∀ b : KBag 64 d,
        EvenFlowSplit ((candidateIntegerSchedule d hd t).sets b).card,
      candidateIntegerSchedule d hd (t + 1) =
        routeEvenFlows (candidateIntegerSchedule d hd t) F ∧
      ∀ (nets : Nat → (b : KBag 64 d) → (n : Nat) → ComparatorNetwork n)
        (v : Equiv.Perm (Fin (64 ^ d))) (target : KBag 64 d) (cut : Nat),
      ((((raggedPlacement (candidateIntegerSchedule d hd) nets v (t + 1)).regs target).filter
        fun k => k.val < cut).card : Int) =
        ∑ x ∈ (Finset.univ : Finset (KBag 64 d × Option (Fin 64))).filter
          (fun x => raggedTreeDestination x.1 x.2 = target),
          (clippedPortPrefix ((F x.1).wireSplit _)
            ((((raggedPlacement (candidateIntegerSchedule d hd) nets v t).regs x.1).filter
              fun k => k.val < cut).card) x.2 +
            portPrefixCorrection ((F x.1).wireSplit _)
              (fun w => (raggedX (candidateIntegerSchedule d hd) nets v (t + 1) w).val < cut) x.2) := by
  obtain ⟨F, hF⟩ := candidate_integer_schedule_routed d hd t ht
  refine ⟨F, hF, ?_⟩
  intro nets v target cut
  exact ragged_execution_prefix_recurrence (candidateIntegerSchedule d hd) nets v t
    (fun b => (F b).wireSplit _) hF target cut

end Tapered945
