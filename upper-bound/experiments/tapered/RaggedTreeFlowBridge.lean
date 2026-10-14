import RaggedIntegerSchedule
import RaggedTreeRoute

namespace Tapered945

open Chvatal

/-- Reindex an integer flow across equal occupancy and discrepancy values.
This is the transport step needed when the routed-count recurrence is
identified with a physical register cardinality. -/
def LocalIntegerFlow.reindex {d : Nat} {b : KBag 64 d}
    {C eta₁ eta₂ : Rat} {n m : Nat}
    (hn : n = m) (heta : eta₁ = eta₂)
    (F : LocalIntegerFlow b C eta₁ n) : LocalIntegerFlow b C eta₂ m := by
  cases hn
  cases heta
  exact F

/-- Realize one checked local integer flow as a physical split of an actual
register. -/
def localFlowWireSplit {d : Nat} {b : KBag 64 d} {C eta : Rat}
    {s : Finset (Fin (64 ^ d))}
    (F : LocalIntegerFlow b C eta s.card) : RaggedWireSplit s :=
  raggedWireSplitOfInteger s F.up F.blocks F.upEven F.upLe F.blockTotal

/-- A valid fallback split for inactive registers: keep every wire in the
first down-port. Active registers use their checked local integer flow. -/
def defaultRaggedWireSplit {n : Nat} (s : Finset (Fin n)) : RaggedWireSplit s := by
  classical
  let blocks : Fin 64 → Nat := fun j => if j = 0 then s.card else 0
  have hblocks : (∑ j : Fin 64, blocks j) = s.card := by
    classical
    simp [blocks]
  exact raggedWireSplitOfInteger s 0 blocks ⟨0, rfl⟩ (Nat.zero_le _) (by
    simpa using hblocks)

/-- Select the actual wire split from each active bag's chosen flow, and use
the fallback split outside the active domain. -/
noncomputable def activeFlowWireSplits {d : Nat}
    (P : RaggedWirePartition d) (Active : KBag 64 d → Prop)
    (C eta : KBag 64 d → Rat)
    (F : ∀ b, Active b →
      LocalIntegerFlow b (C b) (eta b) ((P.sets b).card)) :
    ∀ b, RaggedWireSplit (P.sets b) := by
  classical
  intro b
  exact if h : Active b then
    localFlowWireSplit (s := P.sets b) (F b h)
  else defaultRaggedWireSplit (P.sets b)

@[simp] theorem activeFlowWireSplits_up {d : Nat}
    (P : RaggedWirePartition d) (Active : KBag 64 d → Prop)
    (C eta : KBag 64 d → Rat)
    (F : ∀ b, Active b →
      LocalIntegerFlow b (C b) (eta b) ((P.sets b).card))
    (b : KBag 64 d) (hb : Active b) :
    (activeFlowWireSplits P Active C eta F b).up = (F b hb).up := by
  simp [activeFlowWireSplits, hb, localFlowWireSplit,
    raggedWireSplitOfInteger]

@[simp] theorem activeFlowWireSplits_width {d : Nat}
    (P : RaggedWirePartition d) (Active : KBag 64 d → Prop)
    (C eta : KBag 64 d → Rat)
    (F : ∀ b, Active b →
      LocalIntegerFlow b (C b) (eta b) ((P.sets b).card))
    (b : KBag 64 d) (hb : Active b) (j : Fin 64) :
    (activeFlowWireSplits P Active C eta F b).widths j.val =
      (F b hb).blocks j := by
  simp [activeFlowWireSplits, hb, localFlowWireSplit,
    raggedWireSplitOfInteger]

@[simp] theorem localFlowWireSplit_down_card {d : Nat} {b : KBag 64 d}
    {C eta : Rat} {s : Finset (Fin (64 ^ d))}
    (F : LocalIntegerFlow b C eta s.card) (j : Fin 64) :
    (raggedWirePort (localFlowWireSplit F) (some j)).card = F.blocks j := by
  rw [raggedWirePort_card]
  simp [localFlowWireSplit, raggedWireSplitOfInteger]

@[simp] theorem localFlowWireSplit_up_card {d : Nat} {b : KBag 64 d}
    {C eta : Rat} {s : Finset (Fin (64 ^ d))}
    (F : LocalIntegerFlow b C eta s.card) :
    (raggedWirePort (localFlowWireSplit F) none).card = F.up := by
  rw [raggedWirePort_card]
  rfl

/-- The ordinary interior recurrence is exactly the sum of its physically
routed integer-flow contributions: the parent sends slot `j`, and every
grandchild sends its up-fringe to the middle bag. The tree-route lemmas verify
those destinations, while this equation verifies their total numerical mass. -/
theorem routedChildCount_eq_physical_port_sum {d : Nat}
    {Active : KBag 64 d → Prop} {C eta : KBag 64 d → Rat}
    (P : RaggedWirePartition d)
    (F : ∀ b, Active b →
      LocalIntegerFlow b (C b) (eta b) ((P.sets b).card))
    (b : KBag 64 d) (hb : Active b) (j : Fin 64)
    (hdepth : b.l + 2 < d)
    (hparent : b.l < d)
    (hchild : (b.child j.val j.isLt hparent).l < d)
    (hgcActive : ∀ l : Fin 64,
      Active ((b.child j.val j.isLt hparent).child l.val l.isLt hchild)) :
    routedChildCount F b hb j hdepth hgcActive =
      (raggedWirePort
        (localFlowWireSplit (s := P.sets b) (F b hb)) (some j)).card +
        ∑ l : Fin 64,
          (raggedWirePort
            (localFlowWireSplit (s := P.sets
              ((b.child j.val j.isLt hparent).child l.val l.isLt hchild))
              (F ((b.child j.val j.isLt hparent).child l.val l.isLt
                hchild) (hgcActive l))) none).card := by
  simp only [routedChildCount, localFlowWireSplit_down_card,
    localFlowWireSplit_up_card]

/-- Each summand in the previous recurrence is assigned to its intended
recipient by the canonical tree route. This is the concrete port-to-address
bridge used when installing the local flow table into a wire partition. -/
theorem routedChildCount_port_destinations {d : Nat}
    (b : KBag 64 d) (j : Fin 64)
    (_hdepth : b.l + 2 < d)
    (hparent : b.l < d)
    (hchild : (b.child j.val j.isLt hparent).l < d) :
    raggedTreeDestination b (some j) = b.child j.val j.isLt hparent ∧
      ∀ l : Fin 64,
        raggedTreeDestination
          ((b.child j.val j.isLt hparent).child l.val l.isLt hchild) none =
            b.child j.val j.isLt hparent := by
  constructor
  · exact raggedTreeDestination_down b j hparent
  · intro l
    exact raggedTreeDestination_child_up (b.child j.val j.isLt hparent) hchild l

/-- Gluing the physical route-count theorem to the integer recurrence. The two
matching hypotheses say that the global split uses the local flow's selected
parent block and the grandchild up-flows. Under precisely these interfaces,
the actual routed register cardinality equals `routedChildCount`. -/
theorem actual_routedChildCount_eq {d : Nat}
    {Active : KBag 64 d → Prop} {C eta : KBag 64 d → Rat}
    (P : RaggedWirePartition d)
    (splits : ∀ q, RaggedWireSplit (P.sets q))
    (F : ∀ q, Active q →
      LocalIntegerFlow q (C q) (eta q) ((P.sets q).card))
    (b : KBag 64 d) (hb : Active b) (j : Fin 64)
    (hdepth : b.l + 2 < d)
    (hparent : b.l < d)
    (hchild : (b.child j.val j.isLt hparent).l < d)
    (hgcActive : ∀ l : Fin 64,
      Active ((b.child j.val j.isLt hparent).child l.val l.isLt hchild))
    (hparentWidth : (splits b).widths j.val = (F b hb).blocks j)
    (hgrandUp : ∀ l : Fin 64,
      (splits ((b.child j.val j.isLt hparent).child l.val l.isLt hchild)).up =
        (F ((b.child j.val j.isLt hparent).child l.val l.isLt hchild)
          (hgcActive l)).up) :
    ((P.route splits raggedTreeDestination).sets
      (b.child j.val j.isLt hparent)).card =
        routedChildCount F b hb j hdepth hgcActive := by
  change (routeRaggedWires P.sets splits raggedTreeDestination
    (b.child j.val j.isLt hparent)).card = _
  have hindex : (b.child j.val j.isLt hparent).x % 64 = j.val := by
    simp [KBag.child, Nat.add_mod, Nat.mod_eq_of_lt j.isLt]
  rw [routeRaggedWires_card_eq_tree_recurrence P splits
    (b.child j.val j.isLt hparent) (by change 1 ≤ b.l + 1; omega)
    (by change b.l + 1 < d; omega)]
  have hparentEq := KBag.child_parent b j.val j.isLt hparent (by norm_num)
  rw [hparentEq]
  rw [hindex, hparentWidth]
  unfold routedChildCount
  rw [Finset.sum_congr rfl]
  intro l hl
  exact hgrandUp l

/-- Local flow witnesses transport across the exact routed-cardinality
identity, including the signed discrepancy parameter. -/
def LocalIntegerFlow.transport_routed_count {d : Nat}
    {b : KBag 64 d} {C : Rat} {target : Rat}
    {actual routed : Nat} (hactual : actual = routed)
    (F : LocalIntegerFlow b C ((routed : Rat) - target) routed) :
      LocalIntegerFlow b C ((actual : Rat) - target) actual := by
  cases hactual
  exact F

/-- With the physical split compatibility conditions, a scheduled ordinary
child receives an integer-flow witness indexed by its actual next-stage wire
set. This is the composable interior step; boundary rules remain external. -/
theorem candidate_interior_actual_child_flow_exists {d : Nat}
    (hd : 14 ≤ d) (P : RaggedWirePartition d)
    (t : Nat) (ht : t < candidateTf d) (b : KBag 64 d)
    (hb : candidateScheduledActive d t b)
    (hbottom : b.l + 2 ≤ candidateOmega t)
    (hdepth : b.l + 2 < d)
    (eta : KBag 64 d → Rat)
    (F : ∀ q, candidateScheduledActive d t q →
      LocalIntegerFlow q (candidateReferenceCapacity d q.l t) (eta q)
        ((P.sets q).card))
    (splits : ∀ q, RaggedWireSplit (P.sets q))
    (Pnext : RaggedWirePartition d)
    (hnext : Pnext = P.route splits raggedTreeDestination)
    (hwidth : ∀ q (hq : candidateScheduledActive d t q) (k : Fin 64),
      (splits q).widths k.val = (F q hq).blocks k)
    (hup : ∀ q (hq : candidateScheduledActive d t q),
      (splits q).up = (F q hq).up) :
    ∀ j : Fin 64,
      Nonempty (LocalIntegerFlow
        (b.child j.val j.isLt (by omega))
        (candidateReferenceCapacity d (b.l + 1) (t + 1))
        (↑(Pnext.sets (b.child j.val j.isLt (by omega))).card -
          (1 - 1 / cap) * candidateReferenceCapacity d (b.l + 1) (t + 1))
        ((Pnext.sets (b.child j.val j.isLt (by omega))).card)) := by
  classical
  intro j
  let hp : b.l < d := by omega
  have hc : (b.child j.val j.isLt hp).l < d := by
    change b.l + 1 < d
    omega
  have hgc : ∀ l : Fin 64,
      candidateScheduledActive d t
        ((b.child j.val j.isLt hp).child l.val l.isLt hc) := by
    intro l
    exact (candidate_interior_active_successors d hd t ht b hb hbottom).2 j l
  have hpw := hwidth b hb j
  have hgu : ∀ l : Fin 64,
      (splits ((b.child j.val j.isLt hp).child l.val l.isLt hc)).up =
        (F ((b.child j.val j.isLt hp).child l.val l.isLt hc) (hgc l)).up := by
    intro l
    exact hup _ (hgc l)
  have hcard := actual_routedChildCount_eq P splits F b hb j hdepth hp hc
    hgc hpw hgu
  have hphysical : (Pnext.sets (b.child j.val j.isLt hp)).card =
      routedChildCount F b hb j hdepth hgc := by
    rw [hnext]
    exact hcard
  have hlocal := candidate_interior_child_flow_exists hd t ht b hb hbottom
    hdepth eta (fun q => (P.sets q).card) F j
  rcases hlocal with ⟨G⟩
  exact ⟨LocalIntegerFlow.transport_routed_count hphysical G⟩

/-- A usable ordinary-step interface: current active flows determine one
coherent split for every register (inactive registers use the fixed fallback),
and every scheduled interior child gets a next flow on the supplied routed
partition. -/
theorem candidate_interior_actual_step {d : Nat}
    (hd : 14 ≤ d) (P Pnext : RaggedWirePartition d)
    (t : Nat) (ht : t < candidateTf d)
    (eta : KBag 64 d → Rat)
    (F : ∀ q, candidateScheduledActive d t q →
      LocalIntegerFlow q (candidateReferenceCapacity d q.l t) (eta q)
        ((P.sets q).card))
    (hnext : Pnext = P.route
      (activeFlowWireSplits P (candidateScheduledActive d t)
        (fun q => candidateReferenceCapacity d q.l t) eta F)
      raggedTreeDestination)
    (b : KBag 64 d) (hb : candidateScheduledActive d t b)
    (hbottom : b.l + 2 ≤ candidateOmega t)
    (hdepth : b.l + 2 < d) :
    ∀ j : Fin 64,
      Nonempty (LocalIntegerFlow
        (b.child j.val j.isLt (by omega))
        (candidateReferenceCapacity d (b.l + 1) (t + 1))
        (↑(Pnext.sets (b.child j.val j.isLt (by omega))).card -
          (1 - 1 / cap) * candidateReferenceCapacity d (b.l + 1) (t + 1))
        ((Pnext.sets (b.child j.val j.isLt (by omega))).card)) := by
  apply candidate_interior_actual_child_flow_exists hd P t ht b hb hbottom
    hdepth eta F
    (activeFlowWireSplits P (candidateScheduledActive d t)
      (fun q => candidateReferenceCapacity d q.l t) eta F)
    Pnext hnext
  · intro q hq k
    exact activeFlowWireSplits_width P (candidateScheduledActive d t)
      (fun q => candidateReferenceCapacity d q.l t) eta F q hq k
  · intro q hq
    exact activeFlowWireSplits_up P (candidateScheduledActive d t)
      (fun q => candidateReferenceCapacity d q.l t) eta F q hq

/-- Addresses reached by the ordinary interior rule at stage `t`. The two
depth conditions explicitly exclude bags whose grandchildren hit the moving
bottom frontier or the terminal boundary. -/
def candidateInteriorChildAddress (d t : Nat) (q : KBag 64 d) : Prop :=
  ∃ b, candidateScheduledActive d t b ∧
    b.l + 2 ≤ candidateOmega t ∧ ∃ hdepth : b.l + 2 < d,
    ∃ j : Fin 64, q = b.child j.val j.isLt (by omega)

/-- Every scheduled bag at the next time is either produced by an ordinary
interior parent or lies on one of the two moving frontiers. This isolates the
exact domain where the interior table must be supplemented by boundary rules. -/
theorem candidate_next_active_interior_or_frontier {d : Nat}
    (hd : 14 ≤ d) (t : Nat) (ht : t < candidateTf d)
    (q : KBag 64 d) (hq : candidateScheduledActive d (t + 1) q) :
    candidateInteriorChildAddress d t q ∨
      (q.l + 1 = candidateAlpha d t ∧
        candidateAlpha d t = candidateAlpha d (t + 1) + 1) ∨
      (q.l = candidateOmega t + 1 ∧
        candidateOmega (t + 1) = candidateOmega t + 1) := by
  rcases hq with ⟨⟨haNext, hoNext⟩, hparNext⟩
  have haMove := candidate_alpha_unit_motion d hd t ht
  have hoMove := candidate_omega_unit_motion t
  have haPar := candidate_alpha_parity d t
  have hoPar := candidate_omega_parity t
  have hqlo : candidateAlpha d t - 1 ≤ q.l := by omega
  have hqhi : q.l ≤ candidateOmega t + 1 := by omega
  by_cases hlow : candidateAlpha d t + 1 ≤ q.l
  · by_cases hhigh : q.l + 1 ≤ candidateOmega t
    · let b := q.parent (by norm_num : 1 ≤ 64)
      have hbdepth : b.l < d := by
        change q.l - 1 < d
        have hωd := candidate_omega_le_depth_minus_five d hd t (by omega)
        omega
      have hparentActive : candidateScheduledActive d t b := by
        refine ⟨⟨?_, ?_⟩, ?_⟩
        · change candidateAlpha d t ≤ q.l - 1
          omega
        · change q.l - 1 ≤ candidateOmega t
          omega
        · change (q.l - 1) % 2 = t % 2
          have := hparNext
          omega
      have hbottom : b.l + 2 ≤ candidateOmega t := by
        change q.l - 1 + 2 ≤ candidateOmega t
        omega
      have hdepth : b.l + 2 < d := by
        change q.l - 1 + 2 < d
        have hωd := candidate_omega_le_depth_minus_five d hd t (by omega)
        omega
      have hparentChild := Chvatal.KBag.parent_child q (by omega) (by norm_num)
        hbdepth
      refine Or.inl ⟨b, hparentActive, hbottom, hdepth, ?_⟩
      refine ⟨⟨q.x % 64, Nat.mod_lt _ (by norm_num)⟩, ?_⟩
      simpa [b] using hparentChild.symm
    · right
      right
      have hqparity_ne : q.l % 2 ≠ candidateOmega t % 2 := by omega
      constructor <;> omega
  · right
    left
    have hqparity_ne : q.l % 2 ≠ candidateAlpha d t % 2 := by omega
    constructor <;> omega

def candidateActualNextFlowError {d : Nat} (Pnext : RaggedWirePartition d)
    (t : Nat) (q : KBag 64 d) : Rat :=
  ((Pnext.sets q).card : Rat) -
    (1 - 1 / cap) * candidateReferenceCapacity d q.l (t + 1)

/-- Every address generated by an ordinary interior parent has a local flow
whose count is the actual routed-register size. This yields a genuine
address-indexed next table on the interior-child domain; frontier addresses
are intentionally excluded. -/
theorem candidate_interior_actual_flow_nonempty {d : Nat}
    (hd : 14 ≤ d) (P Pnext : RaggedWirePartition d)
    (t : Nat) (ht : t < candidateTf d)
    (eta : KBag 64 d → Rat)
    (F : ∀ q, candidateScheduledActive d t q →
      LocalIntegerFlow q (candidateReferenceCapacity d q.l t) (eta q)
        ((P.sets q).card))
    (hnext : Pnext = P.route
      (activeFlowWireSplits P (candidateScheduledActive d t)
        (fun q => candidateReferenceCapacity d q.l t) eta F)
      raggedTreeDestination)
    (q : KBag 64 d) (hq : candidateInteriorChildAddress d t q) :
    Nonempty (LocalIntegerFlow q (candidateReferenceCapacity d q.l (t + 1))
      (candidateActualNextFlowError Pnext t q) ((Pnext.sets q).card)) := by
  rcases hq with ⟨b, hb, hbottom, hdepth, j, hq⟩
  subst q
  have hstep := candidate_interior_actual_step hd P Pnext t ht eta F hnext
    b hb hbottom hdepth j
  change Nonempty (LocalIntegerFlow
    (b.child j.val j.isLt (by omega))
    (candidateReferenceCapacity d (b.l + 1) (t + 1))
    (↑(Pnext.sets (b.child j.val j.isLt (by omega))).card -
      (1 - 1 / cap) * candidateReferenceCapacity d (b.l + 1) (t + 1))
    ((Pnext.sets (b.child j.val j.isLt (by omega))).card))
  exact hstep

/-- Choose one flow per interior-child address, so repeated descriptions of
the same address cannot create incompatible next-stage choices. -/
noncomputable def chooseCandidateInteriorActualFlows {d : Nat}
    (hd : 14 ≤ d) (P Pnext : RaggedWirePartition d)
    (t : Nat) (ht : t < candidateTf d)
    (eta : KBag 64 d → Rat)
    (F : ∀ q, candidateScheduledActive d t q →
      LocalIntegerFlow q (candidateReferenceCapacity d q.l t) (eta q)
        ((P.sets q).card))
    (hnext : Pnext = P.route
      (activeFlowWireSplits P (candidateScheduledActive d t)
        (fun q => candidateReferenceCapacity d q.l t) eta F)
      raggedTreeDestination) :
    ∀ q, candidateInteriorChildAddress d t q →
      LocalIntegerFlow q (candidateReferenceCapacity d q.l (t + 1))
        (candidateActualNextFlowError Pnext t q) ((Pnext.sets q).card) := by
  classical
  intro q hq
  exact Classical.choice (candidate_interior_actual_flow_nonempty
    hd P Pnext t ht eta F hnext q hq)

end Tapered945
