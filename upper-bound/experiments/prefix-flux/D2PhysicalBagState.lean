import D2StaticWireSets

/-!
The Python `flow_dag.py` model represents a D2 sender as its occupied native
interval with the occupied intervals of its children removed. This file makes
that address set and its ordered-run representation explicit for a Lean flow
tree. The fit hypothesis is kept visible: proving it for every candidate
snapshot is part of the schedule-to-physical bridge.
-/

namespace Chvatal.D2PhysicalBagState

open Chvatal
open Chvatal.D2Reserve
open Chvatal.D2StaticWireSets
open Chvatal.D2OrdinaryRankRouting

/-- The eight static child holes determined by one flow-tree node. A saturated
child contributes an empty hole, placed at the appropriate boundary by
`d2EightChildHole`. -/
def d2FlowNodeStaticHoles {h : Nat} (base width low high : Nat)
    (children : Fin 8 -> D2FlowTree h) : List (Nat × Nat) :=
  staticHoleList 8
    (fun j => (d2EightChildHole base width low high
      (fun k => d2FlowTreeRootDeficit (children k))
      (fun k => (d2FlowTreeRootData (children k)).2.1)
      (fun k => (d2FlowTreeRootData (children k)).2.2) j).1)
    (fun j => (d2EightChildHole base width low high
      (fun k => d2FlowTreeRootDeficit (children k))
      (fun k => (d2FlowTreeRootData (children k)).2.1)
      (fun k => (d2FlowTreeRootData (children k)).2.2) j).2)

/-- For a non-saturated child, its static hole is exactly its occupied
native interval in the parent's address coordinates. -/
theorem d2FlowNodeChildHole_eq_interval
    {h : Nat} (base width low high : Nat)
    (children : Fin 8 -> D2FlowTree h) (j : Fin 8)
    (hchild : d2FlowTreeRootDeficit (children j) ≠ width) :
    d2EightChildHole base width low high
      (fun k => d2FlowTreeRootDeficit (children k))
      (fun k => (d2FlowTreeRootData (children k)).2.1)
      (fun k => (d2FlowTreeRootData (children k)).2.2) j =
      (base + j.val * width + (d2FlowTreeRootData (children j)).2.1,
        base + (j.val + 1) * width -
          (d2FlowTreeRootData (children j)).2.2) := by
  simp [d2EightChildHole, hchild]

/-- The physical wires assigned to a non-saturated node: its native occupied
interval, excluding the occupied intervals reserved for its children. -/
def d2FlowNodeStaticBag {n h : Nat} (base width G low high : Nat)
    (children : Fin 8 -> D2FlowTree h) : Finset (Fin n) :=
  if G = 8 * width then ∅ else
    staticWireInterval (base + low) (base + 8 * width - high) \
      staticHoleUnion (d2FlowNodeStaticHoles base width low high children)

/-- The ordered address runs of a flow node's sender bag. -/
def d2FlowNodeStaticRuns {n h : Nat} (base width G low high : Nat)
    (children : Fin 8 -> D2FlowTree h) : List (Finset (Fin n)) :=
  if G = 8 * width then [] else
    staticGapRuns (base + low)
      (d2FlowNodeStaticHoles base width low high children)
      (base + 8 * width - high)

/-- Recursive geometric well-formedness of a flow tree: at each node, the
child occupied intervals fit inside the node's occupied interval. -/
def d2FlowTreeStaticFits (scale : Nat) : {h : Nat} ->
    D2FlowTree h -> Prop
  | 0, .leaf _ _ _ => True
  | h + 1, .node _ low high children =>
      StaticHolesFit low
        (d2FlowNodeStaticHoles 0 (scale * 8 ^ h) low high children)
        (8 * (scale * 8 ^ h) - high) ∧
      ∀ j, d2FlowTreeStaticFits scale (children j)

/-- The full native child subtrees occupy their own slots, so their empty
holes fit exactly across the parent interval. -/
theorem d2FlowFullChildren_static_holes_fit (scale h : Nat) :
    StaticHolesFit 0
      (d2FlowNodeStaticHoles 0 (scale * 8 ^ h) 0 0
        (fun _ => d2FlowTreeFull scale h))
      (8 * (scale * 8 ^ h)) := by
  let width := scale * 8 ^ h
  let children : Fin 8 -> D2FlowTree h := fun _ => d2FlowTreeFull scale h
  let sizes : Fin 8 -> Nat := fun j =>
    d2FlowTreeRootDeficit (children j)
  let lows : Fin 8 -> Nat := fun j =>
    (d2FlowTreeRootData (children j)).2.1
  let highs : Fin 8 -> Nat := fun j =>
    (d2FlowTreeRootData (children j)).2.2
  have hsize : ∀ j, sizes j = width := by
    intro j
    simp [sizes, children, width, d2FlowTreeFull_root_deficit]
  have hlow : ∀ j, lows j = 0 := by
    intro j
    cases h <;> simp [lows, children, d2FlowTreeFull, d2FlowTreeRootData]
  have hhigh : ∀ j, highs j = 0 := by
    intro j
    cases h <;> simp [highs, children, d2FlowTreeFull, d2FlowTreeRootData]
  have hslots : ∀ j,
      0 + j.val * width ≤
          (d2EightChildHole 0 width 0 0 sizes lows highs j).1 ∧
        (d2EightChildHole 0 width 0 0 sizes lows highs j).1 ≤
          (d2EightChildHole 0 width 0 0 sizes lows highs j).2 ∧
        (d2EightChildHole 0 width 0 0 sizes lows highs j).2 ≤
          0 + (j.val + 1) * width := by
    intro j
    exact d2EightChildHole_within_slot sizes lows highs (by omega) (by omega)
      j (by rw [hsize j]) (by intro hlt; rw [hsize j] at hlt; omega)
  have hfirst : 0 ≤
      (d2EightChildHole 0 width 0 0 sizes lows highs
        ⟨0, by omega⟩).1 := by
    simp [d2EightChildHole, hsize, hlow, hhigh]
  have hlast :
      (d2EightChildHole 0 width 0 0 sizes lows highs
        ⟨7, by omega⟩).2 ≤ 8 * width := by
    simp [d2EightChildHole, hsize, hlow, hhigh]
  have hfit := d2EightChildHolesFit
    (fun j => (d2EightChildHole 0 width 0 0 sizes lows highs j).1)
    (fun j => (d2EightChildHole 0 width 0 0 sizes lows highs j).2)
    (Nat.zero_le width) (Nat.zero_le width)
    (by simpa using Nat.zero_le (8 * width))
    hslots hfirst (by simpa using hlast)
  simpa [children, sizes, lows, highs, width, d2FlowNodeStaticHoles] using hfit

/-- The all-full D2 tree has a valid nested interval representation at every
depth. -/
theorem d2FlowTreeFull_static_fits (scale h : Nat) :
    d2FlowTreeStaticFits scale (d2FlowTreeFull scale h) := by
  induction h with
  | zero => trivial
  | succ h ih =>
      simp only [d2FlowTreeFull, d2FlowTreeStaticFits]
      constructor
      · simpa [Nat.pow_succ, mul_assoc, mul_left_comm, mul_comm] using
          d2FlowFullChildren_static_holes_fit scale h
      · intro j
        exact ih

/-- Initial candidate state satisfies the nested static-bag geometry; this
is the base case for a future all-stage preservation theorem. -/
theorem d2FlowTreeInitial_static_fits (scale h : Nat) :
    d2FlowTreeStaticFits scale (d2FlowTreeInitial scale h) := by
  cases h with
  | zero => trivial
  | succ h =>
      simp only [d2FlowTreeInitial, d2FlowTreeStaticFits]
      constructor
      · simpa [Nat.pow_succ, mul_assoc, mul_left_comm, mul_comm] using
          d2FlowFullChildren_static_holes_fit scale h
      · intro j
        exact d2FlowTreeFull_static_fits scale h

/-- An active ordinary update sets each child's root data to the corresponding
cut tuple. This exposes the exact link between the abstract cut contract and
the post-stage static-hole geometry. -/
theorem d2FlowStage_regular_child_root_data {active : Nat -> Bool}
    {role : Nat -> D2Role} {quota : Nat -> D2Role -> Nat}
    {h i G low high : Nat} (children : Fin 8 -> D2FlowTree h)
    (ha : active i = true)
    (hr : role i = .topRise ∨ role i = .mid ∨ role i = .botDesc)
    (j : Fin 8) :
    d2FlowTreeRootData
      (d2FlowTreeChild (d2FlowStage active role quota (h + 1) i
        (.node G low high children)) j) =
      d2FlowCutChild
        (d2FlowPosition (fun k => d2FlowTreeRootDeficit (children k)) j)
        (d2FlowTreeRootDeficit (children j))
        (low + quota i (role i) / 2)
        (d2FlowTotal (fun k => d2FlowTreeRootDeficit (children k)) -
          high - quota i (role i) / 2) := by
  rw [d2FlowStage_regular_child_setroot children ha hr j]
  exact d2FlowTreeRootData_setRoot _ _ _ _

/-- The two notations for the new right front agree under the ordinary
stage-input quota and balance bounds. -/
theorem d2FlowStage_right_front_subtraction_eq {scale h i G low high : Nat}
    {active : Nat -> Bool} {role : Nat -> D2Role}
    {quota : Nat -> D2Role -> Nat} {cap : Nat -> Nat}
    (children : Fin 8 -> D2FlowTree h)
    (hinputs : d2FlowStageInvInputs scale active role quota cap i
      (.node G low high children)) (ha : active i = true)
    (hr : role i = .topRise ∨ role i = .mid ∨ role i = .botDesc) :
    d2FlowTotal (fun k => d2FlowTreeRootDeficit (children k)) - high -
        quota i (role i) / 2 =
      d2FlowTotal (fun k => d2FlowTreeRootDeficit (children k)) -
        (high + quota i (role i) / 2) := by
  have hstage := hinputs.2
  simp only [ha, if_true] at hstage
  rcases hr with hrole | hrole | hrole <;>
    simp only [hrole] at hstage <;>
    rcases hstage with ⟨hbalance, hG, hquotacap, hquota, heven,
      hleft, hright⟩ <;>
    simp only [d2FlowTotal] at hquota ⊢ <;> omega

/-- An active ordinary update leaves the new child holes inside its updated
parent fronts. This combines the reserve-derived subtraction identity with
the cut-based static-hole fit. -/
theorem d2FlowStage_active_ordinary_static_fit
    {scale h i G low high : Nat} {active : Nat -> Bool}
    {role : Nat -> D2Role} {quota : Nat -> D2Role -> Nat}
    {cap : Nat -> Nat}
    (children : Fin 8 -> D2FlowTree h)
    (htree : d2FlowTreeInv scale (.node G low high children))
    (hinputs : d2FlowStageInvInputs scale active role quota
      cap i (.node G low high children))
    (ha : active i = true)
    (hr : role i = .topRise ∨ role i = .mid ∨ role i = .botDesc) :
    StaticHolesFit (low + quota i (role i) / 2)
      (d2FlowNodeStaticHoles 0 (scale * 8 ^ h)
        (low + quota i (role i) / 2)
        (high + quota i (role i) / 2)
        (fun j => d2FlowTreeChild
          (d2FlowStage active role quota (h + 1) i
            (.node G low high children)) j))
      (8 * (scale * 8 ^ h) - (high + quota i (role i) / 2)) := by
  cases hrole : role i with
  | topDesc => simp [hrole] at hr
  | botRise => simp [hrole] at hr
  | topRise | mid | botDesc =>
      have hfit := d2FlowStageInvInputs_static_holes
        (scale := scale) (i := i) (base := 0) (G := G)
        (low := low) (high := high) children htree hinputs ha hr
      simp only [hrole] at hfit
      have hright := d2FlowStage_right_front_subtraction_eq
        (scale := scale) (h := h) (i := i) (G := G) (low := low)
        (high := high) (active := active) (role := role) (quota := quota)
        (cap := cap) children hinputs ha hr
      simp only [hrole] at hright
      have hdata (j : Fin 8) :=
        d2FlowStage_regular_child_root_data (h := h) (i := i)
          (G := G) (low := low) (high := high) (quota := quota)
          children ha hr j
      simp only [hrole] at hdata ⊢
      have hdef (j : Fin 8) :
          d2FlowTreeRootDeficit
            (d2FlowTreeChild (d2FlowStage active role quota (h + 1) i
              (.node G low high children)) j) =
          (d2FlowCutChild
            (d2FlowPosition (fun k => d2FlowTreeRootDeficit (children k)) j)
            (d2FlowTreeRootDeficit (children j))
            (low + quota i (role i) / 2)
            (d2FlowTotal (fun k => d2FlowTreeRootDeficit (children k)) -
              (high + quota i (role i) / 2))).1 := by
        simp only [hrole]
        rw [← d2FlowTreeRootData_fst_eq_deficit, hdata, hright]
      simpa [hrole, d2FlowNodeStaticHoles, hdef, hdata, hright] using hfit

/-- A non-saturated node's sender bag is exactly the union of its ordered
static runs; the same fit condition proves those runs are address-ordered. -/
theorem d2FlowNodeStaticBag_eq_runs
    {n h : Nat} {base width G low high : Nat}
    (children : Fin 8 -> D2FlowTree h)
    (hnonsat : G ≠ 8 * width)
    (hfit : StaticHolesFit (base + low)
      (d2FlowNodeStaticHoles base width low high children)
      (base + 8 * width - high)) :
    orderedRunUnion (d2FlowNodeStaticRuns (n := n) base width G low high children) =
        d2FlowNodeStaticBag (n := n) base width G low high children ∧
      OrderedRuns (n := n)
        (d2FlowNodeStaticRuns (n := n) base width G low high children) := by
  constructor
  · simpa [d2FlowNodeStaticRuns, d2FlowNodeStaticBag, hnonsat] using
      staticGapRuns_union_eq_complement (n := n) (base + low)
        (base + 8 * width - high)
        (d2FlowNodeStaticHoles base width low high children) hfit

  · simpa [d2FlowNodeStaticRuns, hnonsat] using
      staticGapRuns_ordered (n := n) (base + low)
        (base + 8 * width - high)
        (d2FlowNodeStaticHoles base width low high children) hfit

/-- A child-tagged rank port of the physical sender bag is exactly the
corresponding rank slice of its ordered static address runs. -/
theorem d2FlowNodeStaticBag_child_port_eq_run_slice
    {n h ports : Nat} {base width G low high : Nat}
    (children : Fin 8 → D2FlowTree h) (hnonsat : G ≠ 8 * width)
    (hfit : StaticHolesFit (base + low)
      (d2FlowNodeStaticHoles base width low high children)
      (base + 8 * width - high))
    (boundary : Nat → Nat) (left rightStart : Nat) (j : Fin ports) :
    destinationPiece (ports := ports)
        (d2FlowNodeStaticBag (n := n) base width G low high children)
        boundary left rightStart (some j) =
      orderedRunSlice
        (d2FlowNodeStaticRuns (n := n) base width G low high children)
        (left + boundary j.val) (left + boundary (j.val + 1)) := by
  have hrep := d2FlowNodeStaticBag_eq_runs (n := n) children hnonsat hfit
  simp only [destinationPiece]
  rw [← hrep.1]
  exact blockOf_orderedRuns (n := n) _ hrep.2 _ _

/-- The two parent end ports of the physical sender bag are the corresponding
left and right slices of its ordered static address runs. -/
theorem d2FlowNodeStaticBag_parent_ports_eq_run_slices
    {n h ports : Nat} {base width G low high : Nat}
    (children : Fin 8 → D2FlowTree h) (hnonsat : G ≠ 8 * width)
    (hfit : StaticHolesFit (base + low)
      (d2FlowNodeStaticHoles base width low high children)
      (base + 8 * width - high))
    (boundary : Nat → Nat) (left rightStart : Nat) :
    destinationPiece (ports := ports)
        (d2FlowNodeStaticBag (n := n) base width G low high children)
        boundary left rightStart none =
      orderedRunSlice
          (d2FlowNodeStaticRuns (n := n) base width G low high children)
          0 left ∪
        orderedRunSlice
          (d2FlowNodeStaticRuns (n := n) base width G low high children)
          rightStart
          (d2FlowNodeStaticBag (n := n) base width G low high children).card := by
  have hrep := d2FlowNodeStaticBag_eq_runs (n := n) children hnonsat hfit
  simp only [destinationPiece]
  rw [← hrep.1]
  rw [blockOf_orderedRuns (n := n) _ hrep.2]
  rw [blockOf_orderedRuns (n := n) _ hrep.2]

/-- A concrete child port intersected with a physical cell is exactly its
per-run address fragments. -/
theorem d2FlowNodeStaticBag_child_port_inter_cell
    {n h ports : Nat} {base width G low high : Nat}
    (children : Fin 8 → D2FlowTree h) (hnonsat : G ≠ 8 * width)
    (hfit : StaticHolesFit (base + low)
      (d2FlowNodeStaticHoles base width low high children)
      (base + 8 * width - high))
    (boundary : Nat → Nat) (left rightStart : Nat) (j : Fin ports)
    (cellLo cellHi : Nat) :
    (destinationPiece (ports := ports)
        (d2FlowNodeStaticBag (n := n) base width G low high children)
        boundary left rightStart (some j)) ∩
        staticWireInterval cellLo cellHi =
      orderedRunSliceInCell
        (d2FlowNodeStaticRuns (n := n) base width G low high children)
        (left + boundary j.val) (left + boundary (j.val + 1)) cellLo cellHi := by
  rw [d2FlowNodeStaticBag_child_port_eq_run_slice
    children hnonsat hfit boundary left rightStart j]
  exact orderedRunSlice_inter_cell _ _ _ _ _

/-- The two concrete parent end ports intersect a physical cell in exactly
the corresponding fragments of the sender's ordered address runs. -/
theorem d2FlowNodeStaticBag_parent_ports_inter_cell
    {n h ports : Nat} {base width G low high : Nat}
    (children : Fin 8 → D2FlowTree h) (hnonsat : G ≠ 8 * width)
    (hfit : StaticHolesFit (base + low)
      (d2FlowNodeStaticHoles base width low high children)
      (base + 8 * width - high))
    (boundary : Nat → Nat) (left rightStart cellLo cellHi : Nat) :
    (destinationPiece (ports := ports)
        (d2FlowNodeStaticBag (n := n) base width G low high children)
        boundary left rightStart none) ∩
        staticWireInterval cellLo cellHi =
      orderedRunSliceInCell
          (d2FlowNodeStaticRuns (n := n) base width G low high children)
          0 left cellLo cellHi ∪
        orderedRunSliceInCell
          (d2FlowNodeStaticRuns (n := n) base width G low high children)
          rightStart
          (d2FlowNodeStaticBag (n := n) base width G low high children).card
          cellLo cellHi := by
  rw [d2FlowNodeStaticBag_parent_ports_eq_run_slices
    children hnonsat hfit boundary left rightStart]
  rw [Finset.union_inter_distrib_right]
  rw [orderedRunSlice_inter_cell, orderedRunSlice_inter_cell]

/-- The cardinality of an ordered, fitting hole union is the sum of its
interval lengths. -/
theorem staticHoleUnion_card_of_fit {n : Nat} (cursor stop : Nat)
    (holes : List (Nat × Nat))
    (hfit : StaticHolesFit cursor holes stop) (hstop : stop ≤ n) :
    (staticHoleUnion (n := n) holes).card =
      (holes.map (fun p => p.2 - p.1)).sum := by
  induction holes generalizing cursor with
  | nil => simp [staticHoleUnion]
  | cons hole holes ih =>
      rcases hole with ⟨lo, hi⟩
      rcases hfit with ⟨hcursor, hwidth, hend, htail⟩
      have hdisj : Disjoint (staticWireInterval lo hi)
          (staticHoleUnion (n := n) holes) := by
        rw [Finset.disjoint_left]
        intro w hw htailw
        simp only [staticWireInterval, Finset.mem_filter,
          Finset.mem_univ, true_and] at hw
        have htailLower := staticHoleUnion_lower_bound hi stop holes htail htailw
        omega
      have hhiN : hi ≤ n := le_trans hend hstop
      simp only [staticHoleUnion, List.map_cons, List.sum_cons]
      rw [Finset.card_union_of_disjoint hdisj,
        staticWireInterval_card hhiN, ih hi htail]

/-- Every wire in a fitting hole lies inside its enclosing parent interval. -/
theorem staticHoleUnion_subset_interval {n : Nat} (cursor stop : Nat)
    (holes : List (Nat × Nat))
    (hfit : StaticHolesFit cursor holes stop) :
    staticHoleUnion (n := n) holes ⊆ staticWireInterval cursor stop := by
  induction holes generalizing cursor with
  | nil => simp [staticHoleUnion]
  | cons hole holes ih =>
      rcases hole with ⟨lo, hi⟩
      rcases hfit with ⟨hcursor, hwidth, hend, htail⟩
      intro w hw
      simp only [staticHoleUnion, Finset.mem_union] at hw
      simp only [staticWireInterval, Finset.mem_filter, Finset.mem_univ,
        true_and]
      rcases hw with hw | hw
      · simp only [staticWireInterval, Finset.mem_filter,
          Finset.mem_univ, true_and] at hw
        exact ⟨by omega, by omega⟩
      · have htailMem := ih hi htail hw
        simp only [staticWireInterval, Finset.mem_filter,
          Finset.mem_univ, true_and] at htailMem ⊢
        exact ⟨by omega, by omega⟩

/-- Under the fit invariant, a non-saturated sender's physical bag size is
the parent interval size minus the occupied child-hole sizes. -/
theorem d2FlowNodeStaticBag_card_of_fit {n h : Nat}
    (base width G low high : Nat) (children : Fin 8 → D2FlowTree h)
    (hnonsat : G ≠ 8 * width)
    (hfit : StaticHolesFit (base + low)
      (d2FlowNodeStaticHoles base width low high children)
      (base + 8 * width - high))
    (hstop : base + 8 * width - high ≤ n) :
    (d2FlowNodeStaticBag (n := n) base width G low high children).card =
      (8 * width - low - high) -
        (staticHoleUnion (n := n)
          (d2FlowNodeStaticHoles base width low high children)).card := by
  classical
  have hsubset := staticHoleUnion_subset_interval
    (n := n) (base + low) (base + 8 * width - high)
    (d2FlowNodeStaticHoles base width low high children) hfit
  simp only [d2FlowNodeStaticBag, if_neg hnonsat]
  rw [Finset.card_sdiff_of_subset hsubset,
    staticWireInterval_card hstop]
  omega

/-- Every static child hole has length equal to its native width minus the
child deficit; saturated children contribute length zero. -/
theorem d2EightChildHole_length_eq {base width left right : Nat}
    (deficit low high : Fin 8 → Nat) (j : Fin 8)
    (hcap : deficit j ≤ width)
    (hbalance : deficit j < width → low j + high j = deficit j) :
    (d2EightChildHole base width left right deficit low high j).2 -
        (d2EightChildHole base width left right deficit low high j).1 =
      width - deficit j := by
  by_cases hsat : deficit j = width
  · simp [d2EightChildHole, hsat] <;> split_ifs <;> simp
  · have hbal := hbalance (by omega)
    have hslot : (j.val + 1) * width = j.val * width + width := by
      rw [Nat.add_mul, Nat.one_mul]
    simp [d2EightChildHole, hsat]
    omega

/-- A non-saturated valid flow-tree root has balanced endpoint reserves. -/
theorem d2FlowTreeInv_root_balance {scale h : Nat}
    (tree : D2FlowTree h) (hinv : d2FlowTreeInv scale tree)
    (hunsat : d2FlowTreeRootDeficit tree < scale * 8 ^ h) :
    (d2FlowTreeRootData tree).2.1 +
        (d2FlowTreeRootData tree).2.2 =
      d2FlowTreeRootDeficit tree := by
  cases tree with
  | leaf G low high =>
      simp only [d2FlowTreeInv, d2FlowTreeRootDeficit] at hinv hunsat ⊢
      exact hinv.2 (by simpa using hunsat)
  | node G low high children =>
      simp only [d2FlowTreeInv, d2FlowTreeRootDeficit] at hinv hunsat ⊢
      exact hinv.2.2.1 (by simpa [Nat.pow_succ, Nat.mul_comm] using hunsat)

/-- For a valid child tree, the static interval removed from its native slot
has length equal to native capacity minus its root deficit. -/
theorem d2FlowNodeChildHole_length {scale h : Nat} (base left right : Nat)
    (children : Fin 8 → D2FlowTree h)
    (hinv : ∀ j, d2FlowTreeInv scale (children j)) (j : Fin 8) :
    (d2EightChildHole base (scale * 8 ^ h) left right
      (fun k => d2FlowTreeRootDeficit (children k))
      (fun k => (d2FlowTreeRootData (children k)).2.1)
      (fun k => (d2FlowTreeRootData (children k)).2.2) j).2 -
    (d2EightChildHole base (scale * 8 ^ h) left right
      (fun k => d2FlowTreeRootDeficit (children k))
      (fun k => (d2FlowTreeRootData (children k)).2.1)
      (fun k => (d2FlowTreeRootData (children k)).2.2) j).1 =
      scale * 8 ^ h - d2FlowTreeRootDeficit (children j) := by
  have hcap := d2FlowTreeInv_root_native_bound (children j) (hinv j)
  have hbalance :
      d2FlowTreeRootDeficit (children j) < scale * 8 ^ h →
        (d2FlowTreeRootData (children j)).2.1 +
            (d2FlowTreeRootData (children j)).2.2 =
          d2FlowTreeRootDeficit (children j) := by
    intro hunsat
    exact d2FlowTreeInv_root_balance (children j) (hinv j) hunsat
  exact d2EightChildHole_length_eq _ _ _ j hcap hbalance

/-- The list encoding of finitely many holes preserves the sum of their
lengths. -/
theorem staticHoleList_lengths_sum {m : Nat} (lo hi : Fin m → Nat) :
    ((staticHoleList m lo hi).map (fun p => p.2 - p.1)).sum =
      Finset.univ.sum (fun j : Fin m => hi j - lo j) := by
  induction m with
  | zero => simp [staticHoleList]
  | succ m ih =>
      rw [staticHoleList, List.map_cons, List.sum_cons,
        Fin.sum_univ_succ]
      congr 1
      exact ih (fun j => lo j.succ) (fun j => hi j.succ)

/-- Under the recursive flow invariant, all eight static child holes remove
exactly their native capacity minus the total child deficit. -/
theorem d2FlowNodeStaticHoles_card {n scale h : Nat}
    (base low high : Nat) (children : Fin 8 → D2FlowTree h)
    (hinv : ∀ j, d2FlowTreeInv scale (children j))
    (hfit : StaticHolesFit (base + low)
      (d2FlowNodeStaticHoles base (scale * 8 ^ h) low high children)
      (base + 8 * (scale * 8 ^ h) - high))
    (hstop : base + 8 * (scale * 8 ^ h) - high ≤ n) :
    (staticHoleUnion (n := n)
      (d2FlowNodeStaticHoles base (scale * 8 ^ h) low high children)).card =
      8 * (scale * 8 ^ h) -
        d2FlowTotal (fun j => d2FlowTreeRootDeficit (children j)) := by
  have hcard := staticHoleUnion_card_of_fit (base + low)
    (base + 8 * (scale * 8 ^ h) - high)
    (d2FlowNodeStaticHoles base (scale * 8 ^ h) low high children) hfit hstop
  let hole : Fin 8 → Nat × Nat := fun j =>
    d2EightChildHole base (scale * 8 ^ h) low high
      (fun k => d2FlowTreeRootDeficit (children k))
      (fun k => (d2FlowTreeRootData (children k)).2.1)
      (fun k => (d2FlowTreeRootData (children k)).2.2) j
  have hlength := staticHoleList_lengths_sum
    (fun j => (hole j).1) (fun j => (hole j).2)
  have hsumLengths :
      ((d2FlowNodeStaticHoles base (scale * 8 ^ h) low high children).map
        (fun p => p.2 - p.1)).sum =
      Finset.univ.sum (fun j : Fin 8 =>
        (scale * 8 ^ h) - d2FlowTreeRootDeficit (children j)) := by
    calc
      ((d2FlowNodeStaticHoles base (scale * 8 ^ h) low high children).map
          (fun p => p.2 - p.1)).sum =
        Finset.univ.sum (fun j : Fin 8 => (hole j).2 - (hole j).1) := by
          simpa [d2FlowNodeStaticHoles, hole] using hlength
      _ = Finset.univ.sum (fun j : Fin 8 =>
          (scale * 8 ^ h) - d2FlowTreeRootDeficit (children j)) := by
            apply Finset.sum_congr rfl
            intro j hj
            exact d2FlowNodeChildHole_length base low high children hinv j
  have hsum :
      (Finset.univ.sum (fun j : Fin 8 => (scale * 8 ^ h) -
        d2FlowTreeRootDeficit (children j))) =
        8 * (scale * 8 ^ h) -
          d2FlowTotal (fun j => d2FlowTreeRootDeficit (children j)) := by
    simp only [d2FlowTotal]
    have hcap (j : Fin 8) :
        d2FlowTreeRootDeficit (children j) ≤ scale * 8 ^ h :=
      d2FlowTreeInv_root_native_bound (children j) (hinv j)
    have hadd :
        Finset.univ.sum (fun j : Fin 8 =>
          (scale * 8 ^ h) - d2FlowTreeRootDeficit (children j)) +
        Finset.univ.sum (fun j : Fin 8 =>
          d2FlowTreeRootDeficit (children j)) =
        Finset.univ.sum (fun _ : Fin 8 => scale * 8 ^ h) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j hj
      exact Nat.sub_add_cancel (hcap j)
    have hwidth : Finset.univ.sum (fun _ : Fin 8 =>
        scale * 8 ^ h) = 8 * (scale * 8 ^ h) := by simp
    omega
  rw [hcard, hsumLengths, hsum]

/-- A valid nonsaturated flow node's static physical bag has exactly the
mass expected by the ordinary sender rank-port partition. -/
theorem d2FlowNodeStaticBag_card_eq_child_total_sub_G {n scale h : Nat}
    (base G low high : Nat) (children : Fin 8 → D2FlowTree h)
    (htree : d2FlowTreeInv scale (.node G low high children))
    (hfit : StaticHolesFit (base + low)
      (d2FlowNodeStaticHoles base (scale * 8 ^ h) low high children)
      (base + 8 * (scale * 8 ^ h) - high))
    (hstop : base + 8 * (scale * 8 ^ h) - high ≤ n)
    (hGlt : G < 8 * (scale * 8 ^ h)) :
    (d2FlowNodeStaticBag (n := n) base (scale * 8 ^ h)
      G low high children).card =
      d2FlowTotal (fun j => d2FlowTreeRootDeficit (children j)) - G := by
  have htree' := htree
  simp only [d2FlowTreeInv] at htree'
  have hchildren : ∀ j, d2FlowTreeInv scale (children j) := htree'.2.2.2
  have hbalance : low + high = G := by
    have hroot := htree'.2.2.1
    have hnative : G < scale * 8 ^ (h + 1) := by
      simpa [Nat.pow_succ, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
        using hGlt
    exact hroot hnative
  have hbag := d2FlowNodeStaticBag_card_of_fit base (scale * 8 ^ h)
    G low high children (by omega) hfit hstop
  have hholes := d2FlowNodeStaticHoles_card base low high children
    hchildren hfit hstop
  have htotal : G ≤ d2FlowTotal
      (fun j => d2FlowTreeRootDeficit (children j)) := by
    simpa [d2FlowTotal] using htree'.2.1
  have htotalcap : d2FlowTotal
      (fun j => d2FlowTreeRootDeficit (children j)) ≤
        8 * (scale * 8 ^ h) := by
    unfold d2FlowTotal
    calc
      _ ≤ Finset.univ.sum (fun _ : Fin 8 => scale * 8 ^ h) :=
        Finset.sum_le_sum fun j _ =>
          d2FlowTreeInv_root_native_bound (children j) (hchildren j)
      _ = 8 * (scale * 8 ^ h) := by simp
  rw [hbag, hholes]
  have hparentLength :
      8 * (scale * 8 ^ h) - low - high =
        8 * (scale * 8 ^ h) - G := by omega
  rw [hparentLength]
  omega

/-- If the parent deficit exhausts its children, no wires remain in that
node's static sender bag. -/
theorem d2FlowNodeStaticBag_eq_empty_of_child_total_eq_G
    {n scale h : Nat} (base G low high : Nat)
    (children : Fin 8 → D2FlowTree h)
    (htree : d2FlowTreeInv scale (.node G low high children))
    (hfit : StaticHolesFit (base + low)
      (d2FlowNodeStaticHoles base (scale * 8 ^ h) low high children)
      (base + 8 * (scale * 8 ^ h) - high))
    (hstop : base + 8 * (scale * 8 ^ h) - high ≤ n)
    (hsum : d2FlowTotal
      (fun j => d2FlowTreeRootDeficit (children j)) = G) :
    d2FlowNodeStaticBag (n := n) base (scale * 8 ^ h)
      G low high children = ∅ := by
  by_cases hsat : G = 8 * (scale * 8 ^ h)
  · simp [d2FlowNodeStaticBag, hsat]
  · have hGnative := d2FlowTreeInv_root_native_bound
      (.node G low high children) htree
    have hGlt : G < 8 * (scale * 8 ^ h) := by
      have hGle : G ≤ 8 * (scale * 8 ^ h) := by
        simpa [Nat.pow_succ, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
          using hGnative
      exact lt_of_le_of_ne hGle hsat
    have hcard := d2FlowNodeStaticBag_card_eq_child_total_sub_G
      base G low high children htree hfit hstop hGlt
    rw [hsum] at hcard
    have hzero :
        (d2FlowNodeStaticBag (n := n) base (scale * 8 ^ h)
          G low high children).card = 0 := by omega
    exact Finset.card_eq_zero.mp hzero

/-- The ordinary sender reserve contract puts both front cuts inside the
child-rank interval, so the eight child ports form a valid middle block. -/
theorem d2FlowStageInvInputs_ordinary_front_bounds
    {scale h i G low high : Nat} {active : Nat → Bool}
    {role : Nat → D2Role} {quota : Nat → D2Role → Nat}
    {cap : Nat → Nat} (children : Fin 8 → D2FlowTree h)
    (hinputs : d2FlowStageInvInputs scale active role quota cap i
      (.node G low high children)) (ha : active i = true)
    (hr : role i = .topRise ∨ role i = .mid ∨ role i = .botDesc) :
    quota i (role i) % 2 = 0 ∧
      low + quota i (role i) / 2 ≤
        d2FlowTotal (fun j => d2FlowTreeRootDeficit (children j)) ∧
      high + quota i (role i) / 2 ≤
        d2FlowTotal (fun j => d2FlowTreeRootDeficit (children j)) ∧
      low + quota i (role i) / 2 ≤
        d2FlowTotal (fun j => d2FlowTreeRootDeficit (children j)) -
          high - quota i (role i) / 2 := by
  have hstage := hinputs.2
  simp only [ha, if_true] at hstage
  cases hrole : role i with
  | topDesc => simp [hrole] at hr
  | botRise => simp [hrole] at hr
  | topRise | mid | botDesc =>
      simp only [hrole] at hstage ⊢
      rcases hstage with ⟨hbalance, hG, hqcap, hqtotal, heven,
        hleftcap, hrightcap⟩
      have hquotaEq : quota i (role i) =
          2 * (quota i (role i) / 2) := by
        rw [hrole]
        omega
      have hquotaEq' := hquotaEq
      rw [hrole] at hquotaEq'
      have hqcapHalf : 512 * (quota i (role i) / 2) ≤ cap i := by
        rw [hrole]
        rw [hquotaEq'] at hqcap
        nlinarith [hqcap]
      have hfront_left : 2 * G + quota i (role i) ≤
          d2FlowTreeRootDeficit (children ⟨0, by omega⟩) := by
        have hsum := Nat.add_le_add hG hqcapHalf
        have hcap' := Nat.add_le_add hleftcap hleftcap
        omega
      have hfront_right : 2 * G + quota i (role i) ≤
          d2FlowTreeRootDeficit (children ⟨7, by omega⟩) := by
        have hsum := Nat.add_le_add hG hqcapHalf
        have hcap' := Nat.add_le_add hrightcap hrightcap
        omega
      have htotEnds :
          d2FlowTreeRootDeficit (children ⟨0, by omega⟩) +
            d2FlowTreeRootDeficit (children ⟨7, by omega⟩) ≤
          d2FlowTotal (fun j => d2FlowTreeRootDeficit (children j)) := by
        have hsum := Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.subset_univ ({⟨0, by omega⟩, ⟨7, by omega⟩} :
            Finset (Fin 8)))
          (fun j hj hj' => Nat.zero_le
            (d2FlowTreeRootDeficit (children j)))
        simpa [d2FlowTotal] using hsum
      constructor
      · exact heven
      constructor
      · have hbalance' : low ≤ G := by omega
        omega
      constructor
      · have hbalance' : high ≤ G := by omega
        omega
      · have hbalance' : low + high = G := hbalance
        omega

/-- After an active ordinary cut, all wires in the updated node interval are
accounted for by its child holes: its own static sender bag is empty. -/
theorem d2FlowStage_active_ordinary_static_bag_empty
    {n scale h i G low high : Nat} {active : Nat → Bool}
    {role : Nat → D2Role} {quota : Nat → D2Role → Nat}
    {cap : Nat → Nat} (children : Fin 8 → D2FlowTree h)
    (htree : d2FlowTreeInv scale (.node G low high children))
    (hinputs : d2FlowStageInvInputs scale active role quota cap i
      (.node G low high children))
    (ha : active i = true)
    (hr : role i = .topRise ∨ role i = .mid ∨ role i = .botDesc)
    (hstop : 8 * (scale * 8 ^ h) -
      (high + quota i (role i) / 2) ≤ n) :
    d2FlowNodeStaticBag (n := n) 0
      (scale * 8 ^ h) (G + quota i (role i))
      (low + quota i (role i) / 2)
      (high + quota i (role i) - quota i (role i) / 2)
      (fun j => d2FlowTreeChild
        (d2FlowStage active role quota (h + 1) i
          (.node G low high children)) j) = ∅ := by
  have hfit := d2FlowStage_active_ordinary_static_fit children htree
    hinputs ha hr
  have hstage := hinputs.2
  simp only [ha, if_true] at hstage
  have hbalance : G = low + high := by
    rcases hr with htop | hmid | hbot
    · simp only [htop] at hstage
      exact hstage.1.symm
    · simp only [hmid] at hstage
      exact hstage.1.symm
    · simp only [hbot] at hstage
      exact hstage.1.symm
  have hbounds := d2FlowStageInvInputs_ordinary_front_bounds
    children hinputs ha hr
  have hsum := d2FlowStage_regular_child_mass children ha hr
    hbalance hbounds.1 hbounds.2.1 hbounds.2.2.1 hbounds.2.2.2
  have hsum' : d2FlowTotal (fun j => d2FlowTreeRootDeficit
      (d2FlowTreeChild
        (d2FlowStage active role quota (h + 1) i
          (.node G low high children)) j)) = G + quota i (role i) := by
    simpa [d2FlowTotal] using hsum
  have hright : high + quota i (role i) - quota i (role i) / 2 =
      high + quota i (role i) / 2 := by omega
  have hfit' : StaticHolesFit (low + quota i (role i) / 2)
      (d2FlowNodeStaticHoles 0 (scale * 8 ^ h)
        (low + quota i (role i) / 2)
        (high + quota i (role i) - quota i (role i) / 2)
        (fun j => d2FlowTreeChild
          (d2FlowStage active role quota (h + 1) i
            (.node G low high children)) j))
      (8 * (scale * 8 ^ h) -
        (high + quota i (role i) - quota i (role i) / 2)) := by
    rw [hright]
    simpa using hfit
  have houtinv := d2FlowStage_preserves_inv_of_inputs
    (.node G low high children) htree hinputs
  apply d2FlowNodeStaticBag_eq_empty_of_child_total_eq_G
    (base := 0) (G := G + quota i (role i))
    (low := low + quota i (role i) / 2)
    (high := high + quota i (role i) - quota i (role i) / 2)
    (children := fun j => d2FlowTreeChild
      (d2FlowStage active role quota (h + 1) i
        (.node G low high children)) j)
  · rcases hr with hrole | hrole | hrole <;>
      simpa [d2FlowStage, ha, hrole] using houtinv
  · simpa [Nat.zero_add] using hfit'
  · omega
  · exact hsum'

/-- Instantiate the generic ordinary rank-port partition with the concrete
static physical bag of a flow node. This partitions the current sender set;
identifying the pieces with all next-stage bags is a separate global step. -/
theorem d2FlowNode_active_ordinary_piece_partition
    {n scale h i G low high : Nat} {active : Nat → Bool}
    {role : Nat → D2Role} {quota : Nat → D2Role → Nat}
    {cap : Nat → Nat} (base : Nat)
    (children : Fin 8 → D2FlowTree h)
    (htree : d2FlowTreeInv scale (.node G low high children))
    (hinputs : d2FlowStageInvInputs scale active role quota cap i
      (.node G low high children))
    (ha : active i = true)
    (hr : role i = .topRise ∨ role i = .mid ∨ role i = .botDesc)
    (hfit : StaticHolesFit (base + low)
      (d2FlowNodeStaticHoles base (scale * 8 ^ h) low high children)
      (base + 8 * (scale * 8 ^ h) - high))
    (hstop : base + 8 * (scale * 8 ^ h) - high ≤ n)
    (hGlt : G < 8 * (scale * 8 ^ h)) :
    let sender := d2FlowNodeStaticBag (n := n) base (scale * 8 ^ h)
      G low high children
    let widths : Fin 8 → Nat := fun j =>
      d2FlowTreeRootDeficit (children j) -
        d2FlowTreeRootDeficit
          (d2FlowTreeChild
            (d2FlowStage active role quota (h + 1) i
              (.node G low high children)) j)
    let boundary : Nat → Nat := d2FlowRankBoundary widths
    (∀ target : Option (Fin 8),
      destinationPiece (ports := 8) sender boundary (quota i (role i) / 2)
        (sender.card - quota i (role i) / 2) target ⊆ sender) ∧
    Finset.univ.biUnion
      (destinationPiece (ports := 8) sender boundary (quota i (role i) / 2)
        (sender.card - quota i (role i) / 2)) = sender ∧
    (∀ a b, a ≠ b →
      Disjoint
        (destinationPiece (ports := 8) sender boundary (quota i (role i) / 2)
          (sender.card - quota i (role i) / 2) a)
        (destinationPiece (ports := 8) sender boundary (quota i (role i) / 2)
          (sender.card - quota i (role i) / 2) b)) := by
  let sender := d2FlowNodeStaticBag (n := n) base (scale * 8 ^ h)
    G low high children
  let widths : Fin 8 → Nat := fun j =>
    d2FlowTreeRootDeficit (children j) -
      d2FlowTreeRootDeficit
        (d2FlowTreeChild
          (d2FlowStage active role quota (h + 1) i
            (.node G low high children)) j)
  let boundary : Nat → Nat := d2FlowRankBoundary widths
  have hbalance : G = low + high := by
    have hroot := d2FlowTreeInv_root_balance
      (.node G low high children) htree (by
        simpa [Nat.pow_succ, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
          using hGlt)
    exact hroot.symm
  have hsender : sender.card =
      d2FlowTotal (fun j => d2FlowTreeRootDeficit (children j)) - G := by
    dsimp [sender]
    exact d2FlowNodeStaticBag_card_eq_child_total_sub_G base G low high
      children htree hfit hstop hGlt
  have hfront := d2FlowStageInvInputs_ordinary_front_bounds
    children hinputs ha hr
  simpa only [sender, widths, boundary] using
    (regular_stage_sender_piece_partition children sender ha hr hbalance
      hfront.1 hfront.2.1 hfront.2.2.1 hfront.2.2.2 hsender)

/-- The tree-capacity/balance invariant alone does not guarantee that a
node's child holes fit between its fronts. Thus the candidate proof must use
the schedule's endpoint-reserve input, not just `d2FlowTreeInv`. -/
theorem d2FlowTreeInv_alone_not_static_holes_fit :
    ∃ (tree : D2FlowTree 1),
      d2FlowTreeInv 2 tree ∧
      ¬ StaticHolesFit 1
        (d2FlowNodeStaticHoles 0 2 1 0
          (fun j => d2FlowTreeChild tree j)) 16 := by
  let children : Fin 8 -> D2FlowTree 0 := fun j =>
    if j.val = 0 then .leaf 1 0 1 else .leaf 0 0 0
  let tree : D2FlowTree 1 := .node 1 1 0 children
  have hchildren : ∀ j, d2FlowTreeInv 2 (children j) := by
    intro j
    by_cases hj : j.val = 0
    · have hj0 : j = ⟨0, by omega⟩ := Fin.ext hj
      rw [hj0]
      norm_num [children, d2FlowTreeInv]
    · change d2FlowTreeInv 2
        (if j.val = 0 then .leaf 1 0 1 else .leaf 0 0 0)
      rw [if_neg hj]
      norm_num [d2FlowTreeInv]
  have hzero : d2FlowTreeRootDeficit (children ⟨0, by omega⟩) = 1 := by
    norm_num [children, d2FlowTreeRootDeficit]
  have hinv : d2FlowTreeInv 2 tree := by
    simp only [tree, d2FlowTreeInv]
    refine ⟨by norm_num, ?_, ?_, hchildren⟩
    · calc
        1 = d2FlowTreeRootDeficit (children ⟨0, by omega⟩) := hzero.symm
        _ ≤ Finset.univ.sum (fun j : Fin 8 =>
            d2FlowTreeRootDeficit (children j)) :=
          Finset.single_le_sum
            (fun j _ => Nat.zero_le (d2FlowTreeRootDeficit (children j)))
            (Finset.mem_univ (⟨0, by omega⟩ : Fin 8))
    · intro _
      norm_num
  refine ⟨tree, hinv, ?_⟩
  intro hfit
  have hfirst := hfit.1
  norm_num [d2FlowNodeStaticHoles, staticHoleList, d2EightChildHole,
    children, tree, d2FlowTreeChild, d2FlowTreeRootDeficit,
    d2FlowTreeRootData] at hfirst

end Chvatal.D2PhysicalBagState
