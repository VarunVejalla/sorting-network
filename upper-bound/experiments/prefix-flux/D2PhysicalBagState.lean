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

/-- Alternative point locations for saturated empty holes. Clamping the slot
marker into the parent interval preserves the removed wire set and can keep
the hole list ordered when a parent frontier passes several native slots. -/
def d2EightChildHoleClamped {h : Nat} (base width left right : Nat)
    (children : Fin 8 → D2FlowTree h) (j : Fin 8) : Nat × Nat :=
  if d2FlowTreeRootDeficit (children j) = width then
    let cursor := base + left
    let stop := base + 8 * width - right
    let point := max cursor (min (base + j.val * width) stop)
    (point, point)
  else
    d2EightChildHole base width left right
      (fun k => d2FlowTreeRootDeficit (children k))
      (fun k => (d2FlowTreeRootData (children k)).2.1)
      (fun k => (d2FlowTreeRootData (children k)).2.2) j

/-- Moving an empty saturated-hole marker does not change its wire set. -/
theorem d2EightChildHoleClamped_interval_eq {n h : Nat}
    (base width left right : Nat) (children : Fin 8 → D2FlowTree h)
    (j : Fin 8) :
    staticWireInterval (n := n)
        (d2EightChildHole base width left right
          (fun k => d2FlowTreeRootDeficit (children k))
          (fun k => (d2FlowTreeRootData (children k)).2.1)
          (fun k => (d2FlowTreeRootData (children k)).2.2) j).1
        (d2EightChildHole base width left right
          (fun k => d2FlowTreeRootDeficit (children k))
          (fun k => (d2FlowTreeRootData (children k)).2.1)
          (fun k => (d2FlowTreeRootData (children k)).2.2) j).2 =
      staticWireInterval (n := n)
        (d2EightChildHoleClamped base width left right children j).1
        (d2EightChildHoleClamped base width left right children j).2 := by
  by_cases hsat : d2FlowTreeRootDeficit (children j) = width
  · have hleft :
        (d2EightChildHole base width left right
          (fun k => d2FlowTreeRootDeficit (children k))
          (fun k => (d2FlowTreeRootData (children k)).2.1)
          (fun k => (d2FlowTreeRootData (children k)).2.2) j).1 =
        (d2EightChildHole base width left right
          (fun k => d2FlowTreeRootDeficit (children k))
          (fun k => (d2FlowTreeRootData (children k)).2.1)
          (fun k => (d2FlowTreeRootData (children k)).2.2) j).2 := by
      by_cases hj0 : j.val = 0
      · simp [d2EightChildHole, hsat, hj0]
      · by_cases hj7 : j.val = 7
        · simp [d2EightChildHole, hsat, hj0, hj7]
        · simp [d2EightChildHole, hsat, hj0, hj7]
    have hright :
        (d2EightChildHoleClamped base width left right children j).1 =
        (d2EightChildHoleClamped base width left right children j).2 := by
      simp only [d2EightChildHoleClamped, if_pos hsat]
    have hempty (p : Nat × Nat) (hp : p.1 = p.2) :
        staticWireInterval (n := n) p.1 p.2 = ∅ := by
      rcases p with ⟨lo, hi⟩
      change lo = hi at hp
      subst hi
      simp [staticWireInterval]
    calc
      staticWireInterval (n := n)
          (d2EightChildHole base width left right
            (fun k => d2FlowTreeRootDeficit (children k))
            (fun k => (d2FlowTreeRootData (children k)).2.1)
            (fun k => (d2FlowTreeRootData (children k)).2.2) j).1
          (d2EightChildHole base width left right
            (fun k => d2FlowTreeRootDeficit (children k))
            (fun k => (d2FlowTreeRootData (children k)).2.1)
            (fun k => (d2FlowTreeRootData (children k)).2.2) j).2 = ∅ :=
        hempty _ hleft
      _ = staticWireInterval (n := n)
          (d2EightChildHoleClamped base width left right children j).1
          (d2EightChildHoleClamped base width left right children j).2 :=
        (hempty _ hright).symm
  · simp [d2EightChildHole, d2EightChildHoleClamped, hsat]

/-- Hole list with the clamped point convention for saturated children. -/
def d2FlowNodeStaticHolesClamped {h : Nat} (base width low high : Nat)
    (children : Fin 8 → D2FlowTree h) : List (Nat × Nat) :=
  staticHoleList 8
    (fun j => (d2EightChildHoleClamped base width low high children j).1)
    (fun j => (d2EightChildHoleClamped base width low high children j).2)

theorem staticHoleList_union_eq_of_pointwise_interval_eq {n m : Nat}
    (lo hi lo' hi' : Fin m → Nat)
    (heq : ∀ j, staticWireInterval (n := n) (lo j) (hi j) =
      staticWireInterval (n := n) (lo' j) (hi' j)) :
    staticHoleUnion (n := n) (staticHoleList m lo hi) =
      staticHoleUnion (n := n) (staticHoleList m lo' hi') := by
  induction m with
  | zero => simp [staticHoleList, staticHoleUnion]
  | succ m ih =>
      let first : Fin (m + 1) := ⟨0, by omega⟩
      change staticWireInterval (n := n) (lo first) (hi first) ∪
          staticHoleUnion (staticHoleList m (fun j => lo j.succ)
            (fun j => hi j.succ)) =
        staticWireInterval (n := n) (lo' first) (hi' first) ∪
          staticHoleUnion (staticHoleList m (fun j => lo' j.succ)
            (fun j => hi' j.succ))
      rw [heq first]
      congr 1
      exact ih (fun j => lo j.succ) (fun j => hi j.succ)
        (fun j => lo' j.succ) (fun j => hi' j.succ)
        (fun j => heq j.succ)

/-- The original and clamped hole lists remove exactly the same wires. -/
theorem d2FlowNodeStaticHoles_union_eq_clamped {n h : Nat}
    (base width low high : Nat) (children : Fin 8 → D2FlowTree h) :
    staticHoleUnion (n := n)
        (d2FlowNodeStaticHoles base width low high children) =
      staticHoleUnion (n := n)
        (d2FlowNodeStaticHolesClamped base width low high children) := by
  apply staticHoleList_union_eq_of_pointwise_interval_eq
  intro j
  exact d2EightChildHoleClamped_interval_eq base width low high children j

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

/-- The clamped empty-hole convention is extensionally the same physical
sender set; only its ordered-run representation can differ. -/
theorem d2FlowNodeStaticBag_eq_clamped_holes {n h : Nat}
    (base width G low high : Nat) (children : Fin 8 → D2FlowTree h) :
    d2FlowNodeStaticBag (n := n) base width G low high children =
      if G = 8 * width then ∅ else
        staticWireInterval (base + low) (base + 8 * width - high) \
          staticHoleUnion (d2FlowNodeStaticHolesClamped
            base width low high children) := by
  by_cases hsat : G = 8 * width
  · simp [d2FlowNodeStaticBag, hsat]
  · simp [d2FlowNodeStaticBag, hsat,
      d2FlowNodeStaticHoles_union_eq_clamped]

/-- The ordered address runs of a flow node's sender bag. -/
def d2FlowNodeStaticRuns {n h : Nat} (base width G low high : Nat)
    (children : Fin 8 -> D2FlowTree h) : List (Finset (Fin n)) :=
  if G = 8 * width then [] else
    staticGapRuns (base + low)
      (d2FlowNodeStaticHoles base width low high children)
      (base + 8 * width - high)

/-- A fitting ordered hole list keeps every hole inside the parent interval.
This is the endpoint projection needed when the holes are updated recursively. -/
theorem staticHoleList_fit_bounds {m : Nat} (cursor stop : Nat)
    (lo hi : Fin m → Nat)
    (hfit : StaticHolesFit cursor (staticHoleList m lo hi) stop) :
    ∀ j, cursor ≤ lo j ∧ hi j ≤ stop := by
  induction m generalizing cursor with
  | zero => intro j; exact Fin.elim0 j
  | succ m ih =>
      let first : Fin (m + 1) := ⟨0, by omega⟩
      change cursor ≤ lo first ∧ lo first ≤ hi first ∧
        hi first ≤ stop ∧
          StaticHolesFit (hi first)
            (staticHoleList m (fun j => lo j.succ)
              (fun j => hi j.succ)) stop at hfit
      rcases hfit with ⟨hstart, hwidth, hend, htail⟩
      intro j
      cases j using Fin.cases with
      | zero => exact ⟨hstart, hend⟩
      | succ j =>
          have hbounds := ih (cursor := hi first)
            (fun j => lo j.succ) (fun j => hi j.succ) htail j
          exact ⟨le_trans (le_trans hstart hwidth) hbounds.1, hbounds.2⟩

theorem staticHolesFit_parent_order {cursor stop : Nat}
    {holes : List (Nat × Nat)}
    (hfit : StaticHolesFit cursor holes stop) : cursor ≤ stop := by
  induction holes generalizing cursor with
  | nil => simpa [StaticHolesFit] using hfit
  | cons hole holes ih =>
      simp only [StaticHolesFit] at hfit
      exact le_trans hfit.1 (le_trans hfit.2.1 hfit.2.2.1)

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

/-- A subtree's own recursive stage never moves either occupied-interval
front inward. Parent overwrites are separate and are handled at that parent. -/
theorem d2FlowStage_root_fronts_mono
    (active : Nat → Bool) (role : Nat → D2Role)
    (quota : Nat → D2Role → Nat) {h : Nat} (i : Nat)
    (tree : D2FlowTree h) :
    (d2FlowTreeRootData tree).2.1 ≤
        (d2FlowTreeRootData (d2FlowStage active role quota h i tree)).2.1 ∧
      (d2FlowTreeRootData tree).2.2 ≤
        (d2FlowTreeRootData (d2FlowStage active role quota h i tree)).2.2 := by
  cases tree with
  | leaf G low high => simp [d2FlowStage, d2FlowTreeRootData]
  | node G low high children =>
      by_cases ha : active i = true
      · cases hrole : role i <;>
          simp [d2FlowStage, d2FlowTreeRootData, ha, hrole] <;> omega
      · simp [d2FlowStage, d2FlowTreeRootData, ha]

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

/-- When every nonempty child interval stays inside the parent interval,
clamping empty saturated markers yields a fitting ordered hole list. -/
theorem d2FlowNodeStaticHolesClamped_fit_of_child_intervals_contained
    {scale h base width left right : Nat}
    (children : Fin 8 → D2FlowTree h)
    (hwidth : width = scale * 8 ^ h)
    (hinv : ∀ j, d2FlowTreeInv scale (children j))
    (hparent : base + left ≤ base + 8 * width - right)
    (hcontain : ∀ j,
      d2FlowTreeRootDeficit (children j) < width →
        base + left ≤ base + j.val * width +
            (d2FlowTreeRootData (children j)).2.1 ∧
        base + (j.val + 1) * width -
            (d2FlowTreeRootData (children j)).2.2 ≤
          base + 8 * width - right) :
    StaticHolesFit (base + left)
      (d2FlowNodeStaticHolesClamped base width left right children)
      (base + 8 * width - right) := by
  let cursor := base + left
  let stop := base + 8 * width - right
  let lo : Fin 8 → Nat := fun j =>
    (d2EightChildHoleClamped base width left right children j).1
  let hi : Fin 8 → Nat := fun j =>
    (d2EightChildHoleClamped base width left right children j).2
  have hcap (j : Fin 8) : d2FlowTreeRootDeficit (children j) ≤ width := by
    simpa [hwidth] using d2FlowTreeInv_root_native_bound (children j) (hinv j)
  have hopen (j : Fin 8) (hsat :
      d2FlowTreeRootDeficit (children j) ≠ width) :
      d2FlowTreeRootDeficit (children j) < width := by
    have hcapj := hcap j
    omega
  have hsatLo (j : Fin 8) (hsat :
      d2FlowTreeRootDeficit (children j) = width) :
      lo j = max cursor (min (base + j.val * width) stop) := by
    simp [lo, d2EightChildHoleClamped, cursor, stop, hsat]
  have hsatHi (j : Fin 8) (hsat :
      d2FlowTreeRootDeficit (children j) = width) :
      hi j = max cursor (min (base + j.val * width) stop) := by
    simp [hi, d2EightChildHoleClamped, cursor, stop, hsat]
  have hopenLo (j : Fin 8) (hsat :
      d2FlowTreeRootDeficit (children j) ≠ width) :
      lo j = base + j.val * width +
        (d2FlowTreeRootData (children j)).2.1 := by
    simp [lo, d2EightChildHoleClamped, d2EightChildHole, hsat]
  have hopenHi (j : Fin 8) (hsat :
      d2FlowTreeRootDeficit (children j) ≠ width) :
      hi j = base + (j.val + 1) * width -
        (d2FlowTreeRootData (children j)).2.2 := by
    simp [hi, d2EightChildHoleClamped, d2EightChildHole, hsat]
  have hstart : ∀ j, cursor ≤ lo j := by
    intro j
    by_cases hs : d2FlowTreeRootDeficit (children j) = width
    · rw [hsatLo j hs]
      exact le_max_left _ _
    · rw [hopenLo j hs]
      exact (hcontain j (hopen j hs)).1
  have hwidths : ∀ j, lo j ≤ hi j := by
    intro j
    by_cases hs : d2FlowTreeRootDeficit (children j) = width
    · rw [hsatLo j hs, hsatHi j hs]
    · rw [hopenLo j hs, hopenHi j hs]
      have hbalance := d2FlowTreeInv_root_balance (children j) (hinv j)
        (by simpa [hwidth] using hopen j hs)
      have hslot : (j.val + 1) * width = j.val * width + width := by
        rw [Nat.add_mul, Nat.one_mul]
      have hcapj := hcap j
      omega
  have hend : ∀ j, hi j ≤ stop := by
    intro j
    by_cases hs : d2FlowTreeRootDeficit (children j) = width
    · rw [hsatHi j hs]
      exact max_le (by simpa [cursor] using hparent) (min_le_right _ _)
    · rw [hopenHi j hs]
      exact (hcontain j (hopen j hs)).2
  have hordered : ∀ i j, i.val < j.val → hi i ≤ lo j := by
    intro i j hij
    by_cases his : d2FlowTreeRootDeficit (children i) = width <;>
      by_cases hjs : d2FlowTreeRootDeficit (children j) = width
    · rw [hsatHi i his, hsatLo j hjs]
      have hslot : base + i.val * width ≤ base + j.val * width := by
        have hmul := Nat.mul_le_mul_right width (Nat.le_of_lt hij)
        omega
      exact max_le_max le_rfl
        (min_le_min hslot le_rfl)
    · rw [hsatHi i his, hopenLo j hjs]
      have hcursor := (hcontain j (hopen j hjs)).1
      have hslot : base + i.val * width ≤
          base + j.val * width + (d2FlowTreeRootData (children j)).2.1 := by
        have hmul := Nat.mul_le_mul_right width (Nat.le_of_lt hij)
        omega
      exact max_le hcursor (le_trans (min_le_left _ _) hslot)
    · rw [hopenHi i his, hsatLo j hjs]
      have hstop := (hcontain i (hopen i his)).2
      have hslot : base + (i.val + 1) * width -
          (d2FlowTreeRootData (children i)).2.2 ≤ base + j.val * width := by
        have hmul := Nat.mul_le_mul_right width (by omega : i.val + 1 ≤ j.val)
        omega
      have hmin : base + (i.val + 1) * width -
          (d2FlowTreeRootData (children i)).2.2 ≤
            min (base + j.val * width) stop := le_min hslot hstop
      exact le_trans hmin (le_max_right _ _)
    · rw [hopenHi i his, hopenLo j hjs]
      have hmul := Nat.mul_le_mul_right width (by omega : i.val + 1 ≤ j.val)
      omega
  have hfit := staticHoleList_fits cursor stop lo hi
    (by simpa [cursor, stop] using hparent) hstart hwidths hend hordered
  simpa [cursor, stop, d2FlowNodeStaticHolesClamped, lo, hi] using hfit

/-- If the canonical hole list already fits, replacing its empty saturated
markers by clamped markers preserves fit. -/
theorem d2FlowNodeStaticHolesClamped_fit_of_static_fit
    {scale h base width left right : Nat}
    (children : Fin 8 → D2FlowTree h)
    (hwidth : width = scale * 8 ^ h)
    (hinv : ∀ j, d2FlowTreeInv scale (children j))
    (hfit : StaticHolesFit (base + left)
      (d2FlowNodeStaticHoles base width left right children)
      (base + 8 * width - right)) :
    StaticHolesFit (base + left)
      (d2FlowNodeStaticHolesClamped base width left right children)
      (base + 8 * width - right) := by
  have hparent := staticHolesFit_parent_order hfit
  have hbounds := staticHoleList_fit_bounds (base + left)
    (base + 8 * width - right)
    (fun j => (d2EightChildHole base width left right
      (fun k => d2FlowTreeRootDeficit (children k))
      (fun k => (d2FlowTreeRootData (children k)).2.1)
      (fun k => (d2FlowTreeRootData (children k)).2.2) j).1)
    (fun j => (d2EightChildHole base width left right
      (fun k => d2FlowTreeRootDeficit (children k))
      (fun k => (d2FlowTreeRootData (children k)).2.1)
      (fun k => (d2FlowTreeRootData (children k)).2.2) j).2) (by
        simpa [d2FlowNodeStaticHoles] using hfit)
  apply d2FlowNodeStaticHolesClamped_fit_of_child_intervals_contained
    children hwidth hinv hparent
  intro j hunsat
  have hneq : d2FlowTreeRootDeficit (children j) ≠ width := by omega
  simpa [d2EightChildHole, hneq] using hbounds j

/-- The ordinary active-stage fit transfers to the bag-equivalent clamped
hole representation. -/
theorem d2FlowStage_active_ordinary_static_fit_clamped
    {scale h i G low high : Nat} {active : Nat → Bool}
    {role : Nat → D2Role} {quota : Nat → D2Role → Nat}
    {cap : Nat → Nat}
    (children : Fin 8 → D2FlowTree h)
    (htree : d2FlowTreeInv scale (.node G low high children))
    (hinputs : d2FlowStageInvInputs scale active role quota cap i
      (.node G low high children))
    (ha : active i = true)
    (hr : role i = .topRise ∨ role i = .mid ∨ role i = .botDesc) :
    StaticHolesFit (low + quota i (role i) / 2)
      (d2FlowNodeStaticHolesClamped 0 (scale * 8 ^ h)
        (low + quota i (role i) / 2)
        (high + quota i (role i) / 2)
        (fun j => d2FlowTreeChild
          (d2FlowStage active role quota (h + 1) i
            (.node G low high children)) j))
      (8 * (scale * 8 ^ h) - (high + quota i (role i) / 2)) := by
  have hfit := d2FlowStage_active_ordinary_static_fit
    (scale := scale) (h := h) (i := i) (G := G) (low := low)
    (high := high) (active := active) (role := role) (quota := quota)
    (cap := cap) children htree hinputs ha hr
  have hout := d2FlowStage_preserves_inv_of_inputs
    (.node G low high children) htree hinputs
  have hinvOutput : ∀ j, d2FlowTreeInv scale
      (d2FlowTreeChild
        (d2FlowStage active role quota (h + 1) i
          (.node G low high children)) j) := by
    intro j
    rcases hr with htop | hmid | hbot
    · have hout' := hout
      simp only [d2FlowStage, ha, htop, d2FlowTreeInv] at hout'
      simpa [d2FlowTreeChild, d2FlowStage, ha, htop] using hout'.2.2.2 j
    · have hout' := hout
      simp only [d2FlowStage, ha, hmid, d2FlowTreeInv] at hout'
      simpa [d2FlowTreeChild, d2FlowStage, ha, hmid] using hout'.2.2.2 j
    · have hout' := hout
      simp only [d2FlowStage, ha, hbot, d2FlowTreeInv] at hout'
      simpa [d2FlowTreeChild, d2FlowStage, ha, hbot] using hout'.2.2.2 j
  have hclamped := d2FlowNodeStaticHolesClamped_fit_of_static_fit
    (base := 0) (width := scale * 8 ^ h)
    (left := low + quota i (role i) / 2)
    (right := high + quota i (role i) / 2)
    (fun j => d2FlowTreeChild
      (d2FlowStage active role quota (h + 1) i
        (.node G low high children)) j)
    rfl hinvOutput (by simpa using hfit)
  simpa using hclamped

/-- Inward-moving child fronts preserve clamped fit inside a fixed parent.
Any child that becomes saturated is empty; every other new interval lies
inside its old interval, which was already contained in the parent. -/
theorem d2FlowNodeStaticHolesClamped_fit_of_fronts_mono
    {scale h base width left right : Nat}
    (oldChildren newChildren : Fin 8 → D2FlowTree h)
    (hwidth : width = scale * 8 ^ h)
    (hinv : ∀ j, d2FlowTreeInv scale (newChildren j))
    (hdef : ∀ j, d2FlowTreeRootDeficit (oldChildren j) ≤
      d2FlowTreeRootDeficit (newChildren j))
    (hfront : ∀ j,
      (d2FlowTreeRootData (oldChildren j)).2.1 ≤
        (d2FlowTreeRootData (newChildren j)).2.1 ∧
      (d2FlowTreeRootData (oldChildren j)).2.2 ≤
        (d2FlowTreeRootData (newChildren j)).2.2)
    (hfit : StaticHolesFit (base + left)
      (d2FlowNodeStaticHolesClamped base width left right oldChildren)
      (base + 8 * width - right)) :
    StaticHolesFit (base + left)
      (d2FlowNodeStaticHolesClamped base width left right newChildren)
      (base + 8 * width - right) := by
  have hparent := staticHolesFit_parent_order hfit
  have hbounds := staticHoleList_fit_bounds (base + left)
    (base + 8 * width - right)
    (fun j => (d2EightChildHoleClamped base width left right oldChildren j).1)
    (fun j => (d2EightChildHoleClamped base width left right oldChildren j).2) (by
        simpa [d2FlowNodeStaticHolesClamped] using hfit)
  apply d2FlowNodeStaticHolesClamped_fit_of_child_intervals_contained
    newChildren hwidth hinv hparent
  intro j hnew
  have hold : d2FlowTreeRootDeficit (oldChildren j) < width := by
    have hle := hdef j
    have hcap := d2FlowTreeInv_root_native_bound (newChildren j) (hinv j)
    have hcapW : d2FlowTreeRootDeficit (newChildren j) ≤ width := by
      simpa [hwidth] using hcap
    omega
  have holdNe : d2FlowTreeRootDeficit (oldChildren j) ≠ width := by omega
  have hstart := (hbounds j).1
  have hend := (hbounds j).2
  have hstartOld : base + left ≤
      base + j.val * width + (d2FlowTreeRootData (oldChildren j)).2.1 := by
    simpa [d2EightChildHoleClamped, d2EightChildHole, holdNe] using hstart
  have hendOld : base + (j.val + 1) * width -
      (d2FlowTreeRootData (oldChildren j)).2.2 ≤
        base + 8 * width - right := by
    simpa [d2EightChildHoleClamped, d2EightChildHole, holdNe] using hend
  have hnewNe : d2FlowTreeRootDeficit (newChildren j) ≠ width := by omega
  have hlow := (hfront j).1
  have hhigh := (hfront j).2
  constructor
  · have hnewStart : base + left ≤
        base + j.val * width + (d2FlowTreeRootData (newChildren j)).2.1 := by
      exact le_trans hstartOld (Nat.add_le_add_left hlow _)
    simpa [d2EightChildHole, hnewNe] using hnewStart
  · have hnewEnd : base + (j.val + 1) * width -
        (d2FlowTreeRootData (newChildren j)).2.2 ≤
          base + 8 * width - right := by
      apply le_trans ?_ hendOld
      omega
    simpa [d2EightChildHole, hnewNe] using hnewEnd

/-- Monotone child fronts preserve an existing fitted parent hole list. -/
theorem d2FlowNodeStaticHoles_fit_of_child_fronts_mono
    {scale h base width left right : Nat}
    (oldChildren newChildren : Fin 8 -> D2FlowTree h)
    (hwidth : width = scale * 8 ^ h)
    (hinv : forall j, d2FlowTreeInv scale (newChildren j))
    (hdef : forall j, d2FlowTreeRootDeficit (oldChildren j) <=
      d2FlowTreeRootDeficit (newChildren j))
    (hfront : forall j,
      (d2FlowTreeRootData (oldChildren j)).2.1 <=
        (d2FlowTreeRootData (newChildren j)).2.1 ∧
      (d2FlowTreeRootData (oldChildren j)).2.2 <=
        (d2FlowTreeRootData (newChildren j)).2.2)
    (hfit : StaticHolesFit (base + left)
      (d2FlowNodeStaticHoles base width left right oldChildren)
      (base + 8 * width - right))
    (hleft : left <= width) (hright : right <= width)
    (hparent : base + left <= base + 8 * width - right) :
    StaticHolesFit (base + left)
      (d2FlowNodeStaticHoles base width left right newChildren)
      (base + 8 * width - right) := by
  let oldLo : Fin 8 -> Nat := fun j =>
    (d2EightChildHole base width left right
      (fun k => d2FlowTreeRootDeficit (oldChildren k))
      (fun k => (d2FlowTreeRootData (oldChildren k)).2.1)
      (fun k => (d2FlowTreeRootData (oldChildren k)).2.2) j).1
  let oldHi : Fin 8 -> Nat := fun j =>
    (d2EightChildHole base width left right
      (fun k => d2FlowTreeRootDeficit (oldChildren k))
      (fun k => (d2FlowTreeRootData (oldChildren k)).2.1)
      (fun k => (d2FlowTreeRootData (oldChildren k)).2.2) j).2
  let newLo : Fin 8 -> Nat := fun j =>
    (d2EightChildHole base width left right
      (fun k => d2FlowTreeRootDeficit (newChildren k))
      (fun k => (d2FlowTreeRootData (newChildren k)).2.1)
      (fun k => (d2FlowTreeRootData (newChildren k)).2.2) j).1
  let newHi : Fin 8 -> Nat := fun j =>
    (d2EightChildHole base width left right
      (fun k => d2FlowTreeRootDeficit (newChildren k))
      (fun k => (d2FlowTreeRootData (newChildren k)).2.1)
      (fun k => (d2FlowTreeRootData (newChildren k)).2.2) j).2
  have hbounds := staticHoleList_fit_bounds (base + left)
    (base + 8 * width - right) oldLo oldHi (by
      simpa [d2FlowNodeStaticHoles, oldLo, oldHi] using hfit)
  have hslots : forall j, base + j.val * width <= newLo j ∧
      newLo j <= newHi j ∧ newHi j <= base + (j.val + 1) * width := by
    intro j
    have hcap := d2FlowTreeInv_root_native_bound (newChildren j) (hinv j)
    exact d2EightChildHole_within_slot
      (fun k => d2FlowTreeRootDeficit (newChildren k))
      (fun k => (d2FlowTreeRootData (newChildren k)).2.1)
      (fun k => (d2FlowTreeRootData (newChildren k)).2.2)
      hleft hright j (by simpa [hwidth] using hcap) (by
        intro hunsat
        exact d2FlowTreeInv_root_balance (newChildren j) (hinv j)
          (by simpa [hwidth] using hunsat))
  have hfirst : base + left <= newLo ⟨0, by omega⟩ := by
    let j : Fin 8 := ⟨0, by omega⟩
    by_cases hsat : d2FlowTreeRootDeficit (newChildren j) = width
    · have hsat0 : d2FlowTreeRootDeficit
          (newChildren 0) = width := by simpa [j] using hsat
      change base + left <= newLo j
      change base + left <=
        (d2EightChildHole base width left right
          (fun k => d2FlowTreeRootDeficit (newChildren k))
          (fun k => (d2FlowTreeRootData (newChildren k)).2.1)
          (fun k => (d2FlowTreeRootData (newChildren k)).2.2) j).1
      simp [d2EightChildHole, j, hsat0]
    · have holdSat : d2FlowTreeRootDeficit (oldChildren j) ≠ width := by
        intro hold
        have hle := hdef j
        rw [hold] at hle
        have hcap := d2FlowTreeInv_root_native_bound (newChildren j) (hinv j)
        have hcapW : d2FlowTreeRootDeficit (newChildren j) <= width := by
          simpa [hwidth] using hcap
        omega
      have hsat0 : d2FlowTreeRootDeficit
          (newChildren 0) ≠ width := by simpa [j] using hsat
      have holdSat0 : d2FlowTreeRootDeficit (oldChildren 0) ≠ width := by
        simpa [j] using holdSat
      have hlow0 : (d2FlowTreeRootData (oldChildren 0)).2.1 <=
          (d2FlowTreeRootData (newChildren 0)).2.1 := by
        simpa [j] using (hfront j).1
      have hbound := (hbounds (0 : Fin 8)).1
      have hbound' : base + left <=
          base + (d2FlowTreeRootData (oldChildren 0)).2.1 := by
        simpa [oldLo, d2EightChildHole, holdSat0] using hbound
      change base + left <= newLo j
      change base + left <=
        (d2EightChildHole base width left right
          (fun k => d2FlowTreeRootDeficit (newChildren k))
          (fun k => (d2FlowTreeRootData (newChildren k)).2.1)
          (fun k => (d2FlowTreeRootData (newChildren k)).2.2) j).1
      simp [d2EightChildHole, j, hsat0]
      omega
  have hlast : newHi ⟨7, by omega⟩ <= base + 8 * width - right := by
    let j : Fin 8 := ⟨7, by omega⟩
    by_cases hsat : d2FlowTreeRootDeficit (newChildren j) = width
    · have hsat7 : d2FlowTreeRootDeficit
          (newChildren 7) = width := by simpa [j] using hsat
      change newHi j <= base + 8 * width - right
      change (d2EightChildHole base width left right
          (fun k => d2FlowTreeRootDeficit (newChildren k))
          (fun k => (d2FlowTreeRootData (newChildren k)).2.1)
          (fun k => (d2FlowTreeRootData (newChildren k)).2.2) j).2 <=
        base + 8 * width - right
      simp [d2EightChildHole, j, hsat7]
    · have holdSat : d2FlowTreeRootDeficit (oldChildren j) ≠ width := by
        intro hold
        have hle := hdef j
        rw [hold] at hle
        have hcap := d2FlowTreeInv_root_native_bound (newChildren j) (hinv j)
        have hcapW : d2FlowTreeRootDeficit (newChildren j) <= width := by
          simpa [hwidth] using hcap
        omega
      have hsat7 : d2FlowTreeRootDeficit
          (newChildren 7) ≠ width := by simpa [j] using hsat
      have holdSat7 : d2FlowTreeRootDeficit (oldChildren 7) ≠ width := by
        simpa [j] using holdSat
      have hhigh7 : (d2FlowTreeRootData (oldChildren 7)).2.2 <=
          (d2FlowTreeRootData (newChildren 7)).2.2 := by
        simpa [j] using (hfront j).2
      have hbound := (hbounds (7 : Fin 8)).2
      have hboundMid : base + 8 * width -
          (d2FlowTreeRootData (oldChildren 7)).2.2 <=
          base + 8 * width - right := by
        simpa [oldHi, d2EightChildHole, holdSat7] using hbound
      have hbound' : right <= (d2FlowTreeRootData (oldChildren 7)).2.2 := by
        omega
      change newHi j <= base + 8 * width - right
      change (d2EightChildHole base width left right
          (fun k => d2FlowTreeRootDeficit (newChildren k))
          (fun k => (d2FlowTreeRootData (newChildren k)).2.1)
          (fun k => (d2FlowTreeRootData (newChildren k)).2.2) j).2 <=
        base + 8 * width - right
      simp [d2EightChildHole, j, hsat7]
      omega
  apply d2EightChildHolesFit (base := base) (width := width)
    (left := left) (right := right) newLo newHi hleft hright hparent hslots
    hfirst hlast

/-- Child invariants place every hole in its native slot, so global static
fit reduces to the two endpoint holes staying inside the parent interval. -/
theorem d2FlowNodeStaticHoles_fit_of_child_endpoint_bounds
    {scale h base width left right : Nat}
    (children : Fin 8 → D2FlowTree h)
    (hwidth : width = scale * 8 ^ h)
    (hinv : ∀ j, d2FlowTreeInv scale (children j))
    (hleft : left ≤ width) (hright : right ≤ width)
    (hparent : base + left ≤ base + 8 * width - right)
    (hfirst : d2FlowTreeRootDeficit (children 0) = width ∨
      left ≤ (d2FlowTreeRootData (children 0)).2.1)
    (hlast : d2FlowTreeRootDeficit (children 7) = width ∨
      right ≤ (d2FlowTreeRootData (children 7)).2.2) :
    StaticHolesFit (base + left)
      (d2FlowNodeStaticHoles base width left right children)
      (base + 8 * width - right) := by
  let lo : Fin 8 → Nat := fun j =>
    (d2EightChildHole base width left right
      (fun k => d2FlowTreeRootDeficit (children k))
      (fun k => (d2FlowTreeRootData (children k)).2.1)
      (fun k => (d2FlowTreeRootData (children k)).2.2) j).1
  let hi : Fin 8 → Nat := fun j =>
    (d2EightChildHole base width left right
      (fun k => d2FlowTreeRootDeficit (children k))
      (fun k => (d2FlowTreeRootData (children k)).2.1)
      (fun k => (d2FlowTreeRootData (children k)).2.2) j).2
  have hslots : ∀ j, base + j.val * width ≤ lo j ∧
      lo j ≤ hi j ∧ hi j ≤ base + (j.val + 1) * width := by
    intro j
    have hcap := d2FlowTreeInv_root_native_bound (children j) (hinv j)
    exact d2EightChildHole_within_slot
      (fun k => d2FlowTreeRootDeficit (children k))
      (fun k => (d2FlowTreeRootData (children k)).2.1)
      (fun k => (d2FlowTreeRootData (children k)).2.2)
      hleft hright j (by simpa [hwidth] using hcap) (by
        intro hunsat
        exact d2FlowTreeInv_root_balance (children j) (hinv j)
          (by simpa [hwidth] using hunsat))
  have hfirst' : base + left ≤ lo ⟨0, by omega⟩ := by
    by_cases hsat : d2FlowTreeRootDeficit (children 0) = width
    · simp [lo, d2EightChildHole, hsat]
    · have hlow : left ≤ (d2FlowTreeRootData (children 0)).2.1 := by
        rcases hfirst with hs | hl
        · exact (hsat hs).elim
        · exact hl
      simp [lo, d2EightChildHole, hsat]
      omega
  have hlast' : hi ⟨7, by omega⟩ ≤ base + 8 * width - right := by
    by_cases hsat : d2FlowTreeRootDeficit (children 7) = width
    · simp [hi, d2EightChildHole, hsat]
    · have hhigh : right ≤ (d2FlowTreeRootData (children 7)).2.2 := by
        rcases hlast with hs | hh
        · exact (hsat hs).elim
        · exact hh
      simp [hi, d2EightChildHole, hsat]
      omega
  apply d2EightChildHolesFit (base := base) (width := width)
    (left := left) (right := right) lo hi hleft hright hparent hslots
    hfirst' hlast'

/-- An inactive node preserves its static-hole fit when its children take
their recursive stages: their roots only gain deficit and front offsets. -/
theorem d2FlowStage_inactive_node_static_fit
    {scale h i G low high : Nat} {active : Nat → Bool}
    {role : Nat → D2Role} {quota : Nat → D2Role → Nat}
    {cap : Nat → Nat} (children : Fin 8 → D2FlowTree h)
    (htree : d2FlowTreeInv scale (.node G low high children))
    (hfit : StaticHolesFit low
      (d2FlowNodeStaticHolesClamped 0 (scale * 8 ^ h) low high children)
      (8 * (scale * 8 ^ h) - high))
    (hinputs : d2FlowStageInvInputs scale active role quota cap i
      (.node G low high children)) (ha : active i = false) :
    StaticHolesFit low
      (d2FlowNodeStaticHolesClamped 0 (scale * 8 ^ h) low high
        (fun j => d2FlowTreeChild
          (d2FlowStage active role quota (h + 1) i
            (.node G low high children)) j))
      (8 * (scale * 8 ^ h) - high) := by
  let nextChildren : Fin 8 → D2FlowTree h := fun j =>
    d2FlowStage active role quota h (i + 1) (children j)
  have hinvChildren : ∀ j, d2FlowTreeInv scale (children j) := by
    have h := htree
    simp only [d2FlowTreeInv] at h
    exact h.2.2.2
  simp only [d2FlowStageInvInputs] at hinputs
  have hnextInv : ∀ j, d2FlowTreeInv scale (nextChildren j) := by
    intro j
    exact d2FlowStage_preserves_inv_of_inputs (children j)
      (hinvChildren j) (hinputs.1 j)
  have hdef : ∀ j, d2FlowTreeRootDeficit (children j) ≤
      d2FlowTreeRootDeficit (nextChildren j) := by
    intro j
    exact d2FlowStage_root_deficit_mono active role quota (i + 1) (children j)
  have hfront : ∀ j,
      (d2FlowTreeRootData (children j)).2.1 ≤
        (d2FlowTreeRootData (nextChildren j)).2.1 ∧
      (d2FlowTreeRootData (children j)).2.2 ≤
        (d2FlowTreeRootData (nextChildren j)).2.2 := by
    intro j
    exact d2FlowStage_root_fronts_mono active role quota (i + 1) (children j)
  have hfit' := d2FlowNodeStaticHolesClamped_fit_of_fronts_mono
    (base := 0) (width := scale * 8 ^ h) (left := low) (right := high)
    children nextChildren rfl hnextInv hdef hfront
    (by simpa using hfit)
  simpa [nextChildren, d2FlowStage, ha] using hfit'

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

/-- At a bottom-rise step whose child level is inactive, the sender bag is
sent wholly to its parent. Under the post-step fit, this conservation is the
corresponding empty-bag statement for the updated node. -/
theorem d2FlowStage_active_bot_rise_static_bag_empty
    {n scale h i G low high : Nat} {active : Nat → Bool}
    {role : Nat → D2Role} {quota : Nat → D2Role → Nat}
    {cap : Nat → Nat} (children : Fin 8 → D2FlowTree h)
    (htree : d2FlowTreeInv scale (.node G low high children))
    (hinputs : d2FlowStageInvInputs scale active role quota cap i
      (.node G low high children))
    (ha : active i = true) (hr : role i = .botRise)
    (hnext : active (i + 1) = false)
    (hleft : low +
      (d2FlowTotal (fun j => d2FlowTreeRootDeficit (children j)) - G) / 2 ≤
        scale * 8 ^ h)
    (hright : high +
      (d2FlowTotal (fun j => d2FlowTreeRootDeficit (children j)) - G) -
        (d2FlowTotal (fun j => d2FlowTreeRootDeficit (children j)) - G) / 2 ≤
        scale * 8 ^ h)
    (hfirst : d2FlowTreeRootDeficit
        (d2FlowTreeChild (d2FlowStage active role quota (h + 1) i
          (.node G low high children)) 0) = scale * 8 ^ h ∨
      low + (d2FlowTotal (fun j => d2FlowTreeRootDeficit (children j)) - G) / 2 ≤
        (d2FlowTreeRootData (d2FlowTreeChild
          (d2FlowStage active role quota (h + 1) i
            (.node G low high children)) 0)).2.1)
    (hlast : d2FlowTreeRootDeficit
        (d2FlowTreeChild (d2FlowStage active role quota (h + 1) i
          (.node G low high children)) 7) = scale * 8 ^ h ∨
      high + (d2FlowTotal (fun j => d2FlowTreeRootDeficit (children j)) - G) -
          (d2FlowTotal (fun j => d2FlowTreeRootDeficit (children j)) - G) / 2 ≤
        (d2FlowTreeRootData (d2FlowTreeChild
          (d2FlowStage active role quota (h + 1) i
            (.node G low high children)) 7)).2.2)
    (hstop : 8 * (scale * 8 ^ h) -
        (high + (d2FlowTotal (fun j => d2FlowTreeRootDeficit (children j)) - G) -
          (d2FlowTotal (fun j => d2FlowTreeRootDeficit (children j)) - G) / 2) ≤ n) :
    d2FlowNodeStaticBag (n := n) 0 (scale * 8 ^ h)
      (G + (d2FlowTotal (fun j => d2FlowTreeRootDeficit (children j)) - G))
      (low + (d2FlowTotal (fun j => d2FlowTreeRootDeficit (children j)) - G) / 2)
      (high + (d2FlowTotal (fun j => d2FlowTreeRootDeficit (children j)) - G) -
        (d2FlowTotal (fun j => d2FlowTreeRootDeficit (children j)) - G) / 2)
      (fun j => d2FlowTreeChild
        (d2FlowStage active role quota (h + 1) i
          (.node G low high children)) j) = ∅ := by
  let pi := d2FlowTotal (fun j => d2FlowTreeRootDeficit (children j)) - G
  have hcover : G ≤ d2FlowTotal
      (fun j => d2FlowTreeRootDeficit (children j)) := htree.2.1
  have hstage := hinputs.2
  simp only [ha, if_true, hr] at hstage
  have hbalance : low + high = G := hstage.1
  have hsum : d2FlowTotal (fun j => d2FlowTreeRootDeficit
      (d2FlowTreeChild
        (d2FlowStage active role quota (h + 1) i
          (.node G low high children)) j)) = G + pi := by
    calc
      d2FlowTotal (fun j => d2FlowTreeRootDeficit
          (d2FlowTreeChild
            (d2FlowStage active role quota (h + 1) i
              (.node G low high children)) j)) =
          d2FlowTotal (fun j => d2FlowTreeRootDeficit (children j)) := by
        unfold d2FlowTotal
        apply Finset.sum_congr rfl
        intro j hj
        exact d2FlowStage_botRise_child_root_deficit children ha hr hnext j
      _ = G + pi := by simp [pi]; omega
  have hinvChildren : ∀ j, d2FlowTreeInv scale (children j) := by
    have h := htree
    simp only [d2FlowTreeInv] at h
    exact h.2.2.2
  have htotalBound : d2FlowTotal
      (fun j => d2FlowTreeRootDeficit (children j)) ≤
      8 * (scale * 8 ^ h) := by
    unfold d2FlowTotal
    calc
      Finset.univ.sum (fun j : Fin 8 => d2FlowTreeRootDeficit (children j)) ≤
          Finset.univ.sum (fun _ : Fin 8 => scale * 8 ^ h) := by
        apply Finset.sum_le_sum
        intro j hj
        exact d2FlowTreeInv_root_native_bound (children j) (hinvChildren j)
      _ = 8 * (scale * 8 ^ h) := by simp
  have hparent : low + pi / 2 ≤
      8 * (scale * 8 ^ h) - (high + pi - pi / 2) := by
    have hsumFront : low + pi / 2 + (high + pi - pi / 2) =
        d2FlowTotal (fun j => d2FlowTreeRootDeficit (children j)) := by
      simp [pi]
      omega
    omega
  have hfit := d2FlowNodeStaticHoles_fit_of_child_endpoint_bounds
    (base := 0) (width := scale * 8 ^ h) (left := low + pi / 2)
    (right := high + pi - pi / 2)
    (children := fun j => d2FlowTreeChild
      (d2FlowStage active role quota (h + 1) i
        (.node G low high children)) j) rfl
    (by
      intro j
      have hchild := d2FlowStage_preserves_inv_of_inputs (children j)
        (hinvChildren j) (by
          simp only [d2FlowStageInvInputs] at hinputs
          exact hinputs.1 j)
      simpa [d2FlowStage, ha, hr, d2FlowTreeChild] using hchild)
    (by simpa [pi] using hleft) (by simpa [pi] using hright)
    (by simpa [Nat.zero_add, pi] using hparent)
    (by simpa [pi] using hfirst)
    (by simpa [pi] using hlast)
  have houtinv := d2FlowStage_preserves_inv_of_inputs
    (.node G low high children) htree hinputs
  apply d2FlowNodeStaticBag_eq_empty_of_child_total_eq_G
    (base := 0) (G := G + pi)
    (low := low + pi / 2) (high := high + pi - pi / 2)
    (children := fun j => d2FlowTreeChild
      (d2FlowStage active role quota (h + 1) i
        (.node G low high children)) j)
  · simpa [d2FlowStage, ha, hr, pi] using houtinv
  · simpa [Nat.zero_add, pi] using hfit
  · simpa [Nat.zero_add, pi] using hstop
  · simpa [pi] using hsum

/-- Under the endpoint-reserve side conditions used by the bot-rise bag
conservation lemma, its updated child holes also fit in the clamped form. -/
theorem d2FlowStage_active_bot_rise_static_fit_clamped
    {scale h i G low high : Nat} {active : Nat → Bool}
    {role : Nat → D2Role} {quota : Nat → D2Role → Nat}
    {cap : Nat → Nat} (children : Fin 8 → D2FlowTree h)
    (htree : d2FlowTreeInv scale (.node G low high children))
    (hinputs : d2FlowStageInvInputs scale active role quota cap i
      (.node G low high children))
    (ha : active i = true) (hr : role i = .botRise)
    (hleft : low +
      (d2FlowTotal (fun j => d2FlowTreeRootDeficit (children j)) - G) / 2 ≤
        scale * 8 ^ h)
    (hright : high +
      (d2FlowTotal (fun j => d2FlowTreeRootDeficit (children j)) - G) -
        (d2FlowTotal (fun j => d2FlowTreeRootDeficit (children j)) - G) / 2 ≤
        scale * 8 ^ h)
    (hfirst : d2FlowTreeRootDeficit
        (d2FlowTreeChild (d2FlowStage active role quota (h + 1) i
          (.node G low high children)) 0) = scale * 8 ^ h ∨
      low + (d2FlowTotal (fun j => d2FlowTreeRootDeficit (children j)) - G) / 2 ≤
        (d2FlowTreeRootData (d2FlowTreeChild
          (d2FlowStage active role quota (h + 1) i
            (.node G low high children)) 0)).2.1)
    (hlast : d2FlowTreeRootDeficit
        (d2FlowTreeChild (d2FlowStage active role quota (h + 1) i
          (.node G low high children)) 7) = scale * 8 ^ h ∨
      high + (d2FlowTotal (fun j => d2FlowTreeRootDeficit (children j)) - G) -
          (d2FlowTotal (fun j => d2FlowTreeRootDeficit (children j)) - G) / 2 ≤
        (d2FlowTreeRootData (d2FlowTreeChild
          (d2FlowStage active role quota (h + 1) i
            (.node G low high children)) 7)).2.2) :
    StaticHolesFit
      (low + (d2FlowTotal (fun j => d2FlowTreeRootDeficit (children j)) - G) / 2)
      (d2FlowNodeStaticHolesClamped 0 (scale * 8 ^ h)
        (low + (d2FlowTotal (fun j => d2FlowTreeRootDeficit (children j)) - G) / 2)
        (high + (d2FlowTotal (fun j => d2FlowTreeRootDeficit (children j)) - G) -
          (d2FlowTotal (fun j => d2FlowTreeRootDeficit (children j)) - G) / 2)
        (fun j => d2FlowTreeChild
          (d2FlowStage active role quota (h + 1) i
            (.node G low high children)) j))
      (8 * (scale * 8 ^ h) -
        (high + (d2FlowTotal (fun j => d2FlowTreeRootDeficit (children j)) - G) -
          (d2FlowTotal (fun j => d2FlowTreeRootDeficit (children j)) - G) / 2)) := by
  let pi := d2FlowTotal (fun j => d2FlowTreeRootDeficit (children j)) - G
  have hcover : G ≤ d2FlowTotal
      (fun j => d2FlowTreeRootDeficit (children j)) := htree.2.1
  have hbalance : low + high = G := by
    have hs := hinputs.2
    simp only [ha, if_true, hr] at hs
    exact hs.1
  have hinvChildren : ∀ j, d2FlowTreeInv scale (children j) := by
    have hs := htree
    simp only [d2FlowTreeInv] at hs
    exact hs.2.2.2
  have htotalBound : d2FlowTotal
      (fun j => d2FlowTreeRootDeficit (children j)) ≤
      8 * (scale * 8 ^ h) := by
    unfold d2FlowTotal
    calc
      Finset.univ.sum (fun j : Fin 8 => d2FlowTreeRootDeficit (children j)) ≤
          Finset.univ.sum (fun _ : Fin 8 => scale * 8 ^ h) := by
        apply Finset.sum_le_sum
        intro j hj
        exact d2FlowTreeInv_root_native_bound (children j) (hinvChildren j)
      _ = 8 * (scale * 8 ^ h) := by simp
  have hparent : low + pi / 2 ≤
      8 * (scale * 8 ^ h) - (high + pi - pi / 2) := by
    have hpi : G + pi =
        d2FlowTotal (fun j => d2FlowTreeRootDeficit (children j)) := by
      change G + (d2FlowTotal
        (fun j => d2FlowTreeRootDeficit (children j)) - G) = _
      omega
    have hsplit : pi / 2 + (pi - pi / 2) = pi := by omega
    have hsumFront : low + pi / 2 + (high + pi - pi / 2) =
        d2FlowTotal (fun j => d2FlowTreeRootDeficit (children j)) := by
      calc
        low + pi / 2 + (high + pi - pi / 2) =
            (low + high) + (pi / 2 + (pi - pi / 2)) := by omega
        _ = d2FlowTotal (fun j => d2FlowTreeRootDeficit (children j)) := by
          rw [hbalance, hsplit, hpi]
    have hrightCap : high + pi - pi / 2 ≤ 8 * (scale * 8 ^ h) := by
      omega
    exact (Nat.le_sub_iff_add_le hrightCap).2 (by omega)
  have hfit : StaticHolesFit (low + pi / 2)
      (d2FlowNodeStaticHoles 0 (scale * 8 ^ h) (low + pi / 2)
        (high + pi - pi / 2)
        (fun j => d2FlowTreeChild
          (d2FlowStage active role quota (h + 1) i
            (.node G low high children)) j))
      (8 * (scale * 8 ^ h) - (high + pi - pi / 2)) := by
    have hfit' : StaticHolesFit (0 + (low + pi / 2))
        (d2FlowNodeStaticHoles 0 (scale * 8 ^ h) (low + pi / 2)
          (high + pi - pi / 2)
          (fun j => d2FlowTreeChild
            (d2FlowStage active role quota (h + 1) i
              (.node G low high children)) j))
        (0 + 8 * (scale * 8 ^ h) - (high + pi - pi / 2)) := by
      apply d2FlowNodeStaticHoles_fit_of_child_endpoint_bounds
        (base := 0) (width := scale * 8 ^ h) (left := low + pi / 2)
        (right := high + pi - pi / 2)
        (children := fun j => d2FlowTreeChild
          (d2FlowStage active role quota (h + 1) i
            (.node G low high children)) j) rfl
      · intro j
        have hc := d2FlowStage_preserves_inv_of_inputs (children j)
          (hinvChildren j) (by
            have hs := hinputs
            simp only [d2FlowStageInvInputs] at hs
            exact hs.1 j)
        simpa [d2FlowStage, ha, hr, d2FlowTreeChild] using hc
      · simpa [pi] using hleft
      · simpa [pi] using hright
      · simpa [Nat.zero_add, pi] using hparent
      · simpa [pi] using hfirst
      · simpa [pi] using hlast
    simpa [Nat.zero_add, pi] using hfit'
  have hfitClamped := d2FlowNodeStaticHolesClamped_fit_of_static_fit
    (base := 0) (width := scale * 8 ^ h) (left := low + pi / 2)
    (right := high + pi - pi / 2)
    (fun j => d2FlowTreeChild
      (d2FlowStage active role quota (h + 1) i
        (.node G low high children)) j)
    rfl (by
      intro j
      have hc := d2FlowStage_preserves_inv_of_inputs (children j)
        (hinvChildren j) (by
          have hs := hinputs
          simp only [d2FlowStageInvInputs] at hs
          exact hs.1 j)
      simpa [d2FlowStage, ha, hr, d2FlowTreeChild] using hc)
    (by simpa [pi] using hfit)
  simpa [pi] using hfitClamped

/-- A top-descending reset makes every child hole its full native slot, so the
clamped hole list fits exactly across the parent. -/
theorem d2FlowStage_active_top_desc_static_fit_clamped
    {scale h i G low high : Nat} {active : Nat → Bool}
    {role : Nat → D2Role} {quota : Nat → D2Role → Nat}
    (children : Fin 8 → D2FlowTree h)
    (ha : active i = true) (hr : role i = .topDesc)
    (hwidth : 0 < scale * 8 ^ h) :
    StaticHolesFit 0
      (d2FlowNodeStaticHolesClamped 0 (scale * 8 ^ h) 0 0
        (fun j => d2FlowTreeChild
          (d2FlowStage active role quota (h + 1) i
            (.node G low high children)) j))
      (8 * (scale * 8 ^ h)) := by
  let postChildren : Fin 8 → D2FlowTree h := fun j =>
    d2FlowTreeChild (d2FlowStage active role quota (h + 1) i
      (.node G low high children)) j
  have hpostG (j : Fin 8) : d2FlowTreeRootDeficit (postChildren j) = 0 := by
    simp [postChildren, d2FlowStage, ha, hr, d2FlowTreeChild,
      d2FlowTreeSetRoot_deficit]
  have hpostData (j : Fin 8) : d2FlowTreeRootData (postChildren j) =
      (0, 0, 0) := by
    simp [postChildren, d2FlowStage, ha, hr, d2FlowTreeChild,
      d2FlowTreeRootData_setRoot]
  have hscale : scale ≠ 0 := by
    intro hs
    subst scale
    simp at hwidth
  let width := scale * 8 ^ h
  let lo : Fin 8 → Nat := fun j =>
    (d2EightChildHoleClamped 0 width 0 0 postChildren j).1
  let hi : Fin 8 → Nat := fun j =>
    (d2EightChildHoleClamped 0 width 0 0 postChildren j).2
  have hslot (j : Fin 8) : lo j = j.val * width ∧
      hi j = (j.val + 1) * width := by
    have hnot : d2FlowTreeRootDeficit (postChildren j) ≠ width := by
      rw [hpostG j]
      omega
    simp [lo, hi, width, d2EightChildHoleClamped, d2EightChildHole,
      hpostG, hpostData, hnot, hscale]
  have hfit := staticHoleList_fits 0 (8 * width) lo hi (by omega)
    (by
      intro j
      rw [(hslot j).1]
      exact Nat.zero_le _)
    (by
      intro j
      rw [(hslot j).1, (hslot j).2]
      exact Nat.mul_le_mul_right width (Nat.le_succ j.val))
    (by
      intro j
      rw [(hslot j).2]
      exact Nat.mul_le_mul_right width (by omega))
    (by
      intro j k hjk
      rw [(hslot j).2, (hslot k).1]
      exact Nat.mul_le_mul_right width (Nat.succ_le_of_lt hjk))
  simpa [width, lo, hi, postChildren, d2FlowNodeStaticHolesClamped] using hfit

/-- The startup top-descending reset also leaves no residual parent bag:
its eight children occupy the full parent interval. -/
theorem d2FlowStage_active_top_desc_static_bag_empty
    {n scale h i G low high : Nat} {active : Nat → Bool}
    {role : Nat → D2Role} {quota : Nat → D2Role → Nat}
    {cap : Nat → Nat} (children : Fin 8 → D2FlowTree h)
    (htree : d2FlowTreeInv scale (.node G low high children))
    (hinputs : d2FlowStageInvInputs scale active role quota cap i
      (.node G low high children))
    (ha : active i = true) (hr : role i = .topDesc)
    (hwidth : 0 < scale * 8 ^ h) (hstop : 8 * (scale * 8 ^ h) ≤ n) :
    d2FlowNodeStaticBag (n := n) 0 (scale * 8 ^ h) 0 0 0
      (fun j => d2FlowTreeChild
        (d2FlowStage active role quota (h + 1) i
          (.node G low high children)) j) = ∅ := by
  have hstage := hinputs.2
  simp only [ha, if_true, hr] at hstage
  rcases hstage with ⟨hbalance, hG⟩
  have hlow : low = 0 := by omega
  have hhigh : high = 0 := by omega
  have houtinv := d2FlowStage_preserves_inv_of_inputs
    (.node G low high children) htree hinputs
  let postChildren : Fin 8 → D2FlowTree h := fun j =>
    d2FlowTreeChild (d2FlowStage active role quota (h + 1) i
      (.node G low high children)) j
  have hpostG (j : Fin 8) : d2FlowTreeRootDeficit (postChildren j) = 0 := by
    simp [postChildren, d2FlowStage, ha, hr, d2FlowTreeChild,
      d2FlowTreeSetRoot_deficit]
  have hpostData (j : Fin 8) : d2FlowTreeRootData (postChildren j) =
      (0, 0, 0) := by
    simp [postChildren, d2FlowStage, ha, hr, d2FlowTreeChild,
      d2FlowTreeRootData_setRoot]
  have hsum : d2FlowTotal (fun j => d2FlowTreeRootDeficit (postChildren j)) = 0 := by
    simp [d2FlowTotal, hpostG]
  have hfit : StaticHolesFit 0
      (d2FlowNodeStaticHoles 0 (scale * 8 ^ h) 0 0 postChildren)
      (8 * (scale * 8 ^ h)) := by
    let width := scale * 8 ^ h
    let lo : Fin 8 → Nat := fun j =>
      (d2EightChildHole 0 width 0 0
        (fun k => d2FlowTreeRootDeficit (postChildren k))
        (fun _ => 0) (fun _ => 0) j).1
    let hi : Fin 8 → Nat := fun j =>
      (d2EightChildHole 0 width 0 0
        (fun k => d2FlowTreeRootDeficit (postChildren k))
        (fun _ => 0) (fun _ => 0) j).2
    have hslot (j : Fin 8) : lo j = j.val * width ∧
        hi j = (j.val + 1) * width := by
      have hnot : d2FlowTreeRootDeficit (postChildren j) ≠ width := by
        rw [hpostG j]
        omega
      simp [lo, hi, width, d2EightChildHole, hnot]
    have hfit' := staticHoleList_fits 0 (8 * width) lo hi
      (by omega)
      (by intro j; rw [(hslot j).1]; exact Nat.zero_le _)
      (by
        intro j
        rw [(hslot j).1, (hslot j).2]
        exact Nat.mul_le_mul_right width (Nat.le_succ j.val))
      (by
        intro j
        rw [(hslot j).2]
        exact Nat.mul_le_mul_right width (by omega))
      (by
        intro j k hjk
        rw [(hslot j).2, (hslot k).1]
        exact Nat.mul_le_mul_right width (Nat.succ_le_of_lt hjk))
    simpa [width, lo, hi, d2FlowNodeStaticHoles, hpostG, hpostData] using hfit'
  apply d2FlowNodeStaticBag_eq_empty_of_child_total_eq_G
    (base := 0) (G := 0) (low := 0) (high := 0)
    (children := postChildren)
  · simpa [postChildren, d2FlowStage, ha, hr, hG, hlow, hhigh] using houtinv
  · simpa [Nat.zero_add] using hfit
  · simpa using hstop
  · exact hsum

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
