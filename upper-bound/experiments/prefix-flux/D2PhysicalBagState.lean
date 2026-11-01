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

end Chvatal.D2PhysicalBagState
