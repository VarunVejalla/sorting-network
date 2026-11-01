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
