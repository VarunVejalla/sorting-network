import D2DynamicSenderCardinality

/-! Recursive sender-set representation for the D2 physical routing. -/

namespace Chvatal.D2OrdinaryRankRouting

universe u

/-- One actual wire set at every node of the finite flow tree. -/
inductive D2SenderLayout (Wire : Type u) [DecidableEq Wire] :
    Nat -> Type (u + 1)
  | leaf (bag : Finset Wire) : D2SenderLayout Wire 0
  | node {h : Nat} (bag : Finset Wire)
      (children : Fin 8 -> D2SenderLayout Wire h) : D2SenderLayout Wire (h + 1)

/-- The parent and child pieces emitted by one active sender. -/
structure D2SenderPorts (Wire : Type*) [DecidableEq Wire] where
  up : Finset Wire
  down : Fin 8 -> Finset Wire

def d2SenderLayoutRootBag {Wire : Type*} [DecidableEq Wire] :
    {h : Nat} -> D2SenderLayout Wire h -> Finset Wire
  | 0, .leaf bag => bag
  | _ + 1, .node bag _ => bag

def d2SenderLayoutWires {Wire : Type*} [DecidableEq Wire] :
    {h : Nat} -> D2SenderLayout Wire h -> Finset Wire
  | 0, .leaf bag => bag
  | _ + 1, .node bag children =>
      bag ∪ Finset.univ.biUnion (fun j => d2SenderLayoutWires (children j))

/-- Replace a node's own set while preserving all child layouts. -/
def d2SenderLayoutSetRoot {Wire : Type*} [DecidableEq Wire] :
    {h : Nat} -> D2SenderLayout Wire h -> Finset Wire -> D2SenderLayout Wire h
  | 0, .leaf _, bag => .leaf bag
  | _ + 1, .node _ children, bag => .node bag children

/-- Process children before the current node, as in `d2FlowStage`.

An inactive node keeps its own set and absorbs child up-ports. An active node
clears its own set, adds down-ports to the recursively updated children, and
returns its up-port. At leaves the bag is retained; the candidate schedule's
leaf-inactivity theorem ensures this branch is used only when inactive. -/
def d2SenderLayoutStage {Wire : Type*} [DecidableEq Wire]
    (active : Nat -> Bool)
    (split : Nat -> Finset Wire -> D2SenderPorts Wire) :
    (h : Nat) -> (level : Nat) -> D2SenderLayout Wire h ->
      Prod (D2SenderLayout Wire h) (Finset Wire)
  | 0, _, .leaf bag => (.leaf bag, Finset.empty)
  | h + 1, level, .node bag children => by
      classical
      let routed : Fin 8 -> Prod (D2SenderLayout Wire h) (Finset Wire) := fun j =>
        d2SenderLayoutStage active split h (level + 1) (children j)
      let updatedChildren : Fin 8 -> D2SenderLayout Wire h := fun j =>
        if active level then
          d2SenderLayoutSetRoot (routed j).1
            ((d2SenderLayoutRootBag (routed j).1) ∪
              (split level bag).down j)
        else (routed j).1
      exact if active level then
        (.node Finset.empty updatedChildren, (split level bag).up)
      else
        (.node (bag ∪
          (Finset.univ.biUnion fun j => (routed j).2)) updatedChildren,
          Finset.empty)

@[simp] theorem d2SenderLayoutStage_leaf {Wire : Type*} [DecidableEq Wire]
    (active : Nat -> Bool)
    (split : Nat -> Finset Wire -> D2SenderPorts Wire) (level : Nat)
    (bag : Finset Wire) :
    d2SenderLayoutStage active split 0 level (.leaf bag) =
      (.leaf bag, Finset.empty) := rfl

theorem d2SenderLayoutStage_node_active {Wire : Type*} [DecidableEq Wire]
    {h : Nat} (active : Nat -> Bool)
    (split : Nat -> Finset Wire -> D2SenderPorts Wire) (level : Nat)
    (bag : Finset Wire) (children : Fin 8 -> D2SenderLayout Wire h)
    (ha : active level = true) :
    d2SenderLayoutRootBag
        (d2SenderLayoutStage active split (h + 1) level
          (.node bag children)).1 = Finset.empty /\
      (d2SenderLayoutStage active split (h + 1) level
        (.node bag children)).2 = (split level bag).up := by
  classical
  simp [d2SenderLayoutStage, ha, d2SenderLayoutRootBag]

theorem d2SenderLayoutStage_node_inactive {Wire : Type*} [DecidableEq Wire]
    {h : Nat} (active : Nat -> Bool)
    (split : Nat -> Finset Wire -> D2SenderPorts Wire) (level : Nat)
    (bag : Finset Wire) (children : Fin 8 -> D2SenderLayout Wire h)
    (ha : active level = false) :
    d2SenderLayoutRootBag
        (d2SenderLayoutStage active split (h + 1) level
          (.node bag children)).1 =
        bag ∪ Finset.univ.biUnion (fun j =>
          (d2SenderLayoutStage active split h (level + 1) (children j)).2) /\
      (d2SenderLayoutStage active split (h + 1) level
        (.node bag children)).2 = Finset.empty := by
  classical
  simp [d2SenderLayoutStage, ha, d2SenderLayoutRootBag]

theorem d2SenderLayoutStage_up_empty_of_inactive {Wire : Type*}
    [DecidableEq Wire] (active : Nat -> Bool)
    (split : Nat -> Finset Wire -> D2SenderPorts Wire) {h : Nat}
    (level : Nat) (layout : D2SenderLayout Wire h)
    (ha : active level = false) :
    (d2SenderLayoutStage active split h level layout).2 = Finset.empty := by
  cases h <;> cases layout <;> simp [d2SenderLayoutStage, ha]

@[simp] theorem d2SenderLayoutRootBag_setRoot {Wire : Type*} [DecidableEq Wire]
    {h : Nat} (layout : D2SenderLayout Wire h) (bag : Finset Wire) :
    d2SenderLayoutRootBag (d2SenderLayoutSetRoot layout bag) = bag := by
  cases layout <;> rfl

theorem d2SenderLayoutWires_setRoot_union {Wire : Type*} [DecidableEq Wire]
    {h : Nat} (layout : D2SenderLayout Wire h) (extra : Finset Wire) :
    d2SenderLayoutWires
        (d2SenderLayoutSetRoot layout
          (d2SenderLayoutRootBag layout ∪ extra)) =
      d2SenderLayoutWires layout ∪ extra := by
  cases layout <;>
    simp [d2SenderLayoutWires, d2SenderLayoutSetRoot,
      d2SenderLayoutRootBag, Finset.union_assoc, Finset.union_left_comm,
      Finset.union_comm]

end Chvatal.D2OrdinaryRankRouting
