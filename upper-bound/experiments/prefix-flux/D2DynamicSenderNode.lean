import D2DynamicSenderCardinality
import D2DynamicSenderLayout
import D2FlowPathLast
import D2NativePathIntervals
import D2PhysicalBagState

/-! A finite flat index for every node of a full D2 flow tree. -/

namespace Chvatal.D2OrdinaryRankRouting

open Chvatal
open Chvatal.D2Reserve
open Chvatal.D2NativePathIntervals
open Chvatal.D2PhysicalBagState
open Chvatal.D2StaticWireSets

noncomputable instance instD2FlowPathDecidableEq (n : Nat) :
    DecidableEq (D2FlowPath n) := Classical.decEq _

def d2FlowPathSuccEquiv (n : Nat) :
    D2FlowPath (n + 1) ≃ (Fin 8 × D2FlowPath n) where
  toFun
    | .cons j tail => (j, tail)
  invFun
    | (j, tail) => .cons j tail
  left_inv
    | .cons _ _ => rfl
  right_inv
    | (_, _) => rfl

noncomputable def d2FlowPathFintype : (n : Nat) -> Fintype (D2FlowPath n)
  | 0 => Fintype.ofEquiv (Fin 1) {
      toFun := fun _ => D2FlowPath.nil
      invFun := fun _ => 0
      left_inv := by intro p; apply Fin.ext; omega
      right_inv := by intro p; cases p; rfl
    }
  | n + 1 => by
      letI := d2FlowPathFintype n
      exact Fintype.ofEquiv (Fin 8 × D2FlowPath n)
        (d2FlowPathSuccEquiv n).symm

abbrev D2SenderNode (depth : Nat) :=
  Sigma fun level : Fin (depth + 1) => D2FlowPath level.val

/-- The unique level-zero node. -/
def d2SenderNodeRoot (depth : Nat) : D2SenderNode depth :=
  ⟨⟨0, Nat.zero_lt_succ depth⟩, D2FlowPath.nil⟩

noncomputable instance instD2SenderNodeFintype (depth : Nat) :
    Fintype (D2SenderNode depth) := by
  classical
  letI (n : Nat) : Fintype (D2FlowPath n) := d2FlowPathFintype n
  infer_instance

noncomputable instance instD2SenderNodeDecidableEq (depth : Nat) :
    DecidableEq (D2SenderNode depth) := Classical.decEq _

/-- Remove the final edge from a root-first path. -/
def d2FlowPathInit : (n : Nat) -> D2FlowPath (n + 1) -> D2FlowPath n
  | 0, .cons _ .nil => .nil
  | n + 1, .cons j tail => .cons j (d2FlowPathInit n tail)

/-- The final edge of a root-first path. -/
def d2FlowPathLast : (n : Nat) -> D2FlowPath (n + 1) -> Fin 8
  | 0, .cons j .nil => j
  | n + 1, .cons _ tail => d2FlowPathLast n tail

/-- The parent of a nonroot node; the root has no parent. -/
def d2SenderNodeParent? {depth : Nat} (node : D2SenderNode depth) :
    Option (D2SenderNode depth) := by
  rcases node with ⟨level, path⟩
  cases level with
  | mk n hn =>
      cases n with
      | zero => exact none
      | succ n =>
          exact some ⟨⟨n, by omega⟩, d2FlowPathInit n path⟩

theorem d2SenderNodeParent?_eq_none_iff {depth : Nat}
    (node : D2SenderNode depth) :
    d2SenderNodeParent? node = none ↔ node.1.val = 0 := by
  rcases node with ⟨⟨level, hlevel⟩, path⟩
  cases level with
  | zero => simp [d2SenderNodeParent?]
  | succ level => simp [d2SenderNodeParent?]

/-- The child at port `j`, if it lies within the finite tree. -/
def d2SenderNodeChild? {depth : Nat} (node : D2SenderNode depth)
    (j : Fin 8) : Option (D2SenderNode depth) := by
  rcases node with ⟨level, path⟩
  by_cases hlt : level.val < depth
  · exact some ⟨⟨level.val + 1, by omega⟩,
      d2FlowPathSnoc path j⟩
  · exact none

theorem d2SenderNodeChild?_eq_none_iff {depth : Nat}
    (node : D2SenderNode depth) (j : Fin 8) :
    d2SenderNodeChild? node j = none ↔ node.1.val = depth := by
  unfold d2SenderNodeChild?
  by_cases hlt : node.1.val < depth
  · constructor
    · intro h
      simp [hlt] at h
    · intro heq
      omega
  · constructor
    · intro _
      omega
    · intro heq
      simp [hlt]

/-- The recursive flow state at a flat sender index. -/
def d2SenderNodeSubtree {depth : Nat} (tree : D2FlowTree depth)
    (node : D2SenderNode depth) : D2FlowTree (depth - node.1.val) := by
  let level := node.1.val
  have hle : level ≤ depth := by omega
  have heq : (depth - level) + level = depth := Nat.sub_add_cancel hle
  let fullTree : D2FlowTree ((depth - level) + level) :=
    cast (congrArg D2FlowTree heq.symm) tree
  exact d2FlowTreeAtPath level fullTree node.2

/-- The root bag at a flat path in a recursive sender layout. -/
def d2SenderLayoutBagAtPath {Wire : Type*} [DecidableEq Wire] :
    (n : Nat) -> {h : Nat} -> D2SenderLayout Wire (h + n) ->
      D2FlowPath n -> Finset Wire
  | 0, _, layout, .nil => d2SenderLayoutRootBag layout
  | n + 1, _, .node _ children, .cons j tail =>
      d2SenderLayoutBagAtPath n (children j) tail

/-- A sender bag indexed by the same flat node type as the abstract flow. -/
def d2SenderNodeBag {Wire : Type*} [DecidableEq Wire] {depth : Nat}
    (layout : D2SenderLayout Wire depth) (node : D2SenderNode depth) :
    Finset Wire := by
  let level := node.1.val
  have hle : level ≤ depth := by omega
  have heq : (depth - level) + level = depth := Nat.sub_add_cancel hle
  let fullLayout : D2SenderLayout Wire ((depth - level) + level) :=
    cast (congrArg (D2SenderLayout Wire) heq.symm) layout
  exact d2SenderLayoutBagAtPath level fullLayout node.2

/-- The physical address bag represented by one flow subtree. Leaves use
their native interval; internal nodes use the checked static-hole bag. -/
def d2FlowTreePhysicalBag {n scale : Nat} :
    (base : Nat) -> {h : Nat} -> D2FlowTree h -> Finset (Fin n)
  | base, 0, .leaf G low high =>
      if G = scale then Finset.empty else
        staticWireInterval (base + low) (base + scale - high)
  | base, h + 1, .node G low high children =>
      d2FlowNodeStaticBag base (scale * 8 ^ h) G low high children

/-- Recursive sender layout obtained from the concrete static physical bags. -/
def d2FlowTreePhysicalLayout {n scale : Nat} :
    (base : Nat) -> {h : Nat} -> D2FlowTree h ->
      D2SenderLayout (Fin n) h
  | base, 0, tree => .leaf (d2FlowTreePhysicalBag (scale := scale) base tree)
  | base, h + 1, .node G low high children =>
      .node (d2FlowTreePhysicalBag (scale := scale) base (.node G low high children))
        (fun j => d2FlowTreePhysicalLayout (n := n) (scale := scale)
          (base + j.val * (scale * 8 ^ h)) (children j))

theorem d2FlowTreePhysicalBag_full_eq_empty {n scale : Nat}
    (base h : Nat) :
    d2FlowTreePhysicalBag (n := n) (scale := scale) base
      (d2FlowTreeFull scale h) = Finset.empty := by
  induction h with
  | zero => simp [d2FlowTreePhysicalBag, d2FlowTreeFull]
  | succ h ih =>
      have hsat : scale * 8 ^ (h + 1) = 8 * (scale * 8 ^ h) := by
        rw [Nat.pow_succ]
        ring
      simp [d2FlowTreePhysicalBag, d2FlowTreeFull, d2FlowNodeStaticBag,
        hsat]
      rfl

theorem d2FlowTreePhysicalLayout_full_wires_eq_empty {n scale : Nat}
    (base h : Nat) :
    d2SenderLayoutWires
      (d2FlowTreePhysicalLayout (n := n) (scale := scale) base
        (d2FlowTreeFull scale h)) = Finset.empty := by
  induction h generalizing base with
  | zero =>
      simp [d2FlowTreePhysicalLayout, d2FlowTreePhysicalBag,
        d2FlowTreeFull]
      rfl
  | succ h ih =>
      have hroot : d2FlowTreePhysicalBag (n := n) (scale := scale) base
          (d2FlowTreeFull scale (h + 1)) = Finset.empty :=
        d2FlowTreePhysicalBag_full_eq_empty base (h + 1)
      have hroot' : d2FlowTreePhysicalBag (n := n) (scale := scale) base
          (.node (scale * 8 ^ (h + 1)) 0 0
            (fun _ => d2FlowTreeFull scale h)) = Finset.empty := by
        simpa [d2FlowTreeFull] using hroot
      simp only [d2FlowTreePhysicalLayout, d2FlowTreeFull,
        d2SenderLayoutWires]
      rw [hroot']
      simp [ih]

/-- The static physical sender set at a flat node index, using the base-eight
native address of its path. -/
def d2SenderNodePhysicalBag {n scale depth : Nat}
    (tree : D2FlowTree depth) (node : D2SenderNode depth) : Finset (Fin n) :=
  d2FlowTreePhysicalBag (scale := scale)
    (nativePathStart scale (depth - node.1.val) node.2)
    (d2SenderNodeSubtree tree node)

theorem d2SenderNodePhysicalBag_root {n scale depth : Nat}
    (tree : D2FlowTree depth) :
    d2SenderNodePhysicalBag (n := n) (scale := scale) tree
      (d2SenderNodeRoot depth) =
      d2FlowTreePhysicalBag (n := n) (scale := scale) 0 tree := by
  simp [d2SenderNodePhysicalBag, d2SenderNodeSubtree, d2SenderNodeRoot,
    nativePathStart, D2NativePathIntervals.pathIndex, d2FlowTreeAtPath]

/-- Initially, the root's static sender bag is the complete wire universe. -/
theorem d2SenderNodePhysicalBag_initial_root_eq_univ (scale depth : Nat) :
    d2SenderNodePhysicalBag (n := scale * 8 ^ depth) (scale := scale)
      (d2FlowTreeInitial scale depth) (d2SenderNodeRoot depth) = Finset.univ := by
  rw [d2SenderNodePhysicalBag_root]
  cases depth with
  | zero =>
      by_cases hscale : scale = 0
      · subst scale
        ext w
        exact Fin.elim0 w
      · have hzero : 0 ≠ scale := Ne.symm hscale
        ext w
        simp [d2FlowTreePhysicalBag, d2FlowTreeInitial, hzero,
          staticWireInterval, Nat.pow_zero]
        omega
  | succ depth =>
      by_cases hscale : scale = 0
      · subst scale
        have hzero : 0 * 8 ^ (depth + 1) = 0 := Nat.zero_mul _
        ext w
        exact Fin.elim0 (Fin.cast hzero w)
      · let width := scale * 8 ^ depth
        let children : Fin 8 → D2FlowTree depth := fun _ =>
          d2FlowTreeFull scale depth
        have hfit := d2FlowFullChildren_static_holes_fit scale depth
        have hchildInv : ∀ j, d2FlowTreeInv scale (children j) := by
          intro j
          exact d2FlowTreeFull_inv scale depth
        have hfit' : StaticHolesFit (0 + 0)
            (d2FlowNodeStaticHoles 0 width 0 0 children)
            (0 + 8 * width - 0) := by
          simpa [width] using hfit
        have hstop : 8 * width ≤ scale * 8 ^ (depth + 1) := by
          simp [width, Nat.pow_succ, Nat.mul_assoc, Nat.mul_comm,
            Nat.mul_left_comm]
        have hstop' : 0 + 8 * width - 0 ≤ scale * 8 ^ (depth + 1) := by
          simpa using hstop
        have hholesCard := d2FlowNodeStaticHoles_card (n := scale * 8 ^ (depth + 1))
          (scale := scale) (base := 0) (low := 0) (high := 0) children
          hchildInv hfit' hstop'
        have hchildrenMass : d2FlowTotal
            (fun j => d2FlowTreeRootDeficit (children j)) = 8 * width := by
          simp [d2FlowTotal, children, width, d2FlowTreeFull_root_deficit]
        have hholesEmpty : staticHoleUnion (n := scale * 8 ^ (depth + 1))
            (d2FlowNodeStaticHoles 0 width 0 0 children) = Finset.empty := by
          have hcard : (staticHoleUnion (n := scale * 8 ^ (depth + 1))
              (d2FlowNodeStaticHoles 0 width 0 0 children)).card = 0 := by
            rw [hholesCard, hchildrenMass]
            omega
          exact Finset.card_eq_zero.mp hcard
        have hwidth : 0 < width := by
          have hpow : 0 < 8 ^ depth := by positivity
          have hscalePos : 0 < scale := Nat.pos_of_ne_zero hscale
          exact Nat.mul_pos hscalePos hpow
        have hnotSat : 0 ≠ 8 * width := by omega
        change d2FlowNodeStaticBag (n := scale * 8 ^ (depth + 1))
          0 width 0 0 0 children = Finset.univ
        rw [d2FlowNodeStaticBag, if_neg hnotSat, hholesEmpty]
        have hnative : 8 * width = scale * 8 ^ (depth + 1) := by
          simp only [width, Nat.pow_succ]
          ring
        rw [hnative]
        classical
        ext w
        simp [staticWireInterval]
        intro hw
        exact (Finset.not_nonempty_iff_eq_empty.mpr rfl) ⟨w, hw⟩

theorem d2FlowTreePhysicalLayout_initial_wires_eq_univ (scale depth : Nat) :
    d2SenderLayoutWires
      (d2FlowTreePhysicalLayout (n := scale * 8 ^ depth) (scale := scale) 0
        (d2FlowTreeInitial scale depth)) = Finset.univ := by
  have hroot := d2SenderNodePhysicalBag_initial_root_eq_univ scale depth
  rw [d2SenderNodePhysicalBag_root] at hroot
  cases depth with
  | zero =>
      simpa [d2FlowTreePhysicalLayout, d2FlowTreeInitial,
        d2SenderLayoutWires] using hroot
  | succ depth =>
      have hroot' : d2FlowTreePhysicalBag (n := scale * 8 ^ (depth + 1))
          (scale := scale) 0
          (.node 0 0 0 (fun _ => d2FlowTreeFull scale depth)) = Finset.univ := by
        simpa [d2FlowTreeInitial] using hroot
      simp only [d2FlowTreePhysicalLayout, d2FlowTreeInitial,
        d2SenderLayoutWires]
      rw [hroot']
      simp [d2FlowTreePhysicalLayout_full_wires_eq_empty]

/-- Port labels for one sender: its parent/output port, or one of its eight
child ports. -/
abbrev D2SenderRoutePort := Option (Fin 8)

/-- The parent piece (`none`) and child pieces (`some j`) of a sender. -/
def d2SenderPortsLocalPiece {Wire : Type*} [DecidableEq Wire]
    (ports : D2SenderPorts Wire) (port : D2SenderRoutePort) : Finset Wire :=
  match port with
  | none => ports.up
  | some j => ports.down j

/-- The receiver of a local port. `none` as a receiver is the external
boundary: the root's parent output or a child below the represented tree. -/
def d2SenderNodeRouteTarget {depth : Nat} (active : Nat → Bool)
    (node : D2SenderNode depth) (port : D2SenderRoutePort) :
    Option (D2SenderNode depth) :=
  if active node.1.val then
    match port with
    | none => d2SenderNodeParent? node
    | some j => d2SenderNodeChild? node j
  else some node

/-- Local rank pieces, with an inactive node's entire bag treated as its
retained self piece on the parent-port label. -/
def d2SenderNodeLocalPiece {Wire : Type*} [DecidableEq Wire]
    {depth : Nat} (active : Nat → Bool)
    (source : D2SenderNode depth → Finset Wire)
    (split : D2SenderNode depth → D2SenderPorts Wire)
    (node : D2SenderNode depth) (port : D2SenderRoutePort) : Finset Wire :=
  if active node.1.val then
    d2SenderPortsLocalPiece (split node) port
  else
    match port with
    | none => source node
    | some _ => Finset.empty

/-- An explicit parent-plus-eight-child partition gives the local port
contract consumed by the flat routing theorem. -/
theorem d2SenderPorts_partition_contract {Wire : Type*}
    [DecidableEq Wire] (source : Finset Wire) (ports : D2SenderPorts Wire)
    (hparentSubset : ports.up ⊆ source)
    (hchildSubset : ∀ j, ports.down j ⊆ source)
    (hcover : ports.up ∪ Finset.univ.biUnion ports.down = source)
    (hparentDisjoint : Disjoint ports.up
      (Finset.univ.biUnion ports.down))
    (hchildDisjoint : ∀ j j', j ≠ j' →
      Disjoint (ports.down j) (ports.down j')) :
    (∀ port, d2SenderPortsLocalPiece ports port ⊆ source) ∧
      Finset.univ.biUnion (d2SenderPortsLocalPiece ports) = source ∧
      (∀ port port', port ≠ port' →
        Disjoint (d2SenderPortsLocalPiece ports port)
          (d2SenderPortsLocalPiece ports port')) := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · intro port
    cases port with
    | none => simpa [d2SenderPortsLocalPiece] using hparentSubset
    | some j => simpa [d2SenderPortsLocalPiece] using hchildSubset j
  · ext x
    constructor
    · intro hx
      rcases Finset.mem_biUnion.mp hx with ⟨port, _, hxport⟩
      have hxUnion : x ∈ ports.up ∪ Finset.univ.biUnion ports.down := by
        cases port with
        | none => exact Finset.mem_union_left _ hxport
        | some j =>
            exact Finset.mem_union_right _
              (Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ _, hxport⟩)
      exact hcover ▸ hxUnion
    · intro hx
      have hx' : x ∈ ports.up ∪ Finset.univ.biUnion ports.down := by
        simpa [hcover] using hx
      rcases Finset.mem_union.mp hx' with hparent | hchild
      · exact Finset.mem_biUnion.mpr ⟨none, Finset.mem_univ _, hparent⟩
      · rcases Finset.mem_biUnion.mp hchild with ⟨j, _, hj⟩
        exact Finset.mem_biUnion.mpr ⟨some j, Finset.mem_univ _, hj⟩
  · intro port port' hne
    cases port with
    | none =>
        cases port' with
        | none => exact (hne rfl).elim
        | some j =>
            rw [Finset.disjoint_left]
            intro x hx hxj
            exact Finset.disjoint_left.mp hparentDisjoint hx
              (Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ _, hxj⟩)
    | some j =>
        cases port' with
        | none =>
            rw [Finset.disjoint_left]
            intro x hxj hx
            exact Finset.disjoint_left.mp hparentDisjoint hx
              (Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ _, hxj⟩)
        | some j' =>
            have hj : j ≠ j' := by
              intro heq
              apply hne
              rw [heq]
            exact hchildDisjoint j j' hj

/-- Package the existing ordinary rank cuts as the parent/eight-child port
record consumed by the flat route. -/
def d2OrdinaryRankSenderPorts {n : Nat} (s : Finset (Fin n))
    (boundary : Nat → Nat) (left rightStart : Nat) :
    D2SenderPorts (Fin n) where
  up := Chvatal.blockOf s 0 left ∪ Chvatal.blockOf s rightStart s.card
  down j := Chvatal.blockOf s (left + boundary j.val)
    (left + boundary (j.val + 1))

/-- The ordinary rank-cut cover/disjointness theorem supplies the exact local
partition contract for `d2SenderPorts_partition_contract`. -/
theorem d2OrdinaryRankSenderPorts_contract {n : Nat}
    (s : Finset (Fin n)) (boundary : Nat → Nat) (left rightStart : Nat)
    (hcover :
      Chvatal.blockOf s 0 left ∪
        ((Finset.univ.biUnion fun j : Fin 8 =>
          Chvatal.blockOf s (left + boundary j.val)
            (left + boundary (j.val + 1))) ∪
          Chvatal.blockOf s rightStart s.card) = s)
    (hdisjoint : Disjoint
        (Chvatal.blockOf s 0 left ∪
          Chvatal.blockOf s rightStart s.card)
        (Finset.univ.biUnion fun j : Fin 8 =>
          Chvatal.blockOf s (left + boundary j.val)
            (left + boundary (j.val + 1))) ∧
      ∀ j j' : Fin 8, j ≠ j' →
        Disjoint
          (Chvatal.blockOf s (left + boundary j.val)
            (left + boundary (j.val + 1)))
          (Chvatal.blockOf s (left + boundary j'.val)
            (left + boundary (j'.val + 1)))) :
    (∀ port, d2SenderPortsLocalPiece
      (d2OrdinaryRankSenderPorts s boundary left rightStart) port ⊆ s) ∧
      Finset.univ.biUnion
        (d2SenderPortsLocalPiece
          (d2OrdinaryRankSenderPorts s boundary left rightStart)) = s ∧
      (∀ port port', port ≠ port' →
        Disjoint
          (d2SenderPortsLocalPiece
            (d2OrdinaryRankSenderPorts s boundary left rightStart) port)
          (d2SenderPortsLocalPiece
            (d2OrdinaryRankSenderPorts s boundary left rightStart) port')) := by
  let ports := d2OrdinaryRankSenderPorts s boundary left rightStart
  have hparentSubset : ports.up ⊆ s := by
    exact Finset.union_subset Chvatal.blockOf_subset Chvatal.blockOf_subset
  have hchildSubset : ∀ j, ports.down j ⊆ s := by
    intro j
    exact Chvatal.blockOf_subset
  have hcover' : ports.up ∪ Finset.univ.biUnion ports.down = s := by
    simpa [ports, d2OrdinaryRankSenderPorts, Finset.union_assoc,
      Finset.union_left_comm, Finset.union_comm] using hcover
  have hparentDisjoint : Disjoint ports.up
      (Finset.univ.biUnion ports.down) := by
    simpa [ports, d2OrdinaryRankSenderPorts] using hdisjoint.1
  have hchildDisjoint : ∀ j j', j ≠ j' →
      Disjoint (ports.down j) (ports.down j') := by
    intro j j' hj
    simpa [ports, d2OrdinaryRankSenderPorts] using hdisjoint.2 j j' hj
  simpa [ports] using d2SenderPorts_partition_contract s ports
    hparentSubset hchildSubset hcover' hparentDisjoint hchildDisjoint

/-- The flat one-stage receiver bags obtained by routing every local piece to
its indexed parent/child (or to the explicit external boundary bucket). -/
noncomputable def d2SenderNodeRoutedBag {Wire : Type*} [DecidableEq Wire]
    {depth : Nat} (active : Nat → Bool)
    (source : D2SenderNode depth → Finset Wire)
    (split : D2SenderNode depth → D2SenderPorts Wire)
    (receiver : Option (D2SenderNode depth)) : Finset Wire :=
  Finset.univ.biUnion fun node =>
    routedTargetPiece (d2SenderNodeLocalPiece active source split)
      (d2SenderNodeRouteTarget active) node receiver

/-- The external receiver bucket is empty when every active root has empty
parent output and the leaf level is inactive. -/
theorem d2SenderNodeRoutedBag_external_empty
    {Wire : Type*} [DecidableEq Wire] {depth : Nat}
    (active : Nat → Bool) (source : D2SenderNode depth → Finset Wire)
    (split : D2SenderNode depth → D2SenderPorts Wire)
    (hrootUp : ∀ node, node.1.val = 0 → active node.1.val = true →
      (split node).up = Finset.empty)
    (hleaf : active depth = false) :
    d2SenderNodeRoutedBag active source split none = Finset.empty := by
  classical
  apply Finset.ext
  intro x
  constructor
  · intro hx
    unfold d2SenderNodeRoutedBag at hx
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and] at hx
    rcases hx with ⟨node, hx⟩
    change x ∈ routedTargetPiece (d2SenderNodeLocalPiece active source split)
      (d2SenderNodeRouteTarget active) node none at hx
    unfold routedTargetPiece at hx
    rcases Finset.mem_biUnion.mp hx with ⟨port, hport, hxpiece⟩
    have htarget := (Finset.mem_filter.mp hport).2
    cases port with
    | none =>
      have ha : active node.1.val = true := by
        by_cases hactive : active node.1.val = true
        · exact hactive
        · simp [d2SenderNodeRouteTarget, hactive] at htarget
      have hroot : node.1.val = 0 := by
        apply (d2SenderNodeParent?_eq_none_iff node).mp
        simpa [d2SenderNodeRouteTarget, ha] using htarget
      have hup := hrootUp node hroot ha
      have hfalse : False := by
        have hp : x ∈ (Finset.empty : Finset Wire) := by
          simpa [d2SenderNodeLocalPiece, ha, d2SenderPortsLocalPiece, hup]
            using hxpiece
        exact Finset.notMem_empty x hp
      exact hfalse.elim
    | some j =>
      have ha : active node.1.val = true := by
        by_cases hactive : active node.1.val = true
        · exact hactive
        · simp [d2SenderNodeRouteTarget, hactive] at htarget
      have hnodeLevel : node.1.val = depth := by
        apply (d2SenderNodeChild?_eq_none_iff node j).mp
        simpa [d2SenderNodeRouteTarget, ha] using htarget
      rw [hnodeLevel] at ha
      have hfalse : False := by simp [hleaf] at ha
      exact hfalse.elim
  · intro hx
    have hfalse : False := Finset.notMem_empty x hx
    exact hfalse.elim

/-- The flat D2 route preserves a global wire partition once source bags and
each sender's local pieces satisfy the partition contracts. This is the
finite-tree instantiation of `routed_local_destinations_preserve_partition`;
the candidate schedule still has to supply these hypotheses. -/
theorem d2SenderNodeRoute_preserves_partition
    {Wire : Type*} [Fintype Wire] [DecidableEq Wire]
    {depth : Nat} (active : Nat → Bool)
    (source : D2SenderNode depth → Finset Wire)
    (split : D2SenderNode depth → D2SenderPorts Wire)
    (hsourceCover : Finset.univ.biUnion source = Finset.univ)
    (hsourceDisjoint : ∀ node node', node ≠ node' →
      Disjoint (source node) (source node'))
    (hlocalSubset : ∀ node port,
      d2SenderNodeLocalPiece active source split node port ⊆ source node)
    (hlocalCover : ∀ node,
      Finset.univ.biUnion (d2SenderNodeLocalPiece active source split node) =
        source node)
    (hlocalDisjoint : ∀ node port port', port ≠ port' →
      Disjoint (d2SenderNodeLocalPiece active source split node port)
        (d2SenderNodeLocalPiece active source split node port')) :
    (∀ receiver receiver', receiver ≠ receiver' →
      Disjoint (d2SenderNodeRoutedBag active source split receiver)
        (d2SenderNodeRoutedBag active source split receiver')) ∧
      Finset.univ.biUnion (d2SenderNodeRoutedBag active source split) =
        Finset.univ := by
  exact routed_local_destinations_preserve_partition source
    (d2SenderNodeLocalPiece active source split)
    (d2SenderNodeRouteTarget active)
    hsourceCover hsourceDisjoint hlocalSubset hlocalCover hlocalDisjoint

/-- The cardinality of one flat receiver bag is exactly the sum of the sizes
of all local ports tagged for that receiver. This exposes the remaining
flow-allocation comparison as a port-width identity. -/
theorem d2SenderNodeRoutedBag_card_eq_incoming_ports
    {Wire : Type*} [Fintype Wire] [DecidableEq Wire]
    {depth : Nat} (active : Nat → Bool)
    (source : D2SenderNode depth → Finset Wire)
    (split : D2SenderNode depth → D2SenderPorts Wire)
    (hsourceDisjoint : ∀ node node', node ≠ node' →
      Disjoint (source node) (source node'))
    (hlocalSubset : ∀ node port,
      d2SenderNodeLocalPiece active source split node port ⊆ source node)
    (hlocalDisjoint : ∀ node port port', port ≠ port' →
      Disjoint (d2SenderNodeLocalPiece active source split node port)
        (d2SenderNodeLocalPiece active source split node port'))
    (receiver : Option (D2SenderNode depth)) :
    (d2SenderNodeRoutedBag active source split receiver).card =
      ∑ node ∈ Finset.univ,
        ∑ port ∈ Finset.univ.filter
          (fun port : D2SenderRoutePort =>
            d2SenderNodeRouteTarget active node port = receiver),
          (d2SenderNodeLocalPiece active source split node port).card := by
  classical
  simpa [d2SenderNodeRoutedBag] using
    (routedReceiver_card_eq_sum_of_piece_cards source
      (d2SenderNodeLocalPiece active source split)
      (d2SenderNodeRouteTarget active)
      hsourceDisjoint hlocalSubset hlocalDisjoint receiver)

/-- If the boundary bucket is empty, the partition after routing is a
partition by internal sender nodes alone. -/
theorem d2SenderNodeRoute_internal_partition_of_external_empty
    {Wire : Type*} [Fintype Wire] [DecidableEq Wire]
    {depth : Nat} (active : Nat → Bool)
    (source : D2SenderNode depth → Finset Wire)
    (split : D2SenderNode depth → D2SenderPorts Wire)
    (hpartition :
      (∀ receiver receiver', receiver ≠ receiver' →
        Disjoint (d2SenderNodeRoutedBag active source split receiver)
          (d2SenderNodeRoutedBag active source split receiver')) ∧
        Finset.univ.biUnion (d2SenderNodeRoutedBag active source split) =
          Finset.univ)
    (hexternal : d2SenderNodeRoutedBag active source split none = Finset.empty) :
    (∀ node node', node ≠ node' →
      Disjoint (d2SenderNodeRoutedBag active source split (some node))
        (d2SenderNodeRoutedBag active source split (some node'))) ∧
      Finset.univ.biUnion
        (fun node => d2SenderNodeRoutedBag active source split (some node)) =
          Finset.univ := by
  refine ⟨?_, ?_⟩
  · intro node node' hne
    apply hpartition.1 (some node) (some node')
    intro heq
    exact hne (Option.some.inj heq)
  · ext x
    constructor
    · intro _
      exact Finset.mem_univ x
    · intro _
      have hx : x ∈ Finset.univ.biUnion (d2SenderNodeRoutedBag active source split) := by
        rw [hpartition.2]
        exact Finset.mem_univ x
      rcases Finset.mem_biUnion.mp hx with ⟨receiver, _, hxreceiver⟩
      cases receiver with
      | none =>
          rw [hexternal] at hxreceiver
          exact (Finset.notMem_empty x hxreceiver).elim
      | some node =>
          exact Finset.mem_biUnion.mpr ⟨node, Finset.mem_univ _, hxreceiver⟩

end Chvatal.D2OrdinaryRankRouting
