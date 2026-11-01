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

/-- A parent edge decreases the flat tree level by exactly one. -/
theorem d2SenderNodeParent?_some_level {depth : Nat}
    (node parent : D2SenderNode depth)
    (h : d2SenderNodeParent? node = some parent) :
    parent.1.val + 1 = node.1.val := by
  rcases node with ⟨⟨level, hlevel⟩, path⟩
  cases level with
  | zero => simp [d2SenderNodeParent?] at h
  | succ level =>
      cases Option.some.inj h
      rfl

/-- A child edge increases the flat tree level by exactly one. -/
theorem d2SenderNodeChild?_some_level {depth : Nat}
    (node : D2SenderNode depth) (port : Fin 8) (child : D2SenderNode depth)
    (h : d2SenderNodeChild? node port = some child) :
    node.1.val + 1 = child.1.val := by
  rcases node with ⟨⟨level, hlevel⟩, path⟩
  unfold d2SenderNodeChild? at h
  by_cases hlt : level < depth
  · simp [hlt] at h
    cases h
    rfl
  · simp [hlt] at h

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

theorem d2SenderLayoutRootBag_subset_wires {Wire : Type*}
    [DecidableEq Wire] {h : Nat} (layout : D2SenderLayout Wire h) :
    d2SenderLayoutRootBag layout ⊆ d2SenderLayoutWires layout := by
  cases layout <;> simp [d2SenderLayoutRootBag, d2SenderLayoutWires]

theorem d2SenderLayoutBagAtPath_subset_wires {Wire : Type*}
    [DecidableEq Wire] :
    ∀ (levels : Nat) {h : Nat}
      (layout : D2SenderLayout Wire (h + levels))
      (path : D2FlowPath levels),
      d2SenderLayoutBagAtPath levels layout path ⊆
        d2SenderLayoutWires layout := by
  intro levels
  induction levels with
  | zero =>
      intro h layout path
      cases path
      simpa [d2SenderLayoutBagAtPath] using
        d2SenderLayoutRootBag_subset_wires layout
  | succ levels ih =>
      intro h layout path
      cases path with
      | cons j tail =>
          cases layout with
          | node bag children =>
              simp only [d2SenderLayoutBagAtPath]
              have hsub := ih (h := h) (layout := children j) tail
              intro wire hwire
              simp only [d2SenderLayoutWires, Finset.mem_union,
                Finset.mem_biUnion, Finset.mem_univ, true_and]
              exact Or.inr ⟨j, hsub hwire⟩

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

theorem d2FlowNodeStaticBag_card_eq_flow_allocation_of_clamped_fit
    {n scale h : Nat} (base G low high : Nat)
    (children : Fin 8 -> D2FlowTree h)
    (hinv : d2FlowTreeInv scale (.node G low high children))
    (hfit : StaticHolesFit (base + low)
      (d2FlowNodeStaticHolesClamped base (scale * 8 ^ h) low high children)
      (base + 8 * (scale * 8 ^ h) - high))
    (hstop : base + 8 * (scale * 8 ^ h) - high <= n) :
    (d2FlowNodeStaticBag (n := n) base (scale * 8 ^ h)
      G low high children).card =
      d2FlowTreeAllocation scale (.node G low high children) := by
  by_cases hsat : G = 8 * (scale * 8 ^ h)
  case pos =>
    have hinv' := hinv
    simp only [d2FlowTreeInv] at hinv'
    have hchildInv : forall j, d2FlowTreeInv scale (children j) := hinv'.2.2.2
    have htotalLe : d2FlowTotal
        (fun j => d2FlowTreeRootDeficit (children j)) <=
          8 * (scale * 8 ^ h) := by
      unfold d2FlowTotal
      calc
        _ <= Finset.univ.sum (fun _ : Fin 8 => scale * 8 ^ h) :=
          Finset.sum_le_sum (fun j hj =>
            d2FlowTreeInv_root_native_bound (children j) (hchildInv j))
        _ = 8 * (scale * 8 ^ h) := by simp
    have htotalEq : d2FlowTotal
        (fun j => d2FlowTreeRootDeficit (children j)) = G := by
      rw [hsat]
      apply Nat.le_antisymm htotalLe
      simpa [hsat] using hinv'.2.1
    simp [d2FlowNodeStaticBag, hsat, d2FlowTreeAllocation, htotalEq]
  case neg =>
    have hcap : G <= 8 * (scale * 8 ^ h) := by
      simpa [Nat.pow_succ, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
        using hinv.1
    have hGlt : G < 8 * (scale * 8 ^ h) := Nat.lt_of_le_of_ne hcap hsat
    rw [d2FlowNodeStaticBag_card_eq_child_total_sub_G_of_clamped_fit
      base G low high children hinv hfit hstop hGlt]
    rfl

/-- Canonical-fit compatibility wrapper for the clamped sender-cardinality
contract. -/
theorem d2FlowNodeStaticBag_card_eq_flow_allocation_of_fit
    {n scale h : Nat} (base G low high : Nat)
    (children : Fin 8 -> D2FlowTree h)
    (hinv : d2FlowTreeInv scale (.node G low high children))
    (hfit : StaticHolesFit (base + low)
      (d2FlowNodeStaticHoles base (scale * 8 ^ h) low high children)
      (base + 8 * (scale * 8 ^ h) - high))
    (hstop : base + 8 * (scale * 8 ^ h) - high <= n) :
    (d2FlowNodeStaticBag (n := n) base (scale * 8 ^ h)
      G low high children).card =
      d2FlowTreeAllocation scale (.node G low high children) := by
  have hinvChildren : ∀ j, d2FlowTreeInv scale (children j) := by
    have h := hinv
    simp only [d2FlowTreeInv] at h
    exact h.2.2.2
  have hclamped := d2FlowNodeStaticHolesClamped_fit_of_static_fit
    children rfl hinvChildren hfit
  exact d2FlowNodeStaticBag_card_eq_flow_allocation_of_clamped_fit
    base G low high children hinv hclamped hstop

theorem d2FlowTreePhysicalBag_leaf_card_eq_allocation
    {n scale : Nat} (base G low high : Nat)
    (hinv : d2FlowTreeInv scale (.leaf G low high))
    (hstop : base + scale - high <= n) :
    (d2FlowTreePhysicalBag (n := n) (scale := scale) base
      (.leaf G low high)).card =
      d2FlowTreeAllocation scale (.leaf G low high) := by
  by_cases hsat : G = scale
  case pos =>
    simp [d2FlowTreePhysicalBag, d2FlowTreeAllocation, hsat]
    rfl
  case neg =>
    have hinv' : G <= scale /\ (G < scale -> low + high = G) := by
      simpa [d2FlowTreeInv] using hinv
    have hGlt : G < scale := by
      have hGle : G <= scale := hinv'.1
      omega
    have hbal : low + high = G := hinv'.2 hGlt
    simp only [d2FlowTreePhysicalBag, if_neg hsat]
    rw [staticWireInterval_card hstop]
    simp [d2FlowTreeAllocation]
    omega

/-- Recursive sender layout obtained from the concrete static physical bags. -/
def d2FlowTreePhysicalLayout {n scale : Nat} :
    (base : Nat) -> {h : Nat} -> D2FlowTree h ->
      D2SenderLayout (Fin n) h
  | base, 0, tree => .leaf (d2FlowTreePhysicalBag (scale := scale) base tree)
  | base, h + 1, .node G low high children =>
      .node (d2FlowTreePhysicalBag (scale := scale) base (.node G low high children))
        (fun j => d2FlowTreePhysicalLayout (n := n) (scale := scale)
          (base + j.val * (scale * 8 ^ h)) (children j))

theorem d2FlowTreePhysicalLayout_cast {n scale a b : Nat}
    (h : a = b) (base : Nat) (tree : D2FlowTree a) :
    cast (congrArg (D2SenderLayout (Fin n)) h)
        (d2FlowTreePhysicalLayout (n := n) (scale := scale) base tree) =
      d2FlowTreePhysicalLayout (n := n) (scale := scale) base
        (cast (congrArg D2FlowTree h) tree) := by
  cases h
  rfl

theorem nativePathStart_cons (scale remaining : Nat) {levels : Nat}
    (j : Fin 8) (path : D2FlowPath levels) :
    nativePathStart scale remaining (.cons j path) =
      j.val * (scale * 8 ^ (remaining + levels)) +
        nativePathStart scale remaining path := by
  simp only [nativePathStart, D2NativePathIntervals.pathIndex, Nat.pow_add]
  ring

theorem d2FlowTreePhysicalLayout_bagAtPath {n scale base remaining levels : Nat}
    (tree : D2FlowTree (remaining + levels)) (path : D2FlowPath levels) :
    d2SenderLayoutBagAtPath levels
        (d2FlowTreePhysicalLayout (n := n) (scale := scale) base tree) path =
      d2FlowTreePhysicalBag (scale := scale)
        (base + nativePathStart scale remaining path)
        (d2FlowTreeAtPath levels tree path) := by
  induction path generalizing remaining base with
  | nil =>
      cases remaining with
      | zero =>
          cases tree with
          | leaf G low high =>
              simp [d2SenderLayoutBagAtPath, d2FlowTreePhysicalLayout,
                d2FlowTreePhysicalBag, d2FlowTreeAtPath, d2SenderLayoutRootBag,
                nativePathStart,
                D2NativePathIntervals.pathIndex]
      | succ remaining =>
          cases tree with
          | node G low high children =>
              simp [d2SenderLayoutBagAtPath, d2FlowTreePhysicalLayout,
                d2FlowTreePhysicalBag, d2FlowTreeAtPath, d2SenderLayoutRootBag,
                nativePathStart,
                D2NativePathIntervals.pathIndex]
  | @cons levels j tail ih =>
      cases tree with
      | node G low high children =>
          simp only [d2SenderLayoutBagAtPath, d2FlowTreePhysicalLayout,
            d2FlowTreeAtPath]
          rw [nativePathStart_cons]
          simpa [d2FlowTreeChild, Nat.add_assoc] using
            (ih (remaining := remaining) (base :=
              base + j.val * (scale * 8 ^ (remaining + levels)))
              (tree := children j))

theorem d2FlowTreeAtPath_full (scale remaining levels : Nat)
    (path : D2FlowPath levels) :
    d2FlowTreeAtPath levels (d2FlowTreeFull scale (remaining + levels)) path =
      d2FlowTreeFull scale remaining := by
  induction path generalizing remaining with
  | nil => simp [d2FlowTreeAtPath]
  | @cons levels j tail ih =>
      simp only [d2FlowTreeAtPath, d2FlowTreeFull]
      simpa [Nat.add_assoc] using ih remaining

theorem d2FlowTreeInitial_cast {a b scale : Nat} (h : a = b) :
    cast (congrArg D2FlowTree h) (d2FlowTreeInitial scale a) =
      d2FlowTreeInitial scale b := by
  cases h
  rfl

theorem d2SenderNodeSubtree_initial_eq_full {scale depth : Nat}
    (node : D2SenderNode depth) (hpos : 0 < node.1.val) :
    d2SenderNodeSubtree (d2FlowTreeInitial scale depth) node =
      d2FlowTreeFull scale (depth - node.1.val) := by
  rcases node with ⟨⟨level, hlevel⟩, path⟩
  cases level with
  | zero => simp_all
  | succ levels =>
      have hle : levels + 1 ≤ depth := by omega
      let remaining := depth - (levels + 1)
      have hdecomp : remaining + (levels + 1) = depth :=
        Nat.sub_add_cancel hle
      let fullTree : D2FlowTree (remaining + (levels + 1)) :=
        cast (congrArg D2FlowTree hdecomp.symm)
          (d2FlowTreeInitial scale depth)
      have hfullTree : fullTree =
          d2FlowTreeInitial scale (remaining + (levels + 1)) := by
        dsimp [fullTree]
        exact d2FlowTreeInitial_cast hdecomp.symm
      change d2FlowTreeAtPath (levels + 1) fullTree path =
        d2FlowTreeFull scale remaining
      rw [hfullTree]
      cases path with
      | cons j tail =>
          simpa [d2FlowTreeAtPath, d2FlowTreeInitial, Nat.add_assoc] using
            (d2FlowTreeAtPath_full scale remaining levels tail)

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

theorem d2SenderNodeBag_physical_eq {n scale depth : Nat}
    (base : Nat) (tree : D2FlowTree depth) (node : D2SenderNode depth) :
    d2SenderNodeBag (d2FlowTreePhysicalLayout (n := n) (scale := scale)
      base tree) node =
      d2FlowTreePhysicalBag (scale := scale)
        (base + nativePathStart scale (depth - node.1.val) node.2)
        (d2SenderNodeSubtree tree node) := by
  classical
  let level := node.1.val
  have hle : level ≤ depth := by omega
  have heq : (depth - level) + level = depth := Nat.sub_add_cancel hle
  let fullTree : D2FlowTree ((depth - level) + level) :=
    cast (congrArg D2FlowTree heq.symm) tree
  let fullLayout : D2SenderLayout (Fin n) ((depth - level) + level) :=
    cast (congrArg (D2SenderLayout (Fin n)) heq.symm)
      (d2FlowTreePhysicalLayout (n := n) (scale := scale) base tree)
  have hcast : fullLayout =
      d2FlowTreePhysicalLayout (n := n) (scale := scale) base fullTree := by
    exact d2FlowTreePhysicalLayout_cast heq.symm base tree
  change d2SenderLayoutBagAtPath level fullLayout node.2 =
    d2FlowTreePhysicalBag (scale := scale)
      (base + nativePathStart scale (depth - level) node.2)
      (d2FlowTreeAtPath level fullTree node.2)
  rw [hcast]
  exact d2FlowTreePhysicalLayout_bagAtPath fullTree node.2

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

theorem d2SenderNodeBag_initial_root_eq_univ (scale depth : Nat) :
    d2SenderNodeBag
      (d2FlowTreePhysicalLayout (n := scale * 8 ^ depth) (scale := scale) 0
        (d2FlowTreeInitial scale depth)) (d2SenderNodeRoot depth) =
      Finset.univ := by
  rw [d2SenderNodeBag_physical_eq 0]
  have hroot := d2SenderNodePhysicalBag_initial_root_eq_univ scale depth
  rw [d2SenderNodePhysicalBag_root] at hroot
  simpa [d2SenderNodeRoot, nativePathStart,
    D2NativePathIntervals.pathIndex] using hroot

theorem d2SenderNodeBag_initial_ne_root_eq_empty (scale depth : Nat)
    (node : D2SenderNode depth) (hpos : 0 < node.1.val) :
    d2SenderNodeBag
      (d2FlowTreePhysicalLayout (n := scale * 8 ^ depth) (scale := scale) 0
        (d2FlowTreeInitial scale depth)) node = Finset.empty := by
  rw [d2SenderNodeBag_physical_eq 0]
  rw [d2SenderNodeSubtree_initial_eq_full node hpos]
  simpa using d2FlowTreePhysicalBag_full_eq_empty
    (nativePathStart scale (depth - node.1.val) node.2)
    (depth - node.1.val)




theorem d2SenderNodeBag_initial_eq_if_root (scale depth : Nat)
    (node : D2SenderNode depth) :
    d2SenderNodeBag
      (d2FlowTreePhysicalLayout (n := scale * 8 ^ depth) (scale := scale) 0
        (d2FlowTreeInitial scale depth)) node =
      if node = d2SenderNodeRoot depth then Finset.univ else Finset.empty := by
  by_cases hlevel : node.1.val = 0
  case pos =>
    have hnode : node = d2SenderNodeRoot depth := by
      cases node with
      | mk level path =>
        have hvalue : level.val = 0 := hlevel
        have hfin : level = 0 := Fin.ext hvalue
        subst level
        cases path
        rfl
    subst node
    rw [d2SenderNodeBag_initial_root_eq_univ]
    simp
  case neg =>
    have hpos : 0 < node.1.val := Nat.pos_of_ne_zero hlevel
    have hnotroot : Not (node = d2SenderNodeRoot depth) := by
      intro h
      apply hlevel
      rw [h]
      rfl
    rw [d2SenderNodeBag_initial_ne_root_eq_empty scale depth node hpos]
    simp [hnotroot]

theorem d2SenderNodeBag_initial_physical_partition (scale depth : Nat) :
    And
      (forall node node' : D2SenderNode depth, Not (node = node') ->
        Disjoint
          (d2SenderNodeBag
            (d2FlowTreePhysicalLayout (n := scale * 8 ^ depth) (scale := scale) 0
              (d2FlowTreeInitial scale depth)) node)
          (d2SenderNodeBag
            (d2FlowTreePhysicalLayout (n := scale * 8 ^ depth) (scale := scale) 0
              (d2FlowTreeInitial scale depth)) node'))
      (Finset.univ.biUnion (fun node =>
        d2SenderNodeBag
          (d2FlowTreePhysicalLayout (n := scale * 8 ^ depth) (scale := scale) 0
            (d2FlowTreeInitial scale depth)) node) = Finset.univ) := by
  classical
  let source : D2SenderNode depth -> Finset (Fin (scale * 8 ^ depth)) := fun node =>
    d2SenderNodeBag
      (d2FlowTreePhysicalLayout (n := scale * 8 ^ depth) (scale := scale) 0
        (d2FlowTreeInitial scale depth)) node
  have hsource : forall node, source node =
      if node = d2SenderNodeRoot depth then Finset.univ else Finset.empty := by
    intro node
    exact d2SenderNodeBag_initial_eq_if_root scale depth node
  constructor
  case left =>
    intro node node' hne
    change Disjoint (source node) (source node')
    rw [hsource node, hsource node']
    by_cases hroot : node = d2SenderNodeRoot depth
    case pos =>
      subst node
      have hnotroot : Not (node' = d2SenderNodeRoot depth) := by
        intro h
        subst node'
        exact hne rfl
      simp only [if_neg hnotroot]
      apply Finset.disjoint_left.mpr
      intro wire hwire hmem
      exact (Finset.not_nonempty_iff_eq_empty.mpr rfl) ⟨wire, hmem⟩
    case neg =>
      rw [if_neg hroot]
      apply Finset.disjoint_left.mpr
      intro wire hwire _
      exact (Finset.not_nonempty_iff_eq_empty.mpr rfl) ⟨wire, hwire⟩
  case right =>
    change Finset.univ.biUnion source = Finset.univ
    ext wire
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and]
    constructor
    case mp =>
      intro _
      trivial
    case mpr =>
      intro _
      apply Exists.intro (d2SenderNodeRoot depth)
      rw [hsource]
      simp

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

/-- A routed piece can only stay at its inactive sender or move by one tree
level to the sender's parent or child. This is the topological support fact
needed to reduce the receiver-port sum to the local flow recurrence. -/
theorem d2SenderNodeRouteTarget_level_relation {depth : Nat}
    (active : Nat → Bool) (node receiver : D2SenderNode depth)
    (port : D2SenderRoutePort)
    (hroute : d2SenderNodeRouteTarget active node port = some receiver) :
    node.1.val + 1 = receiver.1.val ∨
      receiver.1.val + 1 = node.1.val ∨ node.1.val = receiver.1.val := by
  by_cases ha : active node.1.val = true
  · cases port with
    | none =>
        have hp : d2SenderNodeParent? node = some receiver := by
          simpa [d2SenderNodeRouteTarget, ha] using hroute
        exact Or.inr (Or.inl (d2SenderNodeParent?_some_level node receiver hp))
    | some j =>
        have hc : d2SenderNodeChild? node j = some receiver := by
          simpa [d2SenderNodeRouteTarget, ha] using hroute
        exact Or.inl (d2SenderNodeChild?_some_level node j receiver hc)
  · have heq : node = receiver := Option.some.inj (by
      simpa [d2SenderNodeRouteTarget, ha] using hroute)
    exact Or.inr (Or.inr (congrArg (fun n : D2SenderNode depth => n.1.val) heq))

/-- Under a no-adjacent-active-level schedule, active receivers receive no
pieces: inactive nodes only retain themselves, and active neighbors are
excluded by the schedule. -/
theorem d2SenderNodeRouteTarget_not_active_receiver {depth : Nat}
    (active : Nat → Bool) (node receiver : D2SenderNode depth)
    (port : D2SenderRoutePort)
    (hnoadj : ∀ i, active i = true → active (i + 1) = true → False)
    (hreceiver : active receiver.1.val = true) :
    d2SenderNodeRouteTarget active node port ≠ some receiver := by
  intro hroute
  by_cases hnode : active node.1.val = true
  · cases port with
    | none =>
        have hp : d2SenderNodeParent? node = some receiver := by
          simpa [d2SenderNodeRouteTarget, hnode] using hroute
        have hlevel := d2SenderNodeParent?_some_level node receiver hp
        exact hnoadj receiver.1.val hreceiver (by simpa [hlevel] using hnode)
    | some j =>
        have hc : d2SenderNodeChild? node j = some receiver := by
          simpa [d2SenderNodeRouteTarget, hnode] using hroute
        have hlevel := d2SenderNodeChild?_some_level node j receiver hc
        have hreceiver' := hreceiver
        rw [← hlevel] at hreceiver'
        exact hnoadj node.1.val hnode hreceiver'
  · have heq : node = receiver := Option.some.inj (by
      simpa [d2SenderNodeRouteTarget, hnode] using hroute)
    have : active node.1.val = true := by simpa [heq] using hreceiver
    exact hnode this

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

/-- Uniform local partition contract for a flat stage: active nodes use their
rank-port partitions, while inactive nodes retain their whole bag on the
self-port and emit empty child pieces. -/
theorem d2SenderNodeLocalPiece_partition_contract
    {Wire : Type*} [DecidableEq Wire] {depth : Nat}
    (active : Nat -> Bool)
    (source : D2SenderNode depth -> Finset Wire)
    (split : D2SenderNode depth -> D2SenderPorts Wire)
    (hactive : forall node, active node.1.val = true ->
      (forall port, d2SenderPortsLocalPiece (split node) port <= source node) /\
      Finset.univ.biUnion (d2SenderPortsLocalPiece (split node)) = source node /\
      (forall port port', Not (port = port') ->
        Disjoint (d2SenderPortsLocalPiece (split node) port)
          (d2SenderPortsLocalPiece (split node) port'))) :
    (forall node port,
      d2SenderNodeLocalPiece active source split node port <= source node) /\
    (forall node,
      Finset.univ.biUnion (d2SenderNodeLocalPiece active source split node) =
        source node) /\
    (forall node port port', Not (port = port') ->
      Disjoint (d2SenderNodeLocalPiece active source split node port)
        (d2SenderNodeLocalPiece active source split node port')) := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · intro node port
    by_cases ha : active node.1.val = true
    · have hlocalEq : d2SenderNodeLocalPiece active source split node =
          d2SenderPortsLocalPiece (split node) := by
        funext port
        simp [d2SenderNodeLocalPiece, ha]
      rw [hlocalEq]
      exact (hactive node ha).1 port
    · have haFalse : active node.1.val = false := by
        cases hactiveLevel : active node.1.val <;> simp_all
      have hlocalEq : d2SenderNodeLocalPiece active source split node =
          fun port => match port with
            | none => source node
            | some _ => Finset.empty := by
        funext port
        cases port <;> simp [d2SenderNodeLocalPiece, haFalse]
      rw [hlocalEq]
      cases port with
      | none => exact fun _ hx => hx
      | some j => exact Finset.empty_subset _
  · intro node
    by_cases ha : active node.1.val = true
    · have hlocalEq : d2SenderNodeLocalPiece active source split node =
          d2SenderPortsLocalPiece (split node) := by
        funext port
        simp [d2SenderNodeLocalPiece, ha]
      rw [hlocalEq]
      exact (hactive node ha).2.1
    · have haFalse : active node.1.val = false := by
        cases hactiveLevel : active node.1.val <;> simp_all
      have hlocalEq : d2SenderNodeLocalPiece active source split node =
          fun port => match port with
            | none => source node
            | some _ => Finset.empty := by
        funext port
        cases port <;> simp [d2SenderNodeLocalPiece, haFalse]
      rw [hlocalEq]
      ext wire
      simp only [Finset.mem_biUnion, Finset.mem_univ, true_and]
      constructor
      · intro h
        cases h with
        | intro port hp =>
          cases port with
          | none => exact hp
          | some j => exact (Finset.notMem_empty wire hp).elim
      · intro h
        exact Exists.intro none h
  · intro node port port' hne
    by_cases ha : active node.1.val = true
    · have hlocalEq : d2SenderNodeLocalPiece active source split node =
          d2SenderPortsLocalPiece (split node) := by
        funext port
        simp [d2SenderNodeLocalPiece, ha]
      rw [hlocalEq]
      exact (hactive node ha).2.2 port port' hne
    · have haFalse : active node.1.val = false := by
        cases hactiveLevel : active node.1.val <;> simp_all
      have hlocalEq : d2SenderNodeLocalPiece active source split node =
          fun port => match port with
            | none => source node
            | some _ => Finset.empty := by
        funext port
        cases port <;> simp [d2SenderNodeLocalPiece, haFalse]
      rw [hlocalEq]
      cases port with
      | none =>
        cases port' with
        | none => exact (hne rfl).elim
        | some j => exact Finset.disjoint_empty_right _
      | some j =>
        cases port' with
        | none => exact Finset.disjoint_empty_left _
        | some j' => exact Finset.disjoint_empty_left _

/-- Package the existing ordinary rank cuts as the parent/eight-child port
record consumed by the flat route. -/
def d2OrdinaryRankSenderPorts {n : Nat} (s : Finset (Fin n))
    (boundary : Nat → Nat) (left rightStart : Nat) :
    D2SenderPorts (Fin n) where
  up := Chvatal.blockOf s 0 left ∪ Chvatal.blockOf s rightStart s.card
  down j := Chvatal.blockOf s (left + boundary j.val)
    (left + boundary (j.val + 1))

theorem d2FlowRankBoundary_le_total_local (sizes : Fin 8 -> Nat)
    (i : Nat) : d2FlowRankBoundary sizes i <= d2FlowTotal sizes := by
  by_cases hlt : i < 8
  case pos =>
    simp only [d2FlowRankBoundary, dif_pos hlt]
    unfold d2FlowPosition d2FlowTotal
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (by intro j hj hnot; exact Nat.zero_le _)
  case neg =>
    simp [d2FlowRankBoundary, hlt]

theorem d2OrdinaryRankSenderPorts_card_eq_flow_widths
    {active : Nat -> Bool} {role : Nat -> D2Role}
    {quota : Nat -> D2Role -> Nat} {h i G low high n : Nat}
    (children : Fin 8 -> D2FlowTree h) (s : Finset (Fin n))
    (ha : active i = true)
    (hr : Or (role i = .topRise)
      (Or (role i = .mid) (role i = .botDesc)))
    (hbal : G = low + high)
    (heven : quota i (role i) % 2 = 0)
    (hleft : low + quota i (role i) / 2 <=
      d2FlowTotal (fun j => d2FlowTreeRootDeficit (children j)))
    (hright : high + quota i (role i) / 2 <=
      d2FlowTotal (fun j => d2FlowTreeRootDeficit (children j)))
    (hgap : low + quota i (role i) / 2 <=
      d2FlowTotal (fun j => d2FlowTreeRootDeficit (children j)) -
        high - quota i (role i) / 2)
    (hsender : s.card = d2FlowTotal
      (fun j => d2FlowTreeRootDeficit (children j)) - G) :
    let widths : Fin 8 -> Nat := fun j =>
      d2FlowTreeRootDeficit (children j) -
        d2FlowTreeRootDeficit
          (d2FlowTreeChild
            (d2FlowStage active role quota (h + 1) i
              (.node G low high children)) j)
    let boundary : Nat -> Nat := d2FlowRankBoundary widths
    let ports := d2OrdinaryRankSenderPorts s boundary
      (quota i (role i) / 2) (s.card - quota i (role i) / 2)
    And (ports.up.card = quota i (role i))
      (forall j, (ports.down j).card = widths j) := by
  classical
  let q := quota i (role i)
  let left := q / 2
  let widths : Fin 8 -> Nat := fun j =>
    d2FlowTreeRootDeficit (children j) -
      d2FlowTreeRootDeficit
        (d2FlowTreeChild
          (d2FlowStage active role quota (h + 1) i
            (.node G low high children)) j)
  let boundary := d2FlowRankBoundary widths
  let ports := d2OrdinaryRankSenderPorts s boundary left (s.card - left)
  have hconserve : q + d2FlowTotal widths =
      d2FlowTotal (fun j => d2FlowTreeRootDeficit (children j)) - G := by
    simpa [q, widths, d2FlowTotal] using
      d2FlowStage_regular_rank_port_conservation children ha hr hbal heven
        hleft hright hgap
  have hcard : q + d2FlowTotal widths = s.card := by
    rw [hsender]
    exact hconserve
  have hq : q = 2 * left := by
    simp [q, left]
    omega
  have hleftLe : left <= s.card := by omega
  have hseam : left <= s.card - left := by omega
  have hprefixCard : (Chvatal.blockOf s 0 left).card = left := by
    rw [Chvatal.blockOf_card hleftLe]
    simp
  have hsuffixCard : (Chvatal.blockOf s (s.card - left) s.card).card = left := by
    rw [Chvatal.blockOf_card (Nat.le_refl _)]
    omega
  have hup : ports.up.card = q := by
    dsimp [ports, d2OrdinaryRankSenderPorts]
    rw [Finset.card_union_of_disjoint (Chvatal.disjoint_blockOf hseam),
      hprefixCard, hsuffixCard, hq]
    ring
  have hdown (j : Fin 8) : (ports.down j).card = widths j := by
    dsimp [ports, d2OrdinaryRankSenderPorts]
    have hbound : left + boundary (j.val + 1) <= s.card := by
      have htail : boundary (j.val + 1) <= d2FlowTotal widths := by
        simpa [boundary] using
          d2FlowRankBoundary_le_total_local widths (j.val + 1)
      calc
        left + boundary (j.val + 1) <= left + d2FlowTotal widths :=
          Nat.add_le_add_left htail left
        _ <= s.card := by omega
    rw [Chvatal.blockOf_card hbound]
    have hstep : boundary (j.val + 1) = boundary j.val + widths j := by
      simpa [boundary] using d2FlowRankBoundary_succ widths j.val j.isLt
    rw [hstep]
    omega
  simpa [q, left, widths, boundary, ports,
    d2OrdinaryRankSenderPorts] using And.intro hup hdown

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

/-- Combined local contract for an ordinary active sender: the concrete rank
pieces partition the source bag, and their cardinalities equal the flow
up-port quota and child deficit drops. -/
theorem d2OrdinaryRankSenderPorts_complete_contract
    {active : Nat -> Bool} {role : Nat -> D2Role}
    {quota : Nat -> D2Role -> Nat} {h i G low high n : Nat}
    (children : Fin 8 -> D2FlowTree h) (s : Finset (Fin n))
    (ha : active i = true)
    (hr : Or (role i = .topRise)
      (Or (role i = .mid) (role i = .botDesc)))
    (hbal : G = low + high)
    (heven : quota i (role i) % 2 = 0)
    (hleft : low + quota i (role i) / 2 <=
      d2FlowTotal (fun j => d2FlowTreeRootDeficit (children j)))
    (hright : high + quota i (role i) / 2 <=
      d2FlowTotal (fun j => d2FlowTreeRootDeficit (children j)))
    (hgap : low + quota i (role i) / 2 <=
      d2FlowTotal (fun j => d2FlowTreeRootDeficit (children j)) -
        high - quota i (role i) / 2)
    (hsender : s.card = d2FlowTotal
      (fun j => d2FlowTreeRootDeficit (children j)) - G) :
    let widths : Fin 8 -> Nat := fun j =>
      d2FlowTreeRootDeficit (children j) -
        d2FlowTreeRootDeficit
          (d2FlowTreeChild
            (d2FlowStage active role quota (h + 1) i
              (.node G low high children)) j)
    let boundary : Nat -> Nat := d2FlowRankBoundary widths
    let ports := d2OrdinaryRankSenderPorts s boundary
      (quota i (role i) / 2) (s.card - quota i (role i) / 2)
    And
      (And (forall port, d2SenderPortsLocalPiece ports port <= s)
        (And (Finset.univ.biUnion (d2SenderPortsLocalPiece ports) = s)
          (forall port port', Not (port = port') ->
            Disjoint (d2SenderPortsLocalPiece ports port)
              (d2SenderPortsLocalPiece ports port'))))
      (And (ports.up.card = quota i (role i))
        (forall j, (ports.down j).card = widths j)) := by
  classical
  let widths : Fin 8 -> Nat := fun j =>
    d2FlowTreeRootDeficit (children j) -
      d2FlowTreeRootDeficit
        (d2FlowTreeChild
          (d2FlowStage active role quota (h + 1) i
            (.node G low high children)) j)
  let boundary := d2FlowRankBoundary widths
  let ports := d2OrdinaryRankSenderPorts s boundary
    (quota i (role i) / 2) (s.card - quota i (role i) / 2)
  have hcover := d2FlowStage_regular_sender_rank_ports_cover children s
    ha hr hbal heven hleft hright hgap hsender
  have hdisjoint := d2FlowStage_regular_sender_rank_ports_disjoint children s
    ha hr hbal heven hleft hright hgap hsender
  have hlocal := d2OrdinaryRankSenderPorts_contract s boundary
    (quota i (role i) / 2) (s.card - quota i (role i) / 2) hcover hdisjoint
  have hcards := d2OrdinaryRankSenderPorts_card_eq_flow_widths children s
    ha hr hbal heven hleft hright hgap hsender
  simpa [widths, boundary, ports, d2OrdinaryRankSenderPorts] using
    And.intro hlocal hcards

/-- For an ordinary active node, the all-stage sender-input contract itself
supplies the cut-front bounds needed by the arbitrary-set port theorem. Thus
an inductive sender set needs only its flow-allocation cardinality; no static
hole fit or separate endpoint-cut argument is required. -/
theorem d2OrdinaryRankSenderPorts_of_stage_inputs
    {active : Nat -> Bool} {role : Nat -> D2Role}
    {quota : Nat -> D2Role -> Nat} {cap : Nat -> Nat}
    {scale h i G low high n : Nat}
    (children : Fin 8 -> D2FlowTree h) (s : Finset (Fin n))
    (htree : d2FlowTreeInv scale (.node G low high children))
    (hinputs : d2FlowStageInvInputs scale active role quota cap i
      (.node G low high children))
    (ha : active i = true)
    (hr : role i = .topRise \/ role i = .mid \/ role i = .botDesc)
    (hsender : s.card =
      d2FlowTotal (fun j => d2FlowTreeRootDeficit (children j)) - G) :
    let widths : Fin 8 -> Nat := fun j =>
      d2FlowTreeRootDeficit (children j) -
        d2FlowTreeRootDeficit
          (d2FlowTreeChild
            (d2FlowStage active role quota (h + 1) i
              (.node G low high children)) j)
    let boundary : Nat -> Nat := d2FlowRankBoundary widths
    let ports := d2OrdinaryRankSenderPorts s boundary
      (quota i (role i) / 2) (s.card - quota i (role i) / 2)
    And
      (And (forall port, d2SenderPortsLocalPiece ports port <= s)
        (And (Finset.univ.biUnion (d2SenderPortsLocalPiece ports) = s)
          (forall port port', Not (port = port') ->
            Disjoint (d2SenderPortsLocalPiece ports port)
              (d2SenderPortsLocalPiece ports port'))))
      (And (ports.up.card = quota i (role i))
        (forall j, (ports.down j).card = widths j)) := by
  have hactiveFields := hinputs.2
  simp only [ha, if_pos] at hactiveFields
  rcases hactiveFields with ⟨hbal, hroleFields⟩
  have hfields : 512 * G <= cap i /\
      256 * quota i (role i) <= cap i /\
      quota i (role i) <=
        d2FlowTotal (fun j => d2FlowTreeRootDeficit (children j)) - G /\
      quota i (role i) % 2 = 0 /\
      cap i <= 128 * d2FlowTreeRootDeficit (children ⟨0, by omega⟩) /\
      cap i <= 128 * d2FlowTreeRootDeficit (children ⟨7, by omega⟩) := by
    rcases hr with htop | hmid | hbot
    · simpa [htop] using hroleFields
    · simpa [hmid] using hroleFields
    · simpa [hbot] using hroleFields
  rcases hfields with ⟨hG, hqCap, hqAlloc, hqEven, hreserveLeft, hreserveRight⟩
  have hquotaEven : quota i (role i) = 2 * (quota i (role i) / 2) := by
    omega
  have hfronts := d2_endpoint_fronts_fit_of_reserve hG
    (by omega : low <= G) (by omega : high <= G)
    hqCap hquotaEven hreserveLeft hreserveRight
  have hleft : low + quota i (role i) / 2 <=
      d2FlowTotal (fun j => d2FlowTreeRootDeficit (children j)) :=
    le_trans hfronts.1 (d2FlowSize_le_total
      (fun j => d2FlowTreeRootDeficit (children j)) ⟨0, by omega⟩)
  have hright : high + quota i (role i) / 2 <=
      d2FlowTotal (fun j => d2FlowTreeRootDeficit (children j)) :=
    le_trans hfronts.2 (d2FlowSize_le_total
      (fun j => d2FlowTreeRootDeficit (children j)) ⟨7, by omega⟩)
  have hqplus : G + quota i (role i) <=
      d2FlowTotal (fun j => d2FlowTreeRootDeficit (children j)) := by
    have hGtotal : G <=
        d2FlowTotal (fun j => d2FlowTreeRootDeficit (children j)) :=
      htree.2.1
    have hsum := (Nat.le_sub_iff_add_le hGtotal).mp hqAlloc
    omega
  have hgap : low + quota i (role i) / 2 <=
      d2FlowTotal (fun j => d2FlowTreeRootDeficit (children j)) -
        high - quota i (role i) / 2 := by
    rw [Nat.sub_sub]
    omega
  exact d2OrdinaryRankSenderPorts_complete_contract children s ha hr
    (by omega) hqEven hleft hright hgap hsender

/-- The startup top-descending reset is also an arbitrary-set local routing
contract: its stage-input clause supplies the exact zero root needed by the
generic child-port partition. -/
theorem d2TopDescSenderPieces_of_stage_inputs
    {active : Nat -> Bool} {role : Nat -> D2Role}
    {quota : Nat -> D2Role -> Nat} {cap : Nat -> Nat}
    {h i G low high n : Nat}
    (children : Fin 8 -> D2FlowTree h) (s : Finset (Fin n))
    (hinputs : d2FlowStageInvInputs 8192 active role quota cap i
      (.node G low high children))
    (ha : active i = true) (hr : role i = .topDesc)
    (hsender : s.card =
      d2FlowTotal (fun j => d2FlowTreeRootDeficit (children j)) - G) :
    let widths : Fin 8 -> Nat := fun j =>
      d2FlowTreeRootDeficit (children j) -
        d2FlowTreeRootDeficit
          (d2FlowTreeChild
            (d2FlowStage active role quota (h + 1) i
              (.node G low high children)) j)
    let boundary : Nat -> Nat := d2FlowRankBoundary widths
    (forall target, destinationPiece (ports := 8) s boundary 0 s.card target ⊆ s) /\
      Finset.univ.biUnion (destinationPiece (ports := 8) s boundary 0 s.card) = s /\
      (forall a b, a ≠ b ->
        Disjoint (destinationPiece (ports := 8) s boundary 0 s.card a)
          (destinationPiece (ports := 8) s boundary 0 s.card b)) /\
      (destinationPiece (ports := 8) s boundary 0 s.card none).card = 0 /\
      (forall j : Fin 8,
        (destinationPiece (ports := 8) s boundary 0 s.card (some j)).card =
          widths j) := by
  have hactiveFields := hinputs.2
  simp only [ha, if_pos, hr] at hactiveFields
  rcases hactiveFields with ⟨_, hG⟩
  let widths : Fin 8 -> Nat := fun j =>
    d2FlowTreeRootDeficit (children j) -
      d2FlowTreeRootDeficit
        (d2FlowTreeChild
          (d2FlowStage active role quota (h + 1) i
            (.node G low high children)) j)
  let boundary := d2FlowRankBoundary widths
  have hparts := top_desc_sender_piece_partition
    (active := active) (role := role) (quota := quota)
    (h := h) (i := i) (G := G) (low := low) (high := high)
    (n := n) children s ha hr hG hsender
  have hpost (j : Fin 8) :
      d2FlowTreeRootDeficit
        (d2FlowTreeChild
          (d2FlowStage active role quota (h + 1) i
            (.node G low high children)) j) = 0 := by
    exact d2FlowStage_topDesc_child_deficit children ha hr j
  have hwidthTotal : d2FlowTotal widths =
      d2FlowTotal (fun j => d2FlowTreeRootDeficit (children j)) := by
    unfold d2FlowTotal
    apply Finset.sum_congr rfl
    intro j hj
    simp [widths, hpost]
  have hcard : s.card = d2FlowTotal widths := by
    calc
      s.card = d2FlowTotal
          (fun j => d2FlowTreeRootDeficit (children j)) := by
        simpa [hG] using hsender
      _ = d2FlowTotal widths := hwidthTotal.symm
  have hparentCard :
      (destinationPiece (ports := 8) s boundary 0 s.card none).card = 0 := by
    rw [destinationPiece_parent_card s boundary 0 s.card (by omega) (by omega)]
    simp
  have hchildCard (j : Fin 8) :
      (destinationPiece (ports := 8) s boundary 0 s.card (some j)).card =
        widths j := by
    apply destinationPiece_d2_child_card s widths 0 s.card j
    have hbound : d2FlowRankBoundary widths (j.val + 1) <= s.card := by
      calc
        d2FlowRankBoundary widths (j.val + 1) <= d2FlowTotal widths :=
          d2FlowRankBoundary_le_total_local widths (j.val + 1)
        _ = s.card := hcard.symm
    simpa [boundary] using hbound
  refine ⟨hparts.1, hparts.2.1, hparts.2.2, hparentCard, ?_⟩
  intro j
  simpa [widths, boundary] using hchildCard j

/-- The ordinary port contract applies directly to a fitted physical static
bag: its exact cardinality premise is discharged by the clamped-fit theorem.
Schedule reachability must still provide the fit and cut hypotheses. -/
theorem d2OrdinaryRankSenderPorts_static_bag_complete_contract
    {active : Nat → Bool} {role : Nat → D2Role}
    {quota : Nat → D2Role → Nat} {scale h i G low high n : Nat}
    (children : Fin 8 → D2FlowTree h)
    (htree : d2FlowTreeInv scale (.node G low high children))
    (hfit : StaticHolesFit low
      (d2FlowNodeStaticHolesClamped 0 (scale * 8 ^ h) low high children)
      (8 * (scale * 8 ^ h) - high))
    (hstop : 8 * (scale * 8 ^ h) - high ≤ n)
    (hGlt : G < 8 * (scale * 8 ^ h))
    (ha : active i = true)
    (hr : Or (role i = .topRise)
      (Or (role i = .mid) (role i = .botDesc)))
    (hbal : G = low + high)
    (heven : quota i (role i) % 2 = 0)
    (hleft : low + quota i (role i) / 2 ≤
      d2FlowTotal (fun j => d2FlowTreeRootDeficit (children j)))
    (hright : high + quota i (role i) / 2 ≤
      d2FlowTotal (fun j => d2FlowTreeRootDeficit (children j)))
    (hgap : low + quota i (role i) / 2 ≤
      d2FlowTotal (fun j => d2FlowTreeRootDeficit (children j)) -
        high - quota i (role i) / 2) :
    let s : Finset (Fin n) := d2FlowNodeStaticBag (n := n) 0 (scale * 8 ^ h)
      G low high children
    let widths : Fin 8 → Nat := fun j =>
      d2FlowTreeRootDeficit (children j) -
        d2FlowTreeRootDeficit
          (d2FlowTreeChild
            (d2FlowStage active role quota (h + 1) i
              (.node G low high children)) j)
    let boundary : Nat → Nat := d2FlowRankBoundary widths
    let ports := d2OrdinaryRankSenderPorts s boundary
      (quota i (role i) / 2) (s.card - quota i (role i) / 2)
    And
      (And (∀ port, d2SenderPortsLocalPiece ports port ⊆ s)
        (And (Finset.univ.biUnion (d2SenderPortsLocalPiece ports) = s)
          (∀ port port', port ≠ port' →
            Disjoint (d2SenderPortsLocalPiece ports port)
              (d2SenderPortsLocalPiece ports port'))))
      (And (ports.up.card = quota i (role i))
        (∀ j, (ports.down j).card = widths j)) := by
  let s := d2FlowNodeStaticBag (n := n) 0 (scale * 8 ^ h)
    G low high children
  have hsender : s.card = d2FlowTotal
      (fun j => d2FlowTreeRootDeficit (children j)) - G := by
    have hcard := d2FlowNodeStaticBag_card_eq_flow_allocation_of_clamped_fit
      (n := n) (scale := scale) 0 G low high children htree
      (by simpa using hfit) (by simpa using hstop)
    simpa [s, d2FlowTreeAllocation] using hcard
  simpa [s] using d2OrdinaryRankSenderPorts_complete_contract children s
    ha hr hbal heven hleft hright hgap hsender

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

/-- The flat stage route gives no incoming wires to an active receiver when
active levels are separated by at least one inactive level. -/
theorem d2SenderNodeRoutedBag_active_empty
    {Wire : Type*} [DecidableEq Wire] {depth : Nat}
    (active : Nat → Bool) (source : D2SenderNode depth → Finset Wire)
    (split : D2SenderNode depth → D2SenderPorts Wire)
    (hnoadj : ∀ i, active i = true → active (i + 1) = true → False)
    (receiver : D2SenderNode depth)
    (hreceiver : active receiver.1.val = true) :
    d2SenderNodeRoutedBag active source split (some receiver) = Finset.empty := by
  classical
  apply Finset.ext
  intro x
  constructor
  · intro hx
    unfold d2SenderNodeRoutedBag at hx
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and] at hx
    obtain ⟨node, hx⟩ := hx
    change x ∈ routedTargetPiece (d2SenderNodeLocalPiece active source split)
      (d2SenderNodeRouteTarget active) node (some receiver) at hx
    unfold routedTargetPiece at hx
    obtain ⟨port, hport, hxpiece⟩ := Finset.mem_biUnion.mp hx
    have hroute := (Finset.mem_filter.mp hport).2
    exact (d2SenderNodeRouteTarget_not_active_receiver active node receiver port
      hnoadj hreceiver hroute).elim
  · intro hx
    exact (Finset.notMem_empty x hx).elim

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

/-- Stage-wide wire conservation follows from per-active-node rank-port
partitions; inactive nodes need no routing hypothesis because their local
piece contract is automatic. -/
theorem d2SenderNodeRoute_preserves_partition_of_active_contract
    {Wire : Type*} [Fintype Wire] [DecidableEq Wire]
    {depth : Nat} (active : Nat -> Bool)
    (source : D2SenderNode depth -> Finset Wire)
    (split : D2SenderNode depth -> D2SenderPorts Wire)
    (hsourceCover : Finset.univ.biUnion source = Finset.univ)
    (hsourceDisjoint : forall node node', Not (node = node') ->
      Disjoint (source node) (source node'))
    (hactive : forall node, active node.1.val = true ->
      (forall port, d2SenderPortsLocalPiece (split node) port <= source node) /\
      Finset.univ.biUnion (d2SenderPortsLocalPiece (split node)) = source node /\
      (forall port port', Not (port = port') ->
        Disjoint (d2SenderPortsLocalPiece (split node) port)
          (d2SenderPortsLocalPiece (split node) port'))) :
    (forall receiver receiver', Not (receiver = receiver') ->
      Disjoint (d2SenderNodeRoutedBag active source split receiver)
        (d2SenderNodeRoutedBag active source split receiver')) /\
    Finset.univ.biUnion (d2SenderNodeRoutedBag active source split) =
      Finset.univ := by
  have hlocal := d2SenderNodeLocalPiece_partition_contract
    active source split hactive
  exact d2SenderNodeRoute_preserves_partition active source split
    hsourceCover hsourceDisjoint hlocal.1 hlocal.2.1 hlocal.2.2

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

/-- At an inactive internal node, the recursively updated child up-ports
increase the retained root bag by exactly the flow allocation increment.
This is the layout-side cardinality step for a dynamic sender-set induction. -/
theorem d2SenderLayoutStage_inactive_root_card_eq_allocation
    {Wire : Type*} [DecidableEq Wire]
    {active : Nat -> Bool} {role : Nat -> D2Role}
    {quota : Nat -> D2Role -> Nat} {h scale i G low high : Nat}
    (bag : Finset Wire) (layoutChildren : Fin 8 -> D2SenderLayout Wire h)
    (flowChildren : Fin 8 -> D2FlowTree h)
    (split : Nat -> Finset Wire -> D2SenderPorts Wire)
    (ha : active i = false)
    (hinv : d2FlowTreeInv scale (.node G low high flowChildren))
    (hbag : bag.card = d2FlowTreeAllocation scale
      (.node G low high flowChildren))
    (hports : forall j, (d2SenderLayoutStage active split h (i + 1)
      (layoutChildren j)).2.card =
        d2FlowStagePort active role quota h (i + 1) (flowChildren j))
    (hchildDisjoint : forall j j', j ≠ j' ->
      Disjoint
        ((d2SenderLayoutStage active split h (i + 1)
          (layoutChildren j)).2)
        ((d2SenderLayoutStage active split h (i + 1)
          (layoutChildren j')).2))
    (hdisjoint : Disjoint bag (Finset.univ.biUnion fun j =>
      (d2SenderLayoutStage active split h (i + 1)
        (layoutChildren j)).2)) :
    (d2SenderLayoutRootBag
      (d2SenderLayoutStage active split (h + 1) i
        (.node bag layoutChildren)).1).card =
      d2FlowTreeAllocation scale
        (d2FlowStage active role quota (h + 1) i
          (.node G low high flowChildren)) := by
  rcases d2SenderLayoutStage_node_inactive active split i bag
    layoutChildren ha with ⟨hroot, _⟩
  rw [hroot]
  have hunion : (Finset.univ.biUnion fun j =>
      (d2SenderLayoutStage active split h (i + 1)
        (layoutChildren j)).2).card =
      d2FlowTotal (fun j => d2FlowStagePort active role quota h (i + 1)
        (flowChildren j)) := by
    rw [Finset.card_biUnion (fun j _ j' _ hne => hchildDisjoint j j' hne)]
    unfold d2FlowTotal
    apply Finset.sum_congr rfl
    intro j hj
    exact hports j
  rw [Finset.card_union_of_disjoint hdisjoint, hunion, hbag]
  exact (d2FlowTreeAllocation_after_inactive_node_ports
    flowChildren ha hinv).symm

/-- If an active parent appends a down-port to this recursively updated
inactive child, the child's resulting root bag still has its flow allocation
size. The down-port pays for the root overwrite; descendant up-ports pay for
the recursive capacity growth. -/
theorem d2SenderLayoutStage_inactive_child_overwrite_card_eq_allocation
    {Wire : Type*} [DecidableEq Wire]
    {active : Nat -> Bool} {role : Nat -> D2Role}
    {quota : Nat -> D2Role -> Nat} {h scale i G low high newRoot newLow newHigh : Nat}
    (bag : Finset Wire) (layoutChildren : Fin 8 -> D2SenderLayout Wire h)
    (flowChildren : Fin 8 -> D2FlowTree h)
    (split : Nat -> Finset Wire -> D2SenderPorts Wire)
    (parentDown : Finset Wire)
    (ha : active i = false)
    (hinv : d2FlowTreeInv scale (.node G low high flowChildren))
    (hbag : bag.card = d2FlowTreeAllocation scale
      (.node G low high flowChildren))
    (hports : forall j, (d2SenderLayoutStage active split h (i + 1)
      (layoutChildren j)).2.card =
        d2FlowStagePort active role quota h (i + 1) (flowChildren j))
    (hchildDisjoint : forall j j', j ≠ j' ->
      Disjoint
        ((d2SenderLayoutStage active split h (i + 1)
          (layoutChildren j)).2)
        ((d2SenderLayoutStage active split h (i + 1)
          (layoutChildren j')).2))
    (hdisjoint : Disjoint bag (Finset.univ.biUnion fun j =>
      (d2SenderLayoutStage active split h (i + 1)
        (layoutChildren j)).2))
    (hdown : parentDown.card = G - newRoot)
    (hdownDisjoint : Disjoint
      (d2SenderLayoutRootBag
        (d2SenderLayoutStage active split (h + 1) i
          (.node bag layoutChildren)).1) parentDown)
    (hnewCover : newRoot <= d2FlowTreeCapacityMass scale
      (d2FlowStage active role quota (h + 1) i
        (.node G low high flowChildren)))
    (hrootDrop : newRoot <= G) :
    (d2SenderLayoutRootBag
      (d2SenderLayoutSetRoot
        (d2SenderLayoutStage active split (h + 1) i
          (.node bag layoutChildren)).1
        (d2SenderLayoutRootBag
          (d2SenderLayoutStage active split (h + 1) i
          (.node bag layoutChildren)).1 ∪ parentDown)
        )).card =
      d2FlowTreeAllocation scale
        (d2FlowTreeSetRoot
          (d2FlowStage active role quota (h + 1) i
            (.node G low high flowChildren)) newRoot newLow newHigh) := by
  have hstageCard := d2SenderLayoutStage_inactive_root_card_eq_allocation
    bag layoutChildren flowChildren split ha hinv hbag hports
    hchildDisjoint hdisjoint
  rw [d2SenderLayoutRootBag_setRoot,
    Finset.card_union_of_disjoint hdownDisjoint, hstageCard, hdown]
  have halloc := d2FlowTreeAllocation_after_inactive_recursive_stage
    (.node G low high flowChildren) ha hinv newRoot newLow newHigh
    hnewCover (by simpa [d2FlowTreeRootDeficit] using hrootDrop)
  have hincrement := d2FlowTreeCapacityMass_inactive_stage_increment
    active role quota (h := h) (scale := scale) i flowChildren G low high ha
  have hstageAlloc := d2FlowTreeAllocation_after_inactive_node_ports
    (active := active) (role := role) (quota := quota) flowChildren ha hinv
  rw [← hincrement] at halloc
  simp only [d2FlowTreeRootDeficit] at halloc
  omega

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
