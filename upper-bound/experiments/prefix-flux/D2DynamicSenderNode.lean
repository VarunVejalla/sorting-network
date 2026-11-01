import D2DynamicSenderCardinality
import D2DynamicSenderLayout
import D2FlowPathLast

/-! A finite flat index for every node of a full D2 flow tree. -/

namespace Chvatal.D2OrdinaryRankRouting

open Chvatal
open Chvatal.D2Reserve

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

/-- The child at port `j`, if it lies within the finite tree. -/
def d2SenderNodeChild? {depth : Nat} (node : D2SenderNode depth)
    (j : Fin 8) : Option (D2SenderNode depth) := by
  rcases node with ⟨level, path⟩
  by_cases hlt : level.val < depth
  · exact some ⟨⟨level.val + 1, by omega⟩,
      d2FlowPathSnoc path j⟩
  · exact none

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

end Chvatal.D2OrdinaryRankRouting
