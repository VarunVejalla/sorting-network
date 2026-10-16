import PacketUnequalMerge

/-! A compositional balanced merge tree over disjoint sorted runs. -/

namespace Chvatal.PacketAlignment

private def packetLeftEmbed {m n : Nat} : Fin m ↪o Fin (m + n) :=
  OrderEmbedding.ofStrictMono (Fin.castAdd n) (by
    intro i j hij
    apply Fin.mk_lt_mk.mpr
    simpa using (Fin.mk_lt_mk.mp hij))

private def packetRightEmbed {m n : Nat} : Fin n ↪o Fin (m + n) :=
  OrderEmbedding.ofStrictMono (Fin.natAdd m) (by
    intro i j hij
    apply Fin.mk_lt_mk.mpr
    simpa using (Fin.mk_lt_mk.mp hij))

@[simp] private theorem packetLeftEmbed_apply {m n : Nat} (i : Fin m) :
    packetLeftEmbed (n := n) i = Fin.castAdd n i := rfl

@[simp] private theorem packetRightEmbed_apply {m n : Nat} (i : Fin n) :
    packetRightEmbed (m := m) i = Fin.natAdd m i := rfl

private theorem castAdd_ne_natAdd {m n : Nat} (i : Fin m) (j : Fin n) :
    Fin.castAdd n i ≠ Fin.natAdd m j := by
  intro h
  have hv := congrArg Fin.val h
  simp at hv
  omega

private theorem packetEmbeds_disjoint {m n : Nat} (i : Fin m) (j : Fin n) :
    packetLeftEmbed i ≠ packetRightEmbed j := by
  intro h
  have hv := congrArg Fin.val h
  simp [packetLeftEmbed, packetRightEmbed] at hv
  omega

private theorem packetLeft_not_right {m n : Nat} (i : Fin m) :
    packetLeftEmbed i ∉ Set.range (packetRightEmbed : Fin n → Fin (m + n)) := by
  rintro ⟨j, h⟩
  exact packetEmbeds_disjoint i j h.symm

private theorem packetRight_not_left {m n : Nat} (j : Fin n) :
    packetRightEmbed j ∉ Set.range (packetLeftEmbed : Fin m → Fin (m + n)) := by
  rintro ⟨i, h⟩
  exact packetEmbeds_disjoint i j h

def packetParallel {m n : Nat} (left : ComparatorNetwork m)
    (right : ComparatorNetwork n) : ComparatorNetwork (m + n) := by
  let l := left.scatterEmbed (m + n) packetLeftEmbed
  let r := right.scatterEmbed (m + n) packetRightEmbed
  exact ⟨l.comparators ++ r.comparators⟩

theorem packetParallel_exec_eq {m n : Nat} {α : Type} [LinearOrder α]
    (left : ComparatorNetwork m) (right : ComparatorNetwork n)
    (v : Fin (m + n) → α) :
    (packetParallel left right).exec v =
      Fin.append (fun i => left.exec (fun j => v (Fin.castAdd n j)) i)
        (fun i => right.exec (fun j => v (Fin.natAdd m j)) i) := by
  funext i
  by_cases hi : i.val < m
  · let j : Fin m := ⟨i.val, hi⟩
    have hidx : i = Fin.castAdd n j := by apply Fin.ext; rfl
    rw [hidx]
    dsimp [packetParallel]
    rw [ComparatorNetwork.exec_append]
    rw [← packetLeftEmbed_apply (m := m) (n := n) j]
    rw [ComparatorNetwork.scatterEmbed_exec_outside right (m + n) packetRightEmbed _ _
      (packetLeft_not_right j)]
    have hj : packetLeftEmbed j = Fin.castAdd n j := rfl
    rw [ComparatorNetwork.scatterEmbed_exec_inside left (m + n) packetLeftEmbed]
    rw [packetLeftEmbed_apply, Fin.append_left]
    apply congrArg (fun w : Fin m → α => left.exec w j)
    funext q
    simp [packetLeftEmbed_apply]
  · let j : Fin n := ⟨i.val - m, by have := i.isLt; omega⟩
    have hidx : i = Fin.natAdd m j := by apply Fin.ext; simp [j]; omega
    rw [hidx]
    dsimp [packetParallel]
    rw [ComparatorNetwork.exec_append]
    have hj : packetRightEmbed j = Fin.natAdd m j := rfl
    rw [← hj, ComparatorNetwork.scatterEmbed_exec_inside right (m + n) packetRightEmbed]
    rw [hj, Fin.append_right]
    apply congrArg (fun w : Fin n → α => right.exec w j)
    funext q
    change (left.scatterEmbed (m + n) packetLeftEmbed).exec v (packetRightEmbed q) =
      v (Fin.natAdd m q)
    rw [ComparatorNetwork.scatterEmbed_exec_outside left (m + n) packetLeftEmbed _ _
      (packetRight_not_left q)]
    simp [packetRightEmbed_apply]

theorem packetParallel_depth_le {m n : Nat} (left : ComparatorNetwork m)
    (right : ComparatorNetwork n) :
    (packetParallel left right).depth ≤ max left.depth right.depth := by
  let l := left.scatterEmbed (m + n) packetLeftEmbed
  let r := right.scatterEmbed (m + n) packetRightEmbed
  have hl : l.depth ≤ max left.depth right.depth :=
    (depth_scatterEmbed_le _ _ _).trans (le_max_left _ _)
  have hr : r.depth ≤ max left.depth right.depth :=
    (depth_scatterEmbed_le _ _ _).trans (le_max_right _ _)
  have hflat := depth_flatMap_disjoint [false, true]
    (fun b => if b then r.comparators else l.comparators)
    (max left.depth right.depth)
    (by intro b hb; simp only [List.mem_cons, List.mem_nil_iff, or_false] at hb
        rcases hb with rfl | rfl <;> simp [hl, hr])
    (by
      refine List.Pairwise.cons ?_ (List.pairwise_singleton _ _)
      intro b hb
      have hb' : b = true := by simpa using hb
      subst b
      intro c hc d hd
      dsimp only [l, r, ComparatorNetwork.scatterEmbed] at hc hd
      rcases List.mem_map.mp hc with ⟨c₀, _, rfl⟩
      rcases List.mem_map.mp hd with ⟨d₀, _, rfl⟩
      change ((packetLeftEmbed c₀.i ≠ packetRightEmbed d₀.i ∧
        packetLeftEmbed c₀.i ≠ packetRightEmbed d₀.j) ∧
        (packetLeftEmbed c₀.j ≠ packetRightEmbed d₀.i ∧
        packetLeftEmbed c₀.j ≠ packetRightEmbed d₀.j))
      exact ⟨⟨packetEmbeds_disjoint _ _, packetEmbeds_disjoint _ _⟩,
        ⟨packetEmbeds_disjoint _ _, packetEmbeds_disjoint _ _⟩⟩)
  simpa [packetParallel, l, r] using hflat

def packetMergeAfterParallel {m n : Nat} (left : ComparatorNetwork m)
    (right : ComparatorNetwork n) (merge : ComparatorNetwork (m + n)) :
    ComparatorNetwork (m + n) :=
  ⟨(packetParallel left right).comparators ++ merge.comparators⟩

theorem packetMergeAfterParallel_exec_eq {m n : Nat} {α : Type}
    [LinearOrder α] (left : ComparatorNetwork m) (right : ComparatorNetwork n)
    (merge : ComparatorNetwork (m + n)) (v : Fin (m + n) → α) :
    (packetMergeAfterParallel left right merge).exec v =
      merge.exec ((packetParallel left right).exec v) := by
  simp [packetMergeAfterParallel, ComparatorNetwork.exec, List.foldl_append]

theorem packetMergeAfterParallel_depth_le {m n : Nat}
    (left : ComparatorNetwork m) (right : ComparatorNetwork n)
    (merge : ComparatorNetwork (m + n)) :
    (packetMergeAfterParallel left right merge).depth ≤
      max left.depth right.depth + merge.depth := by
  exact (ComparatorNetwork.depth_append_le _ _).trans
    (Nat.add_le_add_right (packetParallel_depth_le left right) _)

/-- A merge tree records, at each internal node, a checked network that merges
any two sorted child runs. -/
inductive PacketMergeTree (α : Type) [LinearOrder α] : Nat → Type where
  | leaf : PacketMergeTree α 64
  | node {m n : Nat} (left : PacketMergeTree α m) (right : PacketMergeTree α n)
      (merge : ComparatorNetwork (m + n))
      (mergeCost : Nat) (merge_depth : merge.depth ≤ mergeCost)
      (merge_sorts : ∀ (A : Fin m → α) (B : Fin n → α),
        Monotone A → Monotone B → Monotone (merge.exec (Fin.append A B))) :
      PacketMergeTree α (m + n)

namespace PacketMergeTree

def network {α : Type} [LinearOrder α] {N : Nat} :
    PacketMergeTree α N → ComparatorNetwork N
  | .leaf => ⟨[]⟩
  | .node left right merge _ _ _ =>
      packetMergeAfterParallel left.network right.network merge

def RunsSorted {α : Type} [LinearOrder α] {N : Nat} :
    (tree : PacketMergeTree α N) → (Fin N → α) → Prop
  | .leaf, v => Monotone v
  | .node (m := m) (n := n) left right _ _ _ _, v =>
      RunsSorted left (fun i => v (Fin.castAdd n i)) ∧
      RunsSorted right (fun j => v (Fin.natAdd m j))

def depthBudget {α : Type} [LinearOrder α] {N : Nat} :
    PacketMergeTree α N → Nat
  | .leaf => 0
  | .node left right _ mergeCost _ _ =>
      max left.depthBudget right.depthBudget + mergeCost

theorem network_sorts {α : Type} [LinearOrder α] {N : Nat}
    (tree : PacketMergeTree α N) (v : Fin N → α)
    (hv : tree.RunsSorted v) : Monotone (tree.network.exec v) := by
  induction tree with
  | leaf => simpa [RunsSorted, network] using hv
  | @node m n left right merge mergeCost hdepth hmerge ihLeft ihRight =>
    dsimp [RunsSorted] at hv
    rcases hv with ⟨hleft, hright⟩
    have hleftSorted := ihLeft (fun i => v (Fin.castAdd n i)) hleft
    have hrightSorted := ihRight (fun j => v (Fin.natAdd m j)) hright
    rw [network, packetMergeAfterParallel_exec_eq, packetParallel_exec_eq]
    exact hmerge _ _ hleftSorted hrightSorted

theorem network_depth_le {α : Type} [LinearOrder α] {N : Nat}
    (tree : PacketMergeTree α N) : tree.network.depth ≤ tree.depthBudget := by
  induction tree with
  | leaf => simp [network, depthBudget, ComparatorNetwork.depth]
  | @node m n left right merge mergeCost hdepth hmerge ihLeft ihRight =>
    have h := packetMergeAfterParallel_depth_le left.network right.network merge
    calc
      (packetMergeAfterParallel left.network right.network merge).depth ≤
          max left.network.depth right.network.depth + merge.depth := h
      _ ≤ max left.depthBudget right.depthBudget + mergeCost := by
        exact Nat.add_le_add (max_le_max ihLeft ihRight) hdepth

theorem scatter_sorts {α : Type} [LinearOrder α] {N M : Nat}
    (tree : PacketMergeTree α M) (e : Fin M ↪o Fin N) (v : Fin N → α)
    (hv : tree.RunsSorted (fun i => v (e i))) :
    Monotone (fun i => (tree.network.scatterEmbed N e).exec v (e i)) := by
  have hs := network_sorts tree (fun i => v (e i)) hv
  simpa only [ComparatorNetwork.scatterEmbed_exec_inside] using hs

theorem scatter_depth_le {α : Type} [LinearOrder α] {N M : Nat}
    (tree : PacketMergeTree α M) (e : Fin M ↪o Fin N) :
    (tree.network.scatterEmbed N e).depth ≤ tree.depthBudget := by
  exact (depth_scatterEmbed_le _ _ _).trans (network_depth_le tree)

end PacketMergeTree

private theorem packetPowPairSizeEq (k : Nat) :
    2 ^ k + 2 ^ k = 2 ^ (k + 1) := by
  rw [pow_succ]
  omega

private theorem oddEvenMerge_sorts_runs {k : Nat} {α : Type} [LinearOrder α]
    (A B : Fin (2 ^ k) → α) (hA : Monotone A) (hB : Monotone B) :
    Monotone ((oddEvenMergeNet (k + 1)).exec
      (fun i => Fin.append A B (Fin.cast (packetPowPairSizeEq k).symm i))) := by
  let v : Fin (2 ^ (k + 1)) → α := fun i =>
    Fin.append A B (Fin.cast (packetPowPairSizeEq k).symm i)
  have hsorted :
      Monotone (fun i : Fin (2 ^ k) =>
        v (Fin.cast (packetPowPairSizeEq k) (Fin.castAdd (2 ^ k) i))) ∧
      Monotone (fun i : Fin (2 ^ k) =>
        v (Fin.cast (packetPowPairSizeEq k) (Fin.natAdd (2 ^ k) i))) := by
    constructor
    · simpa [v, Fin.append_left] using hA
    · have heq :
          (fun i : Fin (2 ^ k) =>
            v (Fin.cast (packetPowPairSizeEq k) (Fin.natAdd (2 ^ k) i))) = B := by
        funext i
        dsimp [v]
        rw [Fin.append_right]
      rw [heq]
      exact hB
  have hs := oddEvenMergeNet_sorts_two_runs k v hsorted
  simpa [v] using hs

def packetPowerTree0 {α : Type} [LinearOrder α] : PacketMergeTree α 64 := .leaf

def packetPowerTree1 {α : Type} [LinearOrder α] : PacketMergeTree α 128 :=
  .node packetPowerTree0 packetPowerTree0 (oddEvenMergeNet 7) 7
    (oddEvenMergeNet_depth_le 7)
    (by intro A B hA hB; exact oddEvenMerge_sorts_runs (k := 6) A B hA hB)

def packetPowerTree2 {α : Type} [LinearOrder α] : PacketMergeTree α 256 :=
  .node packetPowerTree1 packetPowerTree1 (oddEvenMergeNet 8) 8
    (oddEvenMergeNet_depth_le 8)
    (by intro A B hA hB; exact oddEvenMerge_sorts_runs (k := 7) A B hA hB)

def packetPowerTree3 {α : Type} [LinearOrder α] : PacketMergeTree α 512 :=
  .node packetPowerTree2 packetPowerTree2 (oddEvenMergeNet 9) 9
    (oddEvenMergeNet_depth_le 9)
    (by intro A B hA hB; exact oddEvenMerge_sorts_runs (k := 8) A B hA hB)

def packetPowerTree4 {α : Type} [LinearOrder α] : PacketMergeTree α 1024 :=
  .node packetPowerTree3 packetPowerTree3 (oddEvenMergeNet 10) 10
    (oddEvenMergeNet_depth_le 10)
    (by intro A B hA hB; exact oddEvenMerge_sorts_runs (k := 9) A B hA hB)

def packetPowerTree5 {α : Type} [LinearOrder α] : PacketMergeTree α 2048 :=
  .node packetPowerTree4 packetPowerTree4 (oddEvenMergeNet 11) 11
    (oddEvenMergeNet_depth_le 11)
    (by intro A B hA hB; exact oddEvenMerge_sorts_runs (k := 10) A B hA hB)

def packetOddTree1 {α : Type} [LinearOrder α] : PacketMergeTree α 64 := .leaf

def packetOddTree2 {α : Type} [LinearOrder α] : PacketMergeTree α 192 :=
  .node packetPowerTree1 packetOddTree1 unequalTail3Lift6 8 unequalTail3Lift6_depth_le
    (by intro A B hA hB; exact unequalTail3Lift6_sorts_two_runs A B hA hB)

def packetOddTree3 {α : Type} [LinearOrder α] : PacketMergeTree α 448 :=
  .node packetPowerTree2 packetOddTree2 unequalTail7Lift6 9 unequalTail7Lift6_depth_le
    (by intro A B hA hB; exact unequalTail7Lift6_sorts_two_runs A B hA hB)

def packetOddTree4 {α : Type} [LinearOrder α] : PacketMergeTree α 960 :=
  .node packetPowerTree3 packetOddTree3 unequalTail15Lift6 10 unequalTail15Lift6_depth_le
    (by intro A B hA hB; exact unequalTail15Lift6_sorts_two_runs A B hA hB)

def packetOddTree5 {α : Type} [LinearOrder α] : PacketMergeTree α 1984 :=
  .node packetPowerTree4 packetOddTree4 unequalTail31Lift6 11 unequalTail31Lift6_depth_le
    (by intro A B hA hB; exact unequalTail31Lift6_sorts_two_runs A B hA hB)

def packetOddTree6 {α : Type} [LinearOrder α] : PacketMergeTree α 4032 :=
  .node packetPowerTree5 packetOddTree5 unequalTail63Lift6 12 unequalTail63Lift6_depth_le
    (by intro A B hA hB; exact unequalTail63Lift6_sorts_two_runs A B hA hB)

theorem packetOddTree6_sorts {α : Type} [LinearOrder α]
    (v : Fin 4032 → α) (hv : (packetOddTree6 (α := α)).RunsSorted v) :
    Monotone ((packetOddTree6 (α := α)).network.exec v) :=
  PacketMergeTree.network_sorts (packetOddTree6 (α := α)) v hv

theorem packetOddTree6_depthBudget_le : (packetOddTree6 (α := Bool)).depthBudget ≤ 57 := by
  have hp1 : (packetPowerTree1 (α := Bool)).depthBudget ≤ 7 := by
    change max 0 0 + 7 ≤ 7
    omega
  have hp2 : (packetPowerTree2 (α := Bool)).depthBudget ≤ 15 := by
    change max (packetPowerTree1 (α := Bool)).depthBudget
      (packetPowerTree1 (α := Bool)).depthBudget + 8 ≤ 15
    calc
      _ ≤ max 7 7 + 8 := by omega
      _ = 15 := by omega
  have hp3 : (packetPowerTree3 (α := Bool)).depthBudget ≤ 24 := by
    change max (packetPowerTree2 (α := Bool)).depthBudget
      (packetPowerTree2 (α := Bool)).depthBudget + 9 ≤ 24
    calc
      _ ≤ max 15 15 + 9 := by omega
      _ = 24 := by omega
  have hp4 : (packetPowerTree4 (α := Bool)).depthBudget ≤ 34 := by
    change max (packetPowerTree3 (α := Bool)).depthBudget
      (packetPowerTree3 (α := Bool)).depthBudget + 10 ≤ 34
    calc
      _ ≤ max 24 24 + 10 := by omega
      _ = 34 := by omega
  have hp5 : (packetPowerTree5 (α := Bool)).depthBudget ≤ 45 := by
    change max (packetPowerTree4 (α := Bool)).depthBudget
      (packetPowerTree4 (α := Bool)).depthBudget + 11 ≤ 45
    calc
      _ ≤ max 34 34 + 11 := by omega
      _ = 45 := by omega
  have ho1 : (packetOddTree1 (α := Bool)).depthBudget = 0 := by
    simp [packetOddTree1, PacketMergeTree.depthBudget]
  have ho2 : (packetOddTree2 (α := Bool)).depthBudget ≤ 15 := by
    change max (packetPowerTree1 (α := Bool)).depthBudget
      (packetOddTree1 (α := Bool)).depthBudget + 8 ≤ 15
    calc
      _ ≤ max 7 0 + 8 := by omega
      _ = 15 := by omega
  have ho3 : (packetOddTree3 (α := Bool)).depthBudget ≤ 24 := by
    change max (packetPowerTree2 (α := Bool)).depthBudget
      (packetOddTree2 (α := Bool)).depthBudget + 9 ≤ 24
    calc
      _ ≤ max 15 15 + 9 := by omega
      _ = 24 := by omega
  have ho4 : (packetOddTree4 (α := Bool)).depthBudget ≤ 34 := by
    change max (packetPowerTree3 (α := Bool)).depthBudget
      (packetOddTree3 (α := Bool)).depthBudget + 10 ≤ 34
    calc
      _ ≤ max 24 24 + 10 := by omega
      _ = 34 := by omega
  have ho5 : (packetOddTree5 (α := Bool)).depthBudget ≤ 45 := by
    change max (packetPowerTree4 (α := Bool)).depthBudget
      (packetOddTree4 (α := Bool)).depthBudget + 11 ≤ 45
    calc
      _ ≤ max 34 34 + 11 := by omega
      _ = 45 := by omega
  change max (packetPowerTree5 (α := Bool)).depthBudget
    (packetOddTree5 (α := Bool)).depthBudget + 12 ≤ 57
  calc
    _ ≤ max 45 45 + 12 := by omega
    _ = 57 := by omega

theorem packetOddTree6_depth_le : (packetOddTree6 (α := Bool)).network.depth ≤ 57 :=
  (PacketMergeTree.network_depth_le (packetOddTree6 (α := Bool))).trans packetOddTree6_depthBudget_le

end Chvatal.PacketAlignment
