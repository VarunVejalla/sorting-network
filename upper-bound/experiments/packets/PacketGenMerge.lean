import OddEvenMerge64
import AKS.Sort.Untangle

/-! Support-aware packet merging in the repository's generalized comparator
model. An arbitrary injective wire placement preserves execution and depth.
The final sorting theorem must still satisfy `Untangle.untangle` before this
can imply an ordinary sorting-network bound. -/

namespace Chvatal.PacketAlignment

open Untangle

def genScatterComparator {m N : Nat} (e : Fin m ↪ Fin N) (c : Comparator m) :
    GenComparator N := ⟨e c.i, e c.j, fun h => (ne_of_lt c.h) (e.injective h)⟩

def genScatter {m N : Nat} (net : ComparatorNetwork m) (e : Fin m ↪ Fin N) :
    GenNetwork N := ⟨net.comparators.map (genScatterComparator e)⟩

theorem genScatter_exec_inside {m N : Nat} {α : Type} [LinearOrder α]
    (net : ComparatorNetwork m) (e : Fin m ↪ Fin N) (v : Fin N → α) (i : Fin m) :
    (genScatter net e).exec v (e i) = net.exec (v ∘ e) i := by
  suffices hf : ∀ (cs : List (Comparator m)) (v : Fin N → α),
      (fun j => (cs.map (genScatterComparator e)).foldl
        (fun acc c => GenComparator.apply c acc) v (e j)) =
        cs.foldl (fun acc c => Comparator.apply c acc) (v ∘ e) from
    congrFun (hf net.comparators v) i
  intro cs
  induction cs with
  | nil => intro v; rfl
  | cons c cs ih =>
    intro v
    simp only [List.map_cons, List.foldl_cons]
    rw [ih]
    congr 1
    funext j
    simp only [genScatterComparator, GenComparator.apply, Comparator.apply,
      Function.comp, e.injective.eq_iff]

theorem genScatter_exec_outside {m N : Nat} {α : Type} [LinearOrder α]
    (net : ComparatorNetwork m) (e : Fin m ↪ Fin N) (v : Fin N → α)
    (w : Fin N) (hw : w ∉ Set.range e) : (genScatter net e).exec v w = v w := by
  have hf : ∀ (cs : List (Comparator m)) (v : Fin N → α),
      (cs.map (genScatterComparator e)).foldl (fun acc c => GenComparator.apply c acc) v w = v w := by
    intro cs
    induction cs with
    | nil => intro v; rfl
    | cons c cs ih =>
      intro v
      simp only [List.map_cons, List.foldl_cons]
      rw [ih]
      have hwi : w ≠ e c.i := fun h => hw ⟨c.i, h.symm⟩
      have hwj : w ≠ e c.j := fun h => hw ⟨c.j, h.symm⟩
      simp [genScatterComparator, GenComparator.apply, hwi, hwj]
  exact hf net.comparators v

private theorem genScatter_foldl_depth {m N : Nat} (cs : List (Comparator m))
    (e : Fin m ↪ Fin N) (wt₀ : Fin m → Nat) (wt : Fin N → Nat) (dm : Nat)
    (hwt : ∀ j, wt (e j) = wt₀ j) :
    ((cs.map (genScatterComparator e)).foldl genDepthStep (wt, dm)).2 =
      (cs.foldl depthStep (wt₀, dm)).2 := by
  induction cs generalizing wt₀ wt dm with
  | nil => rfl
  | cons c cs ih =>
    simp only [List.map_cons, List.foldl_cons]
    have hnext := ih (depthStep (wt₀, dm) c).1
      (genDepthStep (wt, dm) (genScatterComparator e c)).1
      (genDepthStep (wt, dm) (genScatterComparator e c)).2 (fun j => by
        simp only [genScatterComparator, genDepthStep, depthStep,
          Function.update_apply, hwt, e.injective.eq_iff])
    simp only [genScatterComparator, genDepthStep, depthStep, hwt] at hnext ⊢
    exact hnext

/-- No physical-order hypothesis is needed for generalized scattering. -/
theorem genScatter_depth {m N : Nat} (net : ComparatorNetwork m) (e : Fin m ↪ Fin N) :
    (genScatter net e).depth = net.depth :=
  genScatter_foldl_depth net.comparators e (fun _ => 0) (fun _ => 0) 0 (fun _ => rfl)

private theorem genMergeWidthEq (k : Nat) : 2 ^ k + 2 ^ k = 2 ^ (k + 1) := by
  rw [pow_succ]
  omega

theorem genMerge_sorts_two_runs {N : Nat} {α : Type} [LinearOrder α]
    (k : Nat) (e : Fin (2 ^ (k + 1)) ↪ Fin N) (v : Fin N → α)
    (hA : Monotone (fun i : Fin (2 ^ k) =>
      v (e (Fin.cast (genMergeWidthEq k) (Fin.castAdd (2 ^ k) i)))))
    (hB : Monotone (fun i : Fin (2 ^ k) =>
      v (e (Fin.cast (genMergeWidthEq k) (Fin.natAdd (2 ^ k) i))))) :
    Monotone (fun i => (genScatter (oddEvenMergeNet (k + 1)) e).exec v (e i)) := by
  have hs := oddEvenMergeNet_sorts_two_runs k (v ∘ e) ⟨hA, hB⟩
  simpa only [genScatter_exec_inside] using hs

theorem genMerge_depth_le {N : Nat} (k : Nat) (e : Fin (2 ^ k) ↪ Fin N) :
    (genScatter (oddEvenMergeNet k) e).depth ≤ k := by
  rw [genScatter_depth]
  exact oddEvenMergeNet_depth_le k

theorem genSorted_dealt_counts {m N : Nat} (net : ComparatorNetwork (2 * m))
    (e : Fin (2 * m) ↪ Fin N) (v : Fin N → Bool)
    (hs : Monotone (net.exec (v ∘ e))) :
    boolTrueCount (fun i : Fin m => (genScatter net e).exec v (e (evenWire m i))) =
        boolTrueCount (v ∘ e) / 2 ∧
      boolTrueCount (fun i : Fin m => (genScatter net e).exec v (e (oddWire m i))) =
        (boolTrueCount (v ∘ e) + 1) / 2 := by
  have hc := sorted_bool_parity_counts (net.exec (v ∘ e)) hs
  rw [boolTrueCount_exec] at hc
  simpa only [genScatter_exec_inside] using hc

/-- Two ascending 64-wire packets, placed on any injective list of 128 wires,
are merged in seven generalized-comparator layers. -/
theorem genMerge128_sorts {N : Nat} {α : Type} [LinearOrder α]
    (e : Fin 128 ↪ Fin N) (v : Fin N → α)
    (hA : Monotone (fun i : Fin 64 => v (e (Fin.castAdd 64 i))))
    (hB : Monotone (fun i : Fin 64 => v (e (Fin.natAdd 64 i)))) :
    Monotone (fun i => (genScatter (oddEvenMergeNet 7) e).exec v (e i)) := by
  have hs : Monotone ((oddEvenMergeNet 7).exec (v ∘ e)) := by
    apply oddEvenMergeNet_sorts_two_runs 6
    constructor
    · simpa using hA
    · simpa using hB
  simpa only [genScatter_exec_inside] using hs

theorem genMerge128_depth_le {N : Nat} (e : Fin 128 ↪ Fin N) :
    (genScatter (oddEvenMergeNet 7) e).depth ≤ 7 := by
  rw [genScatter_depth]
  exact oddEvenMergeNet_depth_le 7

/-- Alternating ranks are fixed output packet supports, ready for the next
round's packet embedding. Both packets are ascending. -/
theorem genMerge128_dealt_lanes_sorted {N : Nat} {α : Type} [LinearOrder α]
    (e : Fin 128 ↪ Fin N) (v : Fin N → α)
    (hA : Monotone (fun i : Fin 64 => v (e (Fin.castAdd 64 i))))
    (hB : Monotone (fun i : Fin 64 => v (e (Fin.natAdd 64 i)))) :
    Monotone (fun i : Fin 64 => (genScatter (oddEvenMergeNet 7) e).exec v
      (e ⟨2 * i.val, by omega⟩)) ∧
    Monotone (fun i : Fin 64 => (genScatter (oddEvenMergeNet 7) e).exec v
      (e ⟨2 * i.val + 1, by omega⟩)) := by
  have hs := genMerge128_sorts e v hA hB
  constructor <;> intro i j hij <;> apply hs <;> apply Fin.mk_le_mk.mpr <;>
    have hv := Fin.le_def.mp hij <;> omega

/-- The exact integer averaging law on arbitrary packet placements. For true
counts the even packet receives the floor and the odd packet the ceiling;
zero counts have the opposite orientation. -/
theorem genMerge128_dealt_counts {N : Nat} (e : Fin 128 ↪ Fin N) (v : Fin N → Bool)
    (hA : Monotone (fun i : Fin 64 => v (e (Fin.castAdd 64 i))))
    (hB : Monotone (fun i : Fin 64 => v (e (Fin.natAdd 64 i)))) :
    let H := boolTrueCount (fun i : Fin 64 => v (e (Fin.castAdd 64 i))) +
      boolTrueCount (fun i : Fin 64 => v (e (Fin.natAdd 64 i)))
    boolTrueCount (fun i : Fin 64 => (genScatter (oddEvenMergeNet 7) e).exec v
      (e (evenWire 64 i))) = H / 2 ∧
    boolTrueCount (fun i : Fin 64 => (genScatter (oddEvenMergeNet 7) e).exec v
      (e (oddWire 64 i))) = (H + 1) / 2 := by
  have hs : Monotone ((oddEvenMergeNet 7).exec (v ∘ e)) := by
    apply oddEvenMergeNet_sorts_two_runs 6
    constructor
    · simpa using hA
    · simpa using hB
  have hc := sorted_bool_parity_counts (m := 64) ((oddEvenMergeNet 7).exec (v ∘ e)) hs
  rw [boolTrueCount_exec] at hc
  have hsum := boolTrueCount_halves (m := 64) (v ∘ e)
  rw [hsum] at hc
  simpa only [genScatter_exec_inside, Function.comp_apply] using hc

theorem genScatter_exec_threshold {m N : Nat} {α : Type} [LinearOrder α]
    (net : ComparatorNetwork m) (e : Fin m ↪ Fin N) (v : Fin N → α) (t : α) :
    (genScatter net e).exec (fun w => decide (t ≤ v w)) =
      fun w => decide (t ≤ (genScatter net e).exec v w) := by
  funext w
  by_cases hw : w ∈ Set.range e
  · obtain ⟨i, rfl⟩ := hw
    rw [genScatter_exec_inside, genScatter_exec_inside]
    exact congrFun (exec_threshold net (v ∘ e) t) i
  · rw [genScatter_exec_outside net e _ w hw, genScatter_exec_outside net e v w hw]

/-- The exact count law holds simultaneously at every value threshold of a
sorted output, not only for Boolean input values. -/
theorem genSorted_threshold_counts {m N : Nat} {α : Type} [LinearOrder α]
    (net : ComparatorNetwork (2 * m)) (e : Fin (2 * m) ↪ Fin N)
    (v : Fin N → α) (hs : Monotone (net.exec (v ∘ e))) (t : α) :
    let H := boolTrueCount (fun i : Fin (2 * m) => decide (t ≤ v (e i)))
    boolTrueCount (fun i : Fin m => decide
      (t ≤ (genScatter net e).exec v (e (evenWire m i)))) = H / 2 ∧
    boolTrueCount (fun i : Fin m => decide
      (t ≤ (genScatter net e).exec v (e (oddWire m i)))) = (H + 1) / 2 := by
  let b : Fin N → Bool := fun w => decide (t ≤ v w)
  have hm : Monotone (fun x : α => decide (t ≤ x)) := by
    intro x y hxy
    by_cases hx : t ≤ x
    · have hy : t ≤ y := hx.trans hxy
      simp [hx, hy]
    · simp [hx]
  have hb : Monotone (net.exec (b ∘ e)) := by
    change Monotone (net.exec (fun i => decide (t ≤ (v ∘ e) i)))
    rw [exec_threshold]
    exact hm.comp hs
  have hc := genSorted_dealt_counts net e b hb
  simpa only [b, genScatter_exec_threshold, Function.comp_apply] using hc

private def sumPacketEmbedding {m N : Nat} (a b : Fin m ↪ Fin N)
    (hdis : ∀ i j, a i ≠ b j) : Fin m ⊕ Fin m ↪ Fin N :=
  ⟨Sum.elim a b, by
    intro x y hxy
    cases x with
    | inl i => cases y with
      | inl j => exact congrArg Sum.inl (a.injective hxy)
      | inr j => exact False.elim (hdis i j hxy)
    | inr i => cases y with
      | inl j => exact False.elim (hdis j i hxy.symm)
      | inr j => exact congrArg Sum.inr (b.injective hxy)⟩

/-- Join two disjoint packet embeddings by their logical packet order. No
condition compares the physical positions of the two packets. -/
def joinPacketEmbedding {m N : Nat} (a b : Fin m ↪ Fin N)
    (hdis : ∀ i j, a i ≠ b j) : Fin (m + m) ↪ Fin N :=
  (finSumFinEquiv : Fin m ⊕ Fin m ≃ Fin (m + m)).symm.toEmbedding.trans
    (sumPacketEmbedding a b hdis)

@[simp] theorem joinPacketEmbedding_left {m N : Nat} (a b : Fin m ↪ Fin N)
    (hdis : ∀ i j, a i ≠ b j) (i : Fin m) :
    joinPacketEmbedding a b hdis (Fin.castAdd m i) = a i := by
  change Sum.elim a b (finSumFinEquiv.symm (Fin.castAdd m i)) = a i
  rw [finSumFinEquiv_symm_apply_castAdd]
  rfl

@[simp] theorem joinPacketEmbedding_right {m N : Nat} (a b : Fin m ↪ Fin N)
    (hdis : ∀ i j, a i ≠ b j) (i : Fin m) :
    joinPacketEmbedding a b hdis (Fin.natAdd m i) = b i := by
  change Sum.elim a b (finSumFinEquiv.symm (Fin.natAdd m i)) = b i
  rw [finSumFinEquiv_symm_apply_natAdd]
  rfl

def dealEvenEmbedding {N : Nat} (e : Fin 128 ↪ Fin N) : Fin 64 ↪ Fin N :=
  ⟨fun i => e (evenWire 64 i), by
    intro i j hij
    have hv := congrArg Fin.val (e.injective hij)
    change 2 * i.val = 2 * j.val at hv
    exact Fin.ext (by omega)⟩

def dealOddEmbedding {N : Nat} (e : Fin 128 ↪ Fin N) : Fin 64 ↪ Fin N :=
  ⟨fun i => e (oddWire 64 i), by
    intro i j hij
    have hv := congrArg Fin.val (e.injective hij)
    change 2 * i.val + 1 = 2 * j.val + 1 at hv
    exact Fin.ext (by omega)⟩

theorem dealEmbeddings_disjoint {N : Nat} (e : Fin 128 ↪ Fin N) :
    ∀ i j, dealEvenEmbedding e i ≠ dealOddEmbedding e j := by
  intro i j heq
  have hv := congrArg Fin.val (e.injective heq)
  change 2 * i.val = 2 * j.val + 1 at hv
  omega

/-- The two fixed output packet supports partition the consumed support. -/
theorem dealEmbeddings_partition {N : Nat} (e : Fin 128 ↪ Fin N) :
    Set.range (dealEvenEmbedding e) ∪ Set.range (dealOddEmbedding e) = Set.range e := by
  ext w
  constructor
  · rintro (⟨i, rfl⟩ | ⟨i, rfl⟩)
    · exact ⟨evenWire 64 i, rfl⟩
    · exact ⟨oddWire 64 i, rfl⟩
  · rintro ⟨j, rfl⟩
    let i : Fin 64 := ⟨j.val / 2, by have := j.isLt; omega⟩
    by_cases he : j.val % 2 = 0
    · left
      refine ⟨i, congrArg e ?_⟩
      apply Fin.ext
      change 2 * (j.val / 2) = j.val
      omega
    · right
      refine ⟨i, congrArg e ?_⟩
      apply Fin.ext
      change 2 * (j.val / 2) + 1 = j.val
      omega

/-- A composable local packet step: arbitrary disjoint sorted packets in,
arbitrary disjoint sorted packets out, with all embeddings input-independent. -/
theorem genPacketPair_lanes_sorted {N : Nat} {α : Type} [LinearOrder α]
    (a b : Fin 64 ↪ Fin N) (hdis : ∀ i j, a i ≠ b j) (v : Fin N → α)
    (ha : Monotone (v ∘ a)) (hb : Monotone (v ∘ b)) :
    let e := joinPacketEmbedding a b hdis
    let G := genScatter (oddEvenMergeNet 7) e
    Monotone (G.exec v ∘ dealEvenEmbedding e) ∧
      Monotone (G.exec v ∘ dealOddEmbedding e) := by
  apply genMerge128_dealt_lanes_sorted (joinPacketEmbedding a b hdis) v
  · intro i j hij
    dsimp only
    rw [joinPacketEmbedding_left, joinPacketEmbedding_left]
    exact ha hij
  · intro i j hij
    dsimp only
    rw [joinPacketEmbedding_right, joinPacketEmbedding_right]
    exact hb hij

end Chvatal.PacketAlignment
