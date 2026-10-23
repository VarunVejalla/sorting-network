module
/-
  # Disjoint segment sorts at arbitrary offsets (band repair centred on the cuts, L3)

  `segmentSort m b offs` on `m` wires sorts every segment `[o, o + 2^b)`, `o ∈ offs`, with Batcher's
  bitonic sort (a segment that does not fit is skipped). For pairwise disjoint segments:
  * depth `≤ bitonicDepthBudget b` (the segments run in parallel);
  * wires outside every segment are unchanged;
  * on each segment the output is `bitonicSort b` applied to that segment's input, so it is sorted and
    is a permutation of the segment's input ("keys never leave their segment").
  This is the band repair of `experiments/sub500-screen/PROOFS-L3-L4.md` (L3, full proof): segments
  `[i - W, i + W)` centred on the output cuts, clipped segments shifted to `[0, 2W)`.
  `BlockSort.lean`'s aligned `blockSortNetwork` is the case of offsets at multiples of `2^b`.
-/

public import AKS.Bitonic.Sorts

@[expose] public section

open ComparatorNetwork

namespace Bitonic

/-- Bitonic sort of the segment `[o, o + 2^b)` of `m` wires (empty if it does not fit). -/
def segNet (m b o : ℕ) : ComparatorNetwork m :=
  if h : o + 2 ^ b ≤ m then (bitonicSort b).shiftEmbed m o h else ⟨[]⟩

/-- Sort every segment `[o, o + 2^b)`, `o ∈ offs`. -/
def segmentSort (m b : ℕ) (offs : List ℕ) : ComparatorNetwork m :=
  ⟨offs.flatMap fun o => (segNet m b o).comparators⟩

/-- The segments `[o, o + 2^b)`, `o ∈ offs`, are pairwise disjoint. -/
def SegDisjoint (b : ℕ) (offs : List ℕ) : Prop :=
  offs.Pairwise fun o₁ o₂ => o₁ + 2 ^ b ≤ o₂ ∨ o₂ + 2 ^ b ≤ o₁

/-- Every comparator of `segNet m b o` lies inside `[o, o + 2^b)`. -/
theorem segNet_wires {m b o : ℕ} {c : Comparator m} (hc : c ∈ (segNet m b o).comparators) :
    o ≤ c.i.val ∧ c.i.val < o + 2 ^ b ∧ o ≤ c.j.val ∧ c.j.val < o + 2 ^ b := by
  unfold segNet at hc
  split_ifs at hc with h
  · simp only [ComparatorNetwork.shiftEmbed, ComparatorNetwork.scatterEmbed, List.mem_map] at hc
    obtain ⟨c', -, rfl⟩ := hc
    have := c'.i.2; have := c'.j.2
    simp only [shiftEmb, OrderEmbedding.coe_ofStrictMono]
    omega
  · simp at hc

theorem segNet_depth_le (m b o : ℕ) : (segNet m b o).depth ≤ bitonicDepthBudget b := by
  unfold segNet
  split_ifs with h
  · exact (depth_shiftEmbed_le _ m o h).trans (bitonicSort_depth_le_budget b)
  · simp [depth_nil]

/-- **Disjoint segments are sorted in parallel**: depth at most one bitonic sort. -/
theorem segmentSort_depth_le (m b : ℕ) {offs : List ℕ} (hd : SegDisjoint b offs) :
    (segmentSort m b offs).depth ≤ bitonicDepthBudget b := by
  unfold segmentSort
  refine depth_flatMap_disjoint offs (fun o => (segNet m b o).comparators) _
    (fun o _ => segNet_depth_le m b o) ?_
  refine hd.imp fun {o₁ o₂} h12 c₁ hc₁ c₂ hc₂ => ?_
  have w1 := segNet_wires hc₁
  have w2 := segNet_wires hc₂
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> intro h <;> have := congrArg Fin.val h <;> omega

/-- A wire of segment `o` is untouched by the network of any segment disjoint from it. -/
theorem segNet_untouched {m b o a : ℕ} (hoa : a + 2 ^ b ≤ o ∨ o + 2 ^ b ≤ a) {k : Fin m}
    (hk : o ≤ k.val ∧ k.val < o + 2 ^ b) :
    ∀ c ∈ (segNet m b a).comparators, k ≠ c.i ∧ k ≠ c.j := by
  intro c hc
  have w := segNet_wires hc
  refine ⟨?_, ?_⟩ <;> intro h <;> have := congrArg Fin.val h <;> omega

/-- **Wires outside every segment are unchanged.** -/
theorem segmentSort_exec_outside {m b : ℕ} (offs : List ℕ) {α : Type*} [LinearOrder α]
    (v : Fin m → α) (k : Fin m) (hk : ∀ o ∈ offs, k.val < o ∨ o + 2 ^ b ≤ k.val) :
    (segmentSort m b offs).exec v k = v k := by
  unfold segmentSort
  rw [exec_flatMap]
  refine foldl_exec_outside offs (segNet m b) v k fun a ha c hc => ?_
  have w := segNet_wires hc
  have := hk a ha
  refine ⟨?_, ?_⟩ <;> intro h <;> have := congrArg Fin.val h <;> omega

/-- **On each segment the output is the bitonic sort of that segment's input.** -/
theorem segmentSort_exec_seg {m b : ℕ} {offs : List ℕ} (hd : SegDisjoint b offs) {o : ℕ}
    (ho : o ∈ offs) (hfit : o + 2 ^ b ≤ m) {α : Type*} [LinearOrder α] (v : Fin m → α)
    (i : Fin (2 ^ b)) :
    (segmentSort m b offs).exec v ⟨o + i.val, by have := i.2; omega⟩ =
      (bitonicSort b).exec (fun j : Fin (2 ^ b) => v ⟨o + j.val, by have := j.2; omega⟩) i := by
  obtain ⟨l₁, l₂, rfl⟩ := List.append_of_mem ho
  have hd' : List.Pairwise _ (l₁ ++ o :: l₂) := hd
  rw [List.pairwise_append] at hd'
  obtain ⟨-, hd₂, hd₁₂⟩ := hd'
  have hl₂ : ∀ a ∈ l₂, o + 2 ^ b ≤ a ∨ a + 2 ^ b ≤ o := fun a ha => (List.pairwise_cons.1 hd₂).1 a ha
  have hl₁ : ∀ a ∈ l₁, a + 2 ^ b ≤ o ∨ o + 2 ^ b ≤ a := fun a ha => hd₁₂ a ha o List.mem_cons_self
  unfold segmentSort
  rw [exec_flatMap, List.foldl_append, List.foldl_cons]
  set w := l₁.foldl (fun v' a => (segNet m b a).exec v') v with hw
  have hpos : ∀ j : Fin (2 ^ b), o ≤ (⟨o + j.val, by have := j.2; omega⟩ : Fin m).val ∧
      (⟨o + j.val, by have := j.2; omega⟩ : Fin m).val < o + 2 ^ b := fun j => by
    have := j.2; simp only; omega
  rw [foldl_exec_outside l₂ (segNet m b) _ _ fun a ha =>
    segNet_untouched (by rcases hl₂ a ha with h | h <;> [exact Or.inr h; exact Or.inl h]) (hpos i)]
  unfold segNet
  rw [dif_pos hfit, shiftEmbed_exec_inside]
  congr 1
  funext j
  rw [hw]
  exact foldl_exec_outside l₁ (segNet m b) v _ fun a ha => segNet_untouched (hl₁ a ha) (hpos j)

/-- **Each segment of the output is sorted.** -/
theorem segmentSort_seg_monotone {m b : ℕ} {offs : List ℕ} (hd : SegDisjoint b offs) {o : ℕ}
    (ho : o ∈ offs) (hfit : o + 2 ^ b ≤ m) {α : Type*} [LinearOrder α] (v : Fin m → α) :
    Monotone fun i : Fin (2 ^ b) =>
      (segmentSort m b offs).exec v ⟨o + i.val, by have := i.2; omega⟩ := by
  have := (bitonicSort_sorts b) α (fun j : Fin (2 ^ b) => v ⟨o + j.val, by have := j.2; omega⟩)
  intro x y hxy
  show (segmentSort m b offs).exec v ⟨o + x.val, _⟩ ≤ (segmentSort m b offs).exec v ⟨o + y.val, _⟩
  rw [segmentSort_exec_seg hd ho hfit, segmentSort_exec_seg hd ho hfit]
  exact this hxy

/-- One comparator permutes its input. -/
theorem Comparator.apply_eq_comp_perm' {n : ℕ} {α : Type*} [LinearOrder α] (c : Comparator n)
    (v : Fin n → α) : ∃ ρ : Equiv.Perm (Fin n), c.apply v = v ∘ ρ := by
  have hij := c.h.ne
  rcases le_total (v c.i) (v c.j) with h | h
  · refine ⟨1, funext fun k => ?_⟩
    unfold Comparator.apply
    split_ifs with h1 h2 <;> simp_all
  · refine ⟨Equiv.swap c.i c.j, funext fun k => ?_⟩
    unfold Comparator.apply
    split_ifs with h1 h2 <;> simp_all [Equiv.swap_apply_of_ne_of_ne]

/-- A network permutes its input. -/
theorem exec_eq_comp_perm_seg {n : ℕ} {α : Type*} [LinearOrder α] (net : ComparatorNetwork n)
    (v : Fin n → α) : ∃ ρ : Equiv.Perm (Fin n), net.exec v = v ∘ ρ := by
  obtain ⟨cs⟩ := net
  induction cs generalizing v with
  | nil => exact ⟨1, rfl⟩
  | cons c cs ih =>
    obtain ⟨ρ₁, h₁⟩ := Comparator.apply_eq_comp_perm' c v
    obtain ⟨ρ₂, h₂⟩ := ih (c.apply v)
    exact ⟨ρ₁ * ρ₂, by
      show ComparatorNetwork.exec ⟨cs⟩ (c.apply v) = _
      rw [h₂, h₁]; rfl⟩

/-- **Keys never leave their segment**: each output segment is a permutation of the input segment. -/
theorem segmentSort_seg_perm {m b : ℕ} {offs : List ℕ} (hd : SegDisjoint b offs) {o : ℕ}
    (ho : o ∈ offs) (hfit : o + 2 ^ b ≤ m) {α : Type*} [LinearOrder α] (v : Fin m → α) :
    ∃ ρ : Equiv.Perm (Fin (2 ^ b)),
      (fun i : Fin (2 ^ b) => (segmentSort m b offs).exec v ⟨o + i.val, by have := i.2; omega⟩) =
        (fun j : Fin (2 ^ b) => v ⟨o + j.val, by have := j.2; omega⟩) ∘ ρ := by
  obtain ⟨ρ, hρ⟩ := exec_eq_comp_perm_seg (bitonicSort b)
    (fun j : Fin (2 ^ b) => v ⟨o + j.val, by have := j.2; omega⟩)
  exact ⟨ρ, funext fun i => by rw [segmentSort_exec_seg hd ho hfit, hρ]⟩

end Bitonic

end
