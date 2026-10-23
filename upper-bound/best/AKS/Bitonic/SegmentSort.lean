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

/-! ### Counting form of "keys never leave their segment" (L3a, one column) -/

open Finset in
/-- Number of wires of `S` where `w` takes the value `bv` (default: `true`s). -/
def cntT {m : ℕ} (S : Finset (Fin m)) (w : Fin m → Bool) (bv : Bool := true) : ℕ :=
  (S.filter fun r => w r = bv).card

open Finset in
/-- The wires of segment `[o, o + 2^b)`. -/
def segSet (m b o : ℕ) : Finset (Fin m) := univ.filter fun r : Fin m => o ≤ r.val ∧ r.val < o + 2 ^ b

open Finset in
theorem cntT_comp_perm {N : ℕ} (w : Fin N → Bool) (ρ : Equiv.Perm (Fin N)) (bv : Bool) :
    (univ.filter fun i => (w ∘ ρ) i = bv).card = (univ.filter fun i => w i = bv).card := by
  refine Finset.card_bij (fun i _ => ρ i) (fun i hi => by simpa using hi)
    (fun a _ b _ h => ρ.injective h) (fun j hj => ⟨ρ.symm j, by simpa using hj, by simp⟩)

open Finset in
/-- Counting on a fitting segment through the local view. -/
theorem cntT_segSet {m b o : ℕ} (hfit : o + 2 ^ b ≤ m) (w : Fin m → Bool) (bv : Bool) :
    cntT (segSet m b o) w bv =
      (univ.filter fun i : Fin (2 ^ b) => w ⟨o + i.val, by have := i.2; omega⟩ = bv).card := by
  unfold cntT segSet
  refine (Finset.card_bij (fun i _ => (⟨o + i.val, by have := i.2; omega⟩ : Fin m)) ?_ ?_ ?_).symm
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    exact ⟨⟨by omega, by have := i.2; omega⟩, hi⟩
  · intro a _ c _ h
    exact Fin.ext (by have := congrArg Fin.val h; simp at this; omega)
  · intro r hr
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hr
    refine ⟨⟨r.val - o, by omega⟩, ?_, Fin.ext (by simp; omega)⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    have e : (⟨o + (r.val - o), by omega⟩ : Fin m) = r := Fin.ext (by simp; omega)
    rw [e]; exact hr.2

/-- **The number of `true`s on each segment is preserved.** -/
theorem segmentSort_cntT_seg {m b : ℕ} {offs : List ℕ} (hd : SegDisjoint b offs) {o : ℕ}
    (ho : o ∈ offs) (hfit : o + 2 ^ b ≤ m) (v : Fin m → Bool) (bv : Bool) :
    cntT (segSet m b o) ((segmentSort m b offs).exec v) bv = cntT (segSet m b o) v bv := by
  obtain ⟨ρ, hρ⟩ := segmentSort_seg_perm hd ho hfit v
  rw [cntT_segSet hfit _ bv, cntT_segSet hfit _ bv]
  have : (fun i : Fin (2 ^ b) => (segmentSort m b offs).exec v ⟨o + i.val, by have := i.2; omega⟩) =
      (fun j : Fin (2 ^ b) => v ⟨o + j.val, by have := j.2; omega⟩) ∘ ρ := hρ
  simp only [show ∀ i : Fin (2 ^ b), (segmentSort m b offs).exec v ⟨o + i.val, by have := i.2; omega⟩ =
      ((fun j : Fin (2 ^ b) => v ⟨o + j.val, by have := j.2; omega⟩) ∘ ρ) i from fun i => congr_fun this i]
  exact cntT_comp_perm (fun j : Fin (2 ^ b) => v ⟨o + j.val, by have := j.2; omega⟩) ρ bv

open Finset in
/-- **L3a, one column**: if every segment reaching rows `≥ i` starts at row `≥ h` (and `h ≤ i`), then
the `true`s at rows `≥ i` after the segment sort number at most the `true`s at rows `≥ h` before. -/
theorem segmentSort_cnt_rows_le {m b : ℕ} {offs : List ℕ} (hd : SegDisjoint b offs)
    (hfit : ∀ o ∈ offs, o + 2 ^ b ≤ m) {h i : ℕ} (hhi : h ≤ i)
    (hseg : ∀ o ∈ offs, i < o + 2 ^ b → h ≤ o) (v : Fin m → Bool) (bv : Bool := true) :
    cntT (univ.filter fun r : Fin m => i ≤ r.val) ((segmentSort m b offs).exec v) bv ≤
      cntT (univ.filter fun r : Fin m => h ≤ r.val) v bv := by
  classical
  set out := (segmentSort m b offs).exec v
  set Mf : Finset ℕ := (offs.filter fun o => decide (i < o + 2 ^ b)).toFinset with hMf
  have hMf_mem : ∀ o, o ∈ Mf ↔ o ∈ offs ∧ i < o + 2 ^ b := fun o => by
    simp [hMf, List.mem_filter]
  set U : Finset (Fin m) := Mf.biUnion (segSet m b) with hU
  set Ri : Finset (Fin m) := univ.filter fun r : Fin m => i ≤ r.val
  set Rout := Ri \ U
  -- pairwise disjoint segments
  have hsymm : Symmetric fun o₁ o₂ : ℕ => o₁ + 2 ^ b ≤ o₂ ∨ o₂ + 2 ^ b ≤ o₁ :=
    fun _ _ h => h.symm
  have hpd : (Mf : Set ℕ).PairwiseDisjoint (segSet m b) := by
    intro o₁ h₁ o₂ h₂ hne
    have h₁' := ((hMf_mem o₁).1 h₁).1
    have h₂' := ((hMf_mem o₂).1 h₂).1
    have hr := List.Pairwise.forall hsymm hd h₁' h₂' hne
    rw [Function.onFun, Finset.disjoint_left]
    intro r hr₁ hr₂
    simp only [segSet, Finset.mem_filter, Finset.mem_univ, true_and] at hr₁ hr₂
    omega
  -- outside wires are fixed
  have hout : ∀ r ∈ Rout, out r = v r := by
    intro r hr
    simp only [Rout, Ri, Finset.mem_sdiff, Finset.mem_filter, Finset.mem_univ, true_and, hU,
      Finset.mem_biUnion, not_exists, not_and] at hr
    refine segmentSort_exec_outside offs v r fun o ho => ?_
    by_cases hm : i < o + 2 ^ b
    · have := hr.2 o ((hMf_mem o).2 ⟨ho, hm⟩)
      simp only [segSet, Finset.mem_filter, Finset.mem_univ, true_and, not_and, not_lt] at this
      by_cases h1 : o ≤ r.val
      · exact Or.inr (this h1)
      · exact Or.inl (by omega)
    · exact Or.inr (by omega)
  have hdisj : Disjoint Rout U := Finset.sdiff_disjoint
  have hcntU : ∀ w : Fin m → Bool, cntT U w bv = ∑ o ∈ Mf, cntT (segSet m b o) w bv := by
    intro w
    unfold cntT
    rw [hU, Finset.filter_biUnion, Finset.card_biUnion]
    intro o₁ h₁ o₂ h₂ hne
    exact Finset.disjoint_filter_filter (hpd h₁ h₂ hne)
  have hcntT : ∀ w : Fin m → Bool, cntT (Rout ∪ U) w bv = cntT Rout w bv + cntT U w bv := by
    intro w
    unfold cntT
    rw [Finset.filter_union, Finset.card_union_of_disjoint (Finset.disjoint_filter_filter hdisj)]
  -- step 1: rows >= i inside T
  have h1 : cntT Ri out bv ≤ cntT (Rout ∪ U) out bv := by
    unfold cntT
    refine Finset.card_le_card (Finset.filter_subset_filter _ ?_)
    intro r hr
    by_cases hu : r ∈ U
    · exact Finset.mem_union_right _ hu
    · exact Finset.mem_union_left _ (Finset.mem_sdiff.2 ⟨hr, hu⟩)
  -- step 2: T's count is preserved
  have h2 : cntT (Rout ∪ U) out bv = cntT (Rout ∪ U) v bv := by
    rw [hcntT, hcntT, hcntU, hcntU]
    congr 1
    · unfold cntT
      congr 1
      exact Finset.filter_congr fun r hr => by rw [hout r hr]
    · exact Finset.sum_congr rfl fun o ho =>
        segmentSort_cntT_seg hd ((hMf_mem o).1 ho).1 (hfit o ((hMf_mem o).1 ho).1) v bv
  -- step 3: T lies in rows >= h
  have h3 : cntT (Rout ∪ U) v bv ≤ cntT (univ.filter fun r : Fin m => h ≤ r.val) v bv := by
    unfold cntT
    refine Finset.card_le_card (Finset.filter_subset_filter _ ?_)
    intro r hr
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rcases Finset.mem_union.1 hr with hr | hr
    · have := (Finset.mem_sdiff.1 hr).1
      simp only [Ri, Finset.mem_filter, Finset.mem_univ, true_and] at this
      omega
    · obtain ⟨o, ho, hro⟩ := Finset.mem_biUnion.1 hr
      have := hseg o ((hMf_mem o).1 ho).1 ((hMf_mem o).1 ho).2
      simp only [segSet, Finset.mem_filter, Finset.mem_univ, true_and] at hro
      omega
  exact h1.trans (h2 ▸ h3)

end Bitonic

end
