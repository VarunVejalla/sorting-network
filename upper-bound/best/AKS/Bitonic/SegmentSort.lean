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

/-! ### Row identity for a sorted column -/

open Finset in
/-- A monotone Boolean column is `false` exactly on an initial segment `[0, k)`. -/
theorem monotone_bool_initial {m : ℕ} (w : Fin m → Bool) (hw : Monotone w) :
    ∃ k ≤ m, ∀ r : Fin m, w r = false ↔ r.val < k := by
  classical
  by_cases hT : ∃ r, w r = true
  · set T := univ.filter fun r : Fin m => w r = true
    have hne : T.Nonempty := by
      obtain ⟨r, hr⟩ := hT
      exact ⟨r, by simp [T, hr]⟩
    have hmin : w (T.min' hne) = true := by
      have := T.min'_mem hne
      simpa [T] using this
    refine ⟨(T.min' hne).val, (T.min' hne).2.le, fun r => ⟨fun hf => ?_, fun hlt => ?_⟩⟩
    · by_contra hc
      push_neg at hc
      have hle : T.min' hne ≤ r := Fin.le_iff_val_le_val.2 hc
      have := hw hle
      rw [hmin, hf] at this
      exact absurd this (by decide)
    · by_contra hc
      have hrt : w r = true := by simpa using hc
      have := T.min'_le r (by simp [T, hrt])
      exact absurd hlt (not_lt.2 (Fin.le_iff_val_le_val.1 this))
  · push_neg at hT
    exact ⟨m, le_rfl, fun r => ⟨fun _ => r.2, fun _ => by simpa using hT r⟩⟩

open Finset in
/-- **Row identity (one sorted column).** The `false`s at rows `≥ h` number `F − h`, `F` the column's
`false`s: this is the margin excess `(F − h)₊` of the round-1 count. -/
theorem cntT_rows_false_of_monotone {m : ℕ} (w : Fin m → Bool) (hw : Monotone w) (h : ℕ) :
    cntT (univ.filter fun r : Fin m => h ≤ r.val) w false = cntT univ w false - h := by
  classical
  obtain ⟨k, hkm, hk⟩ := monotone_bool_initial w hw
  have hall : cntT univ w false = k := by
    unfold cntT
    rw [show (univ.filter fun r : Fin m => w r = false) = univ.filter fun r : Fin m => r.val < k from
      Finset.filter_congr fun r _ => hk r]
    refine (Finset.card_bij (fun r _ => r.val) ?_ ?_ ?_).trans (Finset.card_range k)
    · intro r hr; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hr; simpa using hr
    · intro a _ c _ hac; exact Fin.ext hac
    · intro x hx
      simp only [Finset.mem_range] at hx
      exact ⟨⟨x, by omega⟩, by simp [hx], rfl⟩
  rw [hall]
  unfold cntT
  rw [Finset.filter_filter, show (univ.filter fun r : Fin m => h ≤ r.val ∧ w r = false) =
    univ.filter fun r : Fin m => h ≤ r.val ∧ r.val < k from Finset.filter_congr fun r _ => by rw [hk r]]
  refine (Finset.card_bij (fun r _ => r.val) ?_ ?_ ?_).trans (Nat.card_Ico h k)
  · intro r hr
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hr
    simp [Finset.mem_Ico, hr.1, hr.2]
  · intro a _ c _ hac; exact Fin.ext hac
  · intro x hx
    simp only [Finset.mem_Ico] at hx
    exact ⟨⟨x, by omega⟩, by simp [hx.1, hx.2], rfl⟩

/-! ### L3b, one column: escapes at a cut inside a sorted segment -/

open Finset in
/-- Counts on a disjoint union of row ranges add up. -/
theorem cntT_rows_split {m : ℕ} (w : Fin m → Bool) (bv : Bool) {a c : ℕ} (hac : a ≤ c) :
    cntT (univ.filter fun r : Fin m => a ≤ r.val) w bv =
      cntT (univ.filter fun r : Fin m => a ≤ r.val ∧ r.val < c) w bv +
        cntT (univ.filter fun r : Fin m => c ≤ r.val) w bv := by
  classical
  unfold cntT
  rw [← Finset.card_union_of_disjoint]
  · congr 1
    ext r
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
    constructor
    · rintro ⟨h1, h2⟩
      by_cases hc : r.val < c
      · exact Or.inl ⟨⟨h1, hc⟩, h2⟩
      · exact Or.inr ⟨by omega, h2⟩
    · rintro (⟨⟨h1, -⟩, h2⟩ | ⟨h1, h2⟩)
      · exact ⟨h1, h2⟩
      · exact ⟨by omega, h2⟩
  · rw [Finset.disjoint_left]
    intro r h1 h2
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
    omega

open Finset in
/-- In a sorted segment `[o, o + 2^b)` holding `B` `false`s, the `false`s at rows `≥ i`
(`o ≤ i ≤ o + 2^b`) number `B − (i − o)`. -/
theorem seg_sorted_false_above {m b o : ℕ} (hfit : o + 2 ^ b ≤ m) (w : Fin m → Bool)
    (hmono : Monotone fun j : Fin (2 ^ b) => w ⟨o + j.val, by have := j.2; omega⟩)
    {i : ℕ} (hoi : o ≤ i) (hi : i ≤ o + 2 ^ b) :
    cntT (univ.filter fun r : Fin m => i ≤ r.val ∧ r.val < o + 2 ^ b) w false =
      cntT (segSet m b o) w false - (i - o) := by
  classical
  obtain ⟨k, hk2, hk⟩ := monotone_bool_initial _ hmono
  have hseg : cntT (segSet m b o) w false = k := by
    rw [cntT_segSet hfit]
    rw [show (univ.filter fun j : Fin (2 ^ b) => w ⟨o + j.val, by have := j.2; omega⟩ = false) =
      univ.filter fun j : Fin (2 ^ b) => j.val < k from Finset.filter_congr fun j _ => hk j]
    refine (Finset.card_bij (fun j _ => j.val) ?_ ?_ ?_).trans (Finset.card_range k)
    · intro j hj; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj; simpa using hj
    · intro a _ c _ hac; exact Fin.ext hac
    · intro x hx; simp only [Finset.mem_range] at hx; exact ⟨⟨x, by omega⟩, by simp [hx], rfl⟩
  rw [hseg]
  unfold cntT
  have hiff : ∀ r : Fin m, (i ≤ r.val ∧ r.val < o + 2 ^ b) ∧ w r = false ↔
      (i ≤ r.val ∧ r.val < o + k) := by
    intro r
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      have := (hk ⟨r.val - o, by omega⟩).1 (by
        have e : (⟨o + (r.val - o), by omega⟩ : Fin m) = r := Fin.ext (by simp; omega)
        simpa [e] using h3)
      simp at this; omega
    · rintro ⟨h1, h2⟩
      refine ⟨⟨h1, by omega⟩, ?_⟩
      have := (hk ⟨r.val - o, by omega⟩).2 (by simp; omega)
      have e : (⟨o + (r.val - o), by omega⟩ : Fin m) = r := Fin.ext (by simp; omega)
      simpa [e] using this
  rw [Finset.filter_filter, show (univ.filter fun r : Fin m => (i ≤ r.val ∧ r.val < o + 2 ^ b) ∧ w r = false) =
    univ.filter fun r : Fin m => i ≤ r.val ∧ r.val < o + k from Finset.filter_congr fun r _ => hiff r]
  refine (Finset.card_bij (fun r _ => r.val) ?_ ?_ ?_).trans ((Nat.card_Ico i (o + k)).trans (by omega))
  · intro r hr; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hr; simp [Finset.mem_Ico, hr.1, hr.2]
  · intro a _ c _ hac; exact Fin.ext hac
  · intro x hx; simp only [Finset.mem_Ico] at hx; exact ⟨⟨x, by omega⟩, by simp [hx.1, hx.2], rfl⟩

open Finset in
/-- Wires of rows `< o` split into `true`s and `false`s. -/
theorem cntT_below_tf {m : ℕ} (w : Fin m → Bool) {o : ℕ} (ho : o ≤ m) :
    cntT (univ.filter fun r : Fin m => r.val < o) w true +
      cntT (univ.filter fun r : Fin m => r.val < o) w false = o := by
  classical
  unfold cntT
  rw [← Finset.card_union_of_disjoint (Finset.disjoint_filter.2 fun r _ h1 h2 => by simp_all)]
  rw [Finset.filter_union_right]
  have : ((univ.filter fun r : Fin m => r.val < o).filter fun r => w r = true ∨ w r = false) =
      univ.filter fun r : Fin m => r.val < o := Finset.filter_true_of_mem fun r _ => by cases w r <;> simp
  rw [this]
  refine (Finset.card_bij (fun r _ => r.val) ?_ ?_ ?_).trans (Finset.card_range o)
  · intro r hr; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hr; simpa using hr
  · intro a _ c _ hac; exact Fin.ext hac
  · intro x hx; simp only [Finset.mem_range] at hx; exact ⟨⟨x, by omega⟩, by simp [hx], rfl⟩

open Finset in
/-- **L3b, one column.** For a cut `i` inside segment `[o, o + 2^b)`, the `false`s at rows `≥ i` after the
segment sort are at most: the input `false`s at rows `≥ o + 2^b` (left alone), plus `(C − i)₊` (`C` the
column's `false`s, the round-2 excess at the cut), plus the input `true`s below the segment. -/
theorem segmentSort_escapes_le {m b : ℕ} {offs : List ℕ} (hd : SegDisjoint b offs)
    (hfit : ∀ o ∈ offs, o + 2 ^ b ≤ m) {o : ℕ} (ho : o ∈ offs) {i : ℕ} (hoi : o ≤ i)
    (hi : i ≤ o + 2 ^ b) (v : Fin m → Bool) :
    cntT (univ.filter fun r : Fin m => i ≤ r.val) ((segmentSort m b offs).exec v) false ≤
      cntT (univ.filter fun r : Fin m => o + 2 ^ b ≤ r.val) v false +
        (cntT univ v false - i) + cntT (univ.filter fun r : Fin m => r.val < o) v true := by
  classical
  set L := 2 ^ b
  set out := (segmentSort m b offs).exec v
  have hfo := hfit o ho
  -- rows >= o + L: only whole segments above, so the count does not grow
  have hU : cntT (univ.filter fun r : Fin m => o + L ≤ r.val) out false ≤
      cntT (univ.filter fun r : Fin m => o + L ≤ r.val) v false := by
    refine segmentSort_cnt_rows_le hd hfit le_rfl (fun o' ho' h' => ?_) v false
    by_cases hoo : o' = o
    · subst hoo; omega
    · have := List.Pairwise.forall (fun _ _ h => Or.symm h) hd ho' ho hoo
      omega
  -- the segment, sorted, with B falses
  have hB : cntT (segSet m b o) out false = cntT (segSet m b o) v false :=
    segmentSort_cntT_seg hd ho hfo v false
  have hS := seg_sorted_false_above hfo out (segmentSort_seg_monotone hd ho hfo v) hoi hi
  -- split the output rows >= i
  have hsplit := cntT_rows_split out false (show i ≤ o + L by omega)
  -- split the input column: rows < o, the segment, rows >= o + L
  have hall : cntT univ v false = cntT (univ.filter fun r : Fin m => r.val < o) v false +
      cntT (segSet m b o) v false + cntT (univ.filter fun r : Fin m => o + L ≤ r.val) v false := by
    have h0 := cntT_rows_split v false (show 0 ≤ o by omega)
    have h1 := cntT_rows_split v false (show o ≤ o + L by omega)
    have e0 : (univ.filter fun r : Fin m => 0 ≤ r.val) = univ := by ext r; simp
    have e1 : (univ.filter fun r : Fin m => 0 ≤ r.val ∧ r.val < o) =
        univ.filter fun r : Fin m => r.val < o := by ext r; simp
    rw [e0, e1] at h0
    have e2 : (univ.filter fun r : Fin m => o ≤ r.val ∧ r.val < o + L) = segSet m b o := rfl
    rw [e2] at h1
    omega
  have htf := cntT_below_tf v (show o ≤ m by omega)
  rw [hsplit, hS, hB]
  omega

open Finset in
/-- Sorted column: the `true`s below row `o` number `o − F` (`F` the column's `false`s). -/
theorem cntT_below_true_of_monotone {m : ℕ} (w : Fin m → Bool) (hw : Monotone w) {o : ℕ} (ho : o ≤ m) :
    cntT (univ.filter fun r : Fin m => r.val < o) w true = o - cntT univ w false := by
  have htf := cntT_below_tf w ho
  have hab := cntT_rows_false_of_monotone w hw o
  have hs := cntT_rows_split w false (show 0 ≤ o by omega)
  have e0 : (univ.filter fun r : Fin m => 0 ≤ r.val) = univ := by ext r; simp
  have e1 : (univ.filter fun r : Fin m => 0 ≤ r.val ∧ r.val < o) =
      univ.filter fun r : Fin m => r.val < o := by ext r; simp
  rw [e0, e1] at hs
  omega

end Bitonic

end
