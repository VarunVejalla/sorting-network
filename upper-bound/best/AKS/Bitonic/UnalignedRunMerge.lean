module
/-
  # Merging sorted runs with unaligned boundaries (UB-43)

  `RunMerge` needs every *aligned* block of `2^l` positions to be sorted. Here the input is a
  concatenation of sorted runs whose boundaries are arbitrary, as long as two descents
  (`v p > v (p+1)`) are at least `R` apart (`DescentsApart R`). With `2^s ≤ R + 1`, every aligned
  block of `2^s` positions then holds at most one descent, so it is two sorted runs (`TwoRun`).

  * `ssSort s` (on `2^s` wires) sorts every two-run input, at depth `≤ 2s - 1` (`s ≥ 1`):
    sort the even and the odd positions recursively (both are again two runs), interleave, then
    two transposition layers `(2i, 2i+1)` and `(2i+1, 2i+2)`. The counts of `false`s at even and
    odd positions of a two-run Boolean input differ by `-1 … 2`, which the two layers repair.
  * `ssBlocks s k`: `ssSort s` on every aligned `2^s` block (makes the input `RunSorted s`).
  * `uRunMerge s k = ssBlocks s k ; runMerge s k` sorts every input whose aligned `2^s` blocks are
    two runs, at depth `≤ (2s - 1) + bitonicDepthBudget (s+k) - bitonicDepthBudget s`.
  * `uRunMergeNetwork s m` on any `m` wires (padding with `true`), and
    `uRunMergeNetwork_sorts_of_descentsApart`: it sorts every input with descents `R` apart,
    `2^s ≤ R + 1`, any linear order.
-/

public import AKS.Bitonic.BlockSort
public import AKS.Bitonic.SegmentSort

@[expose] public section

open ComparatorNetwork Finset

namespace Bitonic

/-! ### Two sorted runs -/

/-- `v` consists of two sorted runs `[0, p)` and `[p, m)` (at most one descent). -/
def TwoRun {m : ℕ} {α : Type*} [Preorder α] (v : Fin m → α) : Prop :=
  ∃ p : ℕ, (∀ i j : Fin m, i ≤ j → j.val < p → v i ≤ v j) ∧
    (∀ i j : Fin m, p ≤ i.val → i ≤ j → v i ≤ v j)

theorem TwoRun.comp_monotone {m : ℕ} {α β : Type*} [Preorder α] [Preorder β] {f : α → β}
    (hf : Monotone f) {v : Fin m → α} (hv : TwoRun v) : TwoRun (f ∘ v) := by
  obtain ⟨p, h1, h2⟩ := hv
  exact ⟨p, fun i j a b => hf (h1 i j a b), fun i j a b => hf (h2 i j a b)⟩

theorem pow_succ_eq_two_mul (s : ℕ) : 2 ^ (s + 1) = 2 * 2 ^ s := by rw [pow_succ]; ring

/-- The even positions of `2^(s+1)` wires. -/
def evE (s : ℕ) : Fin (2 ^ s) ↪o Fin (2 ^ (s + 1)) :=
  OrderEmbedding.ofStrictMono
    (fun i => ⟨2 * i.val, by have := i.2; have := pow_succ_eq_two_mul s; omega⟩)
    fun a b h => by
      change 2 * a.val < 2 * b.val
      have : a.val < b.val := h
      omega

/-- The odd positions of `2^(s+1)` wires. -/
def odE (s : ℕ) : Fin (2 ^ s) ↪o Fin (2 ^ (s + 1)) :=
  OrderEmbedding.ofStrictMono
    (fun i => ⟨2 * i.val + 1, by have := i.2; have := pow_succ_eq_two_mul s; omega⟩)
    fun a b h => by
      change 2 * a.val + 1 < 2 * b.val + 1
      have : a.val < b.val := h
      omega

@[simp] theorem evE_val (s : ℕ) (i : Fin (2 ^ s)) : (evE s i).val = 2 * i.val := rfl

@[simp] theorem odE_val (s : ℕ) (i : Fin (2 ^ s)) : (odE s i).val = 2 * i.val + 1 := rfl

theorem evE_ne_odE (s : ℕ) (i j : Fin (2 ^ s)) : evE s i ≠ odE s j := by
  intro h
  have := congrArg Fin.val h
  simp only [evE_val, odE_val] at this
  omega

/-- A network on the even positions and a copy on the odd positions. -/
def evenOdd (s : ℕ) (N : ComparatorNetwork (2 ^ s)) : ComparatorNetwork (2 ^ (s + 1)) :=
  ⟨(N.scatterEmbed _ (evE s)).comparators ++ (N.scatterEmbed _ (odE s)).comparators⟩

theorem evenOdd_exec_ev {α : Type*} [LinearOrder α] (s : ℕ) (N : ComparatorNetwork (2 ^ s))
    (v : Fin (2 ^ (s + 1)) → α) (i : Fin (2 ^ s)) :
    (evenOdd s N).exec v (evE s i) = N.exec (v ∘ evE s) i := by
  unfold evenOdd
  rw [exec_append, scatterEmbed_exec_outside _ _ _ _ _
    (by rintro ⟨j, hj⟩; exact evE_ne_odE s i j hj.symm), scatterEmbed_exec_inside]

theorem evenOdd_exec_od {α : Type*} [LinearOrder α] (s : ℕ) (N : ComparatorNetwork (2 ^ s))
    (v : Fin (2 ^ (s + 1)) → α) (i : Fin (2 ^ s)) :
    (evenOdd s N).exec v (odE s i) = N.exec (v ∘ odE s) i := by
  unfold evenOdd
  rw [exec_append, scatterEmbed_exec_inside]
  congr 1
  funext j
  exact scatterEmbed_exec_outside _ _ _ _ _ (by rintro ⟨k, hk⟩; exact evE_ne_odE s k j hk)

theorem evenOdd_depth_le (s : ℕ) (N : ComparatorNetwork (2 ^ s)) :
    (evenOdd s N).depth ≤ N.depth := by
  have := depth_flatMap_disjoint [false, true]
    (fun b => (cond b (N.scatterEmbed _ (odE s)) (N.scatterEmbed _ (evE s))).comparators) N.depth
    (fun x _ => by
      cases x
      · exact depth_scatterEmbed_le N _ (evE s)
      · exact depth_scatterEmbed_le N _ (odE s))
    (by
      refine List.Pairwise.cons ?_ (List.pairwise_singleton _ _)
      intro b hb
      obtain rfl : b = true := by simpa using hb
      intro c₁ h₁ c₂ h₂
      simp only [cond, ComparatorNetwork.scatterEmbed, List.mem_map] at h₁ h₂
      obtain ⟨a₁, -, rfl⟩ := h₁
      obtain ⟨a₂, -, rfl⟩ := h₂
      exact ⟨⟨evE_ne_odE s _ _, evE_ne_odE s _ _⟩, ⟨evE_ne_odE s _ _, evE_ne_odE s _ _⟩⟩)
  simpa [evenOdd] using this

/-! ### The two transposition layers -/

/-- Layer `(2i, 2i+1)`. -/
def fixA (s : ℕ) : ComparatorNetwork (2 ^ (s + 1)) :=
  ⟨(List.finRange (2 ^ s)).map fun i : Fin (2 ^ s) =>
    ⟨⟨2 * i.val, by have := i.2; have := pow_succ_eq_two_mul s; omega⟩,
      ⟨2 * i.val + 1, by have := i.2; have := pow_succ_eq_two_mul s; omega⟩,
      Fin.mk_lt_mk.2 (by omega)⟩⟩

/-- Layer `(2i+1, 2i+2)`. -/
def fixB (s : ℕ) : ComparatorNetwork (2 ^ (s + 1)) :=
  ⟨(List.finRange (2 ^ s - 1)).map fun i : Fin (2 ^ s - 1) =>
    ⟨⟨2 * i.val + 1, by have := i.2; have := pow_succ_eq_two_mul s; omega⟩,
      ⟨2 * i.val + 2, by have := i.2; have := pow_succ_eq_two_mul s; omega⟩,
      Fin.mk_lt_mk.2 (by omega)⟩⟩

theorem fixA_parallel (s : ℕ) : IsParallelLayer (fixA s).comparators := by
  unfold IsParallelLayer fixA
  rw [List.pairwise_map]
  refine (List.nodup_finRange _).imp fun {a b} hab => ?_
  have h2 : a.val ≠ b.val := fun h => hab (Fin.ext h)
  simp only [Comparator.overlaps, Fin.ext_iff]
  omega

theorem fixB_parallel (s : ℕ) : IsParallelLayer (fixB s).comparators := by
  unfold IsParallelLayer fixB
  rw [List.pairwise_map]
  refine (List.nodup_finRange _).imp fun {a b} hab => ?_
  have h2 : a.val ≠ b.val := fun h => hab (Fin.ext h)
  simp only [Comparator.overlaps, Fin.ext_iff]
  omega

theorem fixA_depth_le (s : ℕ) : (fixA s).depth ≤ 1 :=
  depth_le_of_decomposition _ [(fixA s).comparators]
    ⟨fun l hl => by simp at hl; subst hl; exact fixA_parallel s, by simp⟩

theorem fixB_depth_le (s : ℕ) : (fixB s).depth ≤ 1 :=
  depth_le_of_decomposition _ [(fixB s).comparators]
    ⟨fun l hl => by simp at hl; subst hl; exact fixB_parallel s, by simp⟩

theorem fixB_zero_depth : (fixB 0).depth = 0 := by
  have : (fixB 0) = ⟨[]⟩ := by
    unfold fixB
    congr 1
  rw [this, depth_nil]

theorem fixA_exec_ev {α : Type*} [LinearOrder α] (s : ℕ) (w : Fin (2 ^ (s + 1)) → α)
    (k : Fin (2 ^ (s + 1))) (i : ℕ) (hi : i < 2 ^ s) (hk : k.val = 2 * i) :
    (fixA s).exec w k = min (w ⟨2 * i, by have := pow_succ_eq_two_mul s; omega⟩)
      (w ⟨2 * i + 1, by have := pow_succ_eq_two_mul s; omega⟩) := by
  obtain ⟨kv, hkv⟩ := k
  simp only at hk
  subst hk
  exact (foldl_parallel _ (fixA_parallel s) w _
    (List.mem_map.2 ⟨⟨i, hi⟩, List.mem_finRange _, rfl⟩)).1

theorem fixA_exec_od {α : Type*} [LinearOrder α] (s : ℕ) (w : Fin (2 ^ (s + 1)) → α)
    (k : Fin (2 ^ (s + 1))) (i : ℕ) (hi : i < 2 ^ s) (hk : k.val = 2 * i + 1) :
    (fixA s).exec w k = max (w ⟨2 * i, by have := pow_succ_eq_two_mul s; omega⟩)
      (w ⟨2 * i + 1, by have := pow_succ_eq_two_mul s; omega⟩) := by
  obtain ⟨kv, hkv⟩ := k
  simp only at hk
  subst hk
  exact (foldl_parallel _ (fixA_parallel s) w _
    (List.mem_map.2 ⟨⟨i, hi⟩, List.mem_finRange _, rfl⟩)).2

theorem fixB_exec_lo {α : Type*} [LinearOrder α] (s : ℕ) (w : Fin (2 ^ (s + 1)) → α)
    (k : Fin (2 ^ (s + 1))) (i : ℕ) (hi : i < 2 ^ s - 1) (hk : k.val = 2 * i + 1) :
    (fixB s).exec w k = min (w ⟨2 * i + 1, by have := pow_succ_eq_two_mul s; omega⟩)
      (w ⟨2 * i + 2, by have := pow_succ_eq_two_mul s; omega⟩) := by
  obtain ⟨kv, hkv⟩ := k
  simp only at hk
  subst hk
  exact (foldl_parallel _ (fixB_parallel s) w _
    (List.mem_map.2 ⟨⟨i, hi⟩, List.mem_finRange _, rfl⟩)).1

theorem fixB_exec_hi {α : Type*} [LinearOrder α] (s : ℕ) (w : Fin (2 ^ (s + 1)) → α)
    (k : Fin (2 ^ (s + 1))) (i : ℕ) (hi : i < 2 ^ s - 1) (hk : k.val = 2 * i + 2) :
    (fixB s).exec w k = max (w ⟨2 * i + 1, by have := pow_succ_eq_two_mul s; omega⟩)
      (w ⟨2 * i + 2, by have := pow_succ_eq_two_mul s; omega⟩) := by
  obtain ⟨kv, hkv⟩ := k
  simp only at hk
  subst hk
  exact (foldl_parallel _ (fixB_parallel s) w _
    (List.mem_map.2 ⟨⟨i, hi⟩, List.mem_finRange _, rfl⟩)).2

/-- The first and the last wire are untouched by `fixB`. -/
theorem fixB_exec_end {α : Type*} [LinearOrder α] (s : ℕ) (w : Fin (2 ^ (s + 1)) → α)
    (k : Fin (2 ^ (s + 1))) (hk : k.val = 0 ∨ k.val + 1 = 2 ^ (s + 1)) :
    (fixB s).exec w k = w k := by
  unfold ComparatorNetwork.exec
  refine foldl_comparators_outside _ w k fun c hc => ?_
  obtain ⟨i, -, rfl⟩ := List.mem_map.1 hc
  have := i.2
  have := pow_succ_eq_two_mul s
  refine ⟨fun h => ?_, fun h => ?_⟩ <;>
  · have h' := congrArg Fin.val h
    simp only at h'
    omega

/-! ### The two-run sorter -/

/-- Sorts every two-run input on `2^s` wires (`ssSort_sorts`). -/
def ssSort : (s : ℕ) → ComparatorNetwork (2 ^ s)
  | 0 => ⟨[]⟩
  | s + 1 => ((evenOdd s (ssSort s)).append (fixA s)).append (fixB s)

theorem ssSort_exec_succ {α : Type*} [LinearOrder α] (s : ℕ) (v : Fin (2 ^ (s + 1)) → α) :
    (ssSort (s + 1)).exec v = (fixB s).exec ((fixA s).exec ((evenOdd s (ssSort s)).exec v)) := by
  have h1 := exec_append ((evenOdd s (ssSort s)).append (fixA s)) (fixB s) v
  have h2 := exec_append (evenOdd s (ssSort s)) (fixA s) v
  exact h1.trans (congrArg _ h2)

/-- **Depth `2s - 1`** (for `s ≥ 1`). -/
theorem ssSort_depth_le : ∀ s, (ssSort (s + 1)).depth ≤ 2 * s + 1
  | 0 => by
    have h1 := depth_append_le ((evenOdd 0 (ssSort 0)).append (fixA 0)) (fixB 0)
    have h2 := depth_append_le (evenOdd 0 (ssSort 0)) (fixA 0)
    have h3 := evenOdd_depth_le 0 (ssSort 0)
    have h4 : (ssSort 0).depth = 0 := depth_nil
    have h5 := fixA_depth_le 0
    have h6 := fixB_zero_depth
    show (((evenOdd 0 (ssSort 0)).append (fixA 0)).append (fixB 0)).depth ≤ 1
    omega
  | s + 1 => by
    have h1 := depth_append_le ((evenOdd (s + 1) (ssSort (s + 1))).append (fixA (s + 1)))
      (fixB (s + 1))
    have h2 := depth_append_le (evenOdd (s + 1) (ssSort (s + 1))) (fixA (s + 1))
    have h3 := evenOdd_depth_le (s + 1) (ssSort (s + 1))
    have h5 := fixA_depth_le (s + 1)
    have h6 := fixB_depth_le (s + 1)
    have ih := ssSort_depth_le s
    show (((evenOdd (s + 1) (ssSort (s + 1))).append (fixA (s + 1))).append (fixB (s + 1))).depth
      ≤ 2 * (s + 1) + 1
    omega

theorem ssSort_depth_le' (s : ℕ) : (ssSort s).depth ≤ 2 * s := by
  rcases s with _ | s
  · exact (show (ssSort 0).depth = 0 from depth_nil).le
  · have := ssSort_depth_le s; omega

/-! ### Counting `false`s -/

theorem card_filter_val_lt {N k : ℕ} (hk : k ≤ N) :
    (univ.filter fun r : Fin N => r.val < k).card = k := by
  rw [← Finset.card_range k]
  refine Finset.card_bij (fun r _ => r.val) (fun r hr => by simpa using hr)
    (fun a _ b _ h => Fin.ext h) (fun b hb => ⟨⟨b, by simp at hb; omega⟩, by simpa using hb, rfl⟩)

theorem mono_bool_false_iff {N : ℕ} (E : Fin N → Bool) (hE : Monotone E) :
    ∀ r : Fin N, E r = false ↔ r.val < (univ.filter fun i => E i = false).card := by
  obtain ⟨k, hk, h⟩ := monotone_bool_initial E hE
  have : (univ.filter fun i => E i = false) = univ.filter fun i : Fin N => i.val < k := by
    ext i; simp [h]
  rw [this, card_filter_val_lt hk]
  exact h

theorem exec_card_false {N : ℕ} (net : ComparatorNetwork N) (u : Fin N → Bool) :
    (univ.filter fun i => net.exec u i = false).card = (univ.filter fun i => u i = false).card := by
  obtain ⟨ρ, hρ⟩ := exec_eq_comp_perm_seg net u
  rw [hρ]
  exact cntT_comp_perm u ρ false

theorem bool_eq_false_of_le {a b : Bool} (h : a ≤ b) (hb : b = false) : a = false := by
  subst hb
  cases a
  · rfl
  · exact absurd h (by decide)

/-- **Parity counts of a two-run Boolean vector**: the `false`s at odd positions are at most one
more, and at most two fewer, than those at even positions. -/
theorem twoRun_counts {s : ℕ} (u : Fin (2 ^ (s + 1)) → Bool) (hu : TwoRun u) :
    (univ.filter fun i : Fin (2 ^ s) => (u ∘ odE s) i = false).card ≤
        (univ.filter fun i : Fin (2 ^ s) => (u ∘ evE s) i = false).card + 1 ∧
    (univ.filter fun i : Fin (2 ^ s) => (u ∘ evE s) i = false).card ≤
        (univ.filter fun i : Fin (2 ^ s) => (u ∘ odE s) i = false).card + 2 := by
  obtain ⟨p, h1, h2⟩ := hu
  have hle : ∀ a b : Fin (2 ^ (s + 1)), a ≤ b → (b.val < p ∨ p ≤ a.val) → u b = false →
      u a = false := by
    intro a b hab hc hb
    refine bool_eq_false_of_le ?_ hb
    rcases hc with hc | hc
    · exact h1 a b hab hc
    · exact h2 a b hc hab
  have hone1 : (univ.filter fun i : Fin (2 ^ s) => 2 * i.val + 1 = p).card ≤ 1 := by
    refine Finset.card_le_one.2 fun a ha b hb => ?_
    simp only [mem_filter, mem_univ, true_and] at ha hb
    exact Fin.ext (by omega)
  have hone0 : (univ.filter fun i : Fin (2 ^ s) => 2 * i.val = p).card ≤ 1 := by
    refine Finset.card_le_one.2 fun a ha b hb => ?_
    simp only [mem_filter, mem_univ, true_and] at ha hb
    exact Fin.ext (by omega)
  constructor
  · have hsub : (univ.filter fun i : Fin (2 ^ s) => (u ∘ odE s) i = false) ⊆
        (univ.filter fun i : Fin (2 ^ s) => (u ∘ evE s) i = false) ∪
          (univ.filter fun i : Fin (2 ^ s) => 2 * i.val + 1 = p) := by
      intro i hi
      simp only [mem_filter, mem_univ, true_and, mem_union] at hi ⊢
      by_cases hp : 2 * i.val + 1 = p
      · exact Or.inr hp
      · refine Or.inl (hle (evE s i) (odE s i) (Fin.le_iff_val_le_val.2 (by simp)) ?_ hi)
        simp only [evE_val, odE_val]
        omega
    have := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
    omega
  · set A := univ.filter fun i : Fin (2 ^ s) => (u ∘ evE s) i = false
    have hsub : A ⊆ A.filter (fun i : Fin (2 ^ s) => 1 ≤ i.val ∧ 2 * i.val ≠ p) ∪
        ((univ.filter fun i : Fin (2 ^ s) => i.val = 0) ∪
          (univ.filter fun i : Fin (2 ^ s) => 2 * i.val = p)) := by
      intro i hi
      simp only [mem_filter, mem_univ, true_and, mem_union]
      by_cases h0 : i.val = 0
      · exact Or.inr (Or.inl h0)
      · by_cases hp : 2 * i.val = p
        · exact Or.inr (Or.inr hp)
        · exact Or.inl ⟨hi, by omega, hp⟩
    have hinj : (A.filter (fun i : Fin (2 ^ s) => 1 ≤ i.val ∧ 2 * i.val ≠ p)).card ≤
        (univ.filter fun i : Fin (2 ^ s) => (u ∘ odE s) i = false).card := by
      refine Finset.card_le_card_of_injOn (fun i => (⟨i.val - 1, by have := i.2; omega⟩ : Fin (2 ^ s)))
        ?_ ?_
      · intro i hi
        simp only [A, coe_filter, mem_filter, mem_univ, true_and, Set.mem_setOf_eq] at hi ⊢
        obtain ⟨hi, h1i, hpi⟩ := hi
        refine hle _ (evE s i) (Fin.le_iff_val_le_val.2 (by simp only [evE_val, odE_val]; omega)) ?_ hi
        simp only [evE_val, odE_val]
        omega
      · intro a ha b hb hab
        simp only [A, coe_filter, mem_filter, mem_univ, true_and, Set.mem_setOf_eq] at ha hb
        have := congrArg Fin.val hab
        simp only at this
        exact Fin.ext (by omega)
    have h3 := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
    have h4 := Finset.card_union_le (univ.filter fun i : Fin (2 ^ s) => i.val = 0)
      (univ.filter fun i : Fin (2 ^ s) => 2 * i.val = p)
    have h5': (univ.filter fun i : Fin (2 ^ s) => i.val = 0).card ≤ 1 := by
      refine Finset.card_le_one.2 fun a ha b hb => ?_
      simp only [mem_filter, mem_univ, true_and] at ha hb
      exact Fin.ext (ha.trans hb.symm)
    omega

theorem bool_true_iff_of_false_iff {b : Bool} {P : Prop} (h : b = false ↔ P) : b = true ↔ ¬ P := by
  cases b <;> simp_all

/-- **The two-run sorter sorts every two-run Boolean input.** -/
theorem ssSort_sorts_bool : ∀ (s : ℕ) (v : Fin (2 ^ s) → Bool), TwoRun v →
    Monotone ((ssSort s).exec v)
  | 0, v, _ => by
    intro i j _
    have hi := i.2; have hj := j.2
    have : i = j := Fin.ext (by simp at hi hj; omega)
    rw [this]
  | s + 1, v, hv => by
    obtain ⟨p, h1, h2⟩ := id hv
    have hev : TwoRun (v ∘ evE s) := ⟨(p + 1) / 2,
      fun i j hij hj => h1 _ _ ((evE s).monotone hij) (by simp only [evE_val]; omega),
      fun i j hi hij => h2 _ _ (by simp only [evE_val]; omega) ((evE s).monotone hij)⟩
    have hod : TwoRun (v ∘ odE s) := ⟨p / 2,
      fun i j hij hj => h1 _ _ ((odE s).monotone hij) (by simp only [odE_val]; omega),
      fun i j hi hij => h2 _ _ (by simp only [odE_val]; omega) ((odE s).monotone hij)⟩
    have hEf := mono_bool_false_iff _ (ssSort_sorts_bool s _ hev)
    have hOf := mono_bool_false_iff _ (ssSort_sorts_bool s _ hod)
    rw [exec_card_false] at hEf hOf
    obtain ⟨hc1, hc2⟩ := twoRun_counts v hv
    obtain ⟨kE, hkE⟩ : ∃ k, (univ.filter fun i : Fin (2 ^ s) => (v ∘ evE s) i = false).card = k :=
      ⟨_, rfl⟩
    obtain ⟨kO, hkO⟩ : ∃ k, (univ.filter fun i : Fin (2 ^ s) => (v ∘ odE s) i = false).card = k :=
      ⟨_, rfl⟩
    have bE : kE ≤ 2 ^ s := hkE ▸ (Finset.card_filter_le _ _).trans (by simp)
    have bO : kO ≤ 2 ^ s := hkO ▸ (Finset.card_filter_le _ _).trans (by simp)
    rw [hkE] at hEf hc1 hc2
    rw [hkO] at hOf hc1 hc2
    have hL := pow_succ_eq_two_mul s
    have hw_ev : ∀ (k : Fin (2 ^ (s + 1))) (i : ℕ) (hi : i < 2 ^ s), k.val = 2 * i →
        ((evenOdd s (ssSort s)).exec v k = true ↔ kE ≤ i) := by
      intro k i hi hk
      rw [show k = evE s ⟨i, hi⟩ from Fin.ext (by simp [hk]), evenOdd_exec_ev,
        bool_true_iff_of_false_iff (hEf ⟨i, hi⟩)]
      exact not_lt
    have hw_od : ∀ (k : Fin (2 ^ (s + 1))) (i : ℕ) (hi : i < 2 ^ s), k.val = 2 * i + 1 →
        ((evenOdd s (ssSort s)).exec v k = true ↔ kO ≤ i) := by
      intro k i hi hk
      rw [show k = odE s ⟨i, hi⟩ from Fin.ext (by simp [hk]), evenOdd_exec_od,
        bool_true_iff_of_false_iff (hOf ⟨i, hi⟩)]
      exact not_lt
    have hx_ev : ∀ (k : Fin (2 ^ (s + 1))) (i : ℕ) (hi : i < 2 ^ s), k.val = 2 * i →
        ((fixA s).exec ((evenOdd s (ssSort s)).exec v) k = true ↔ kE ≤ i ∧ kO ≤ i) := by
      intro k i hi hk
      rw [fixA_exec_ev s _ k i hi hk, min_eq_true, hw_ev _ i hi rfl, hw_od _ i hi rfl]
    have hx_od : ∀ (k : Fin (2 ^ (s + 1))) (i : ℕ) (hi : i < 2 ^ s), k.val = 2 * i + 1 →
        ((fixA s).exec ((evenOdd s (ssSort s)).exec v) k = true ↔ kE ≤ i ∨ kO ≤ i) := by
      intro k i hi hk
      rw [fixA_exec_od s _ k i hi hk, max_eq_true, hw_ev _ i hi rfl, hw_od _ i hi rfl]
    have hy : ∀ k : Fin (2 ^ (s + 1)), (ssSort (s + 1)).exec v k = true ↔ kE + kO ≤ k.val := by
      intro k
      have hk2 := k.2
      rw [ssSort_exec_succ]
      rcases Nat.even_or_odd' k.val with ⟨i, hi | hi⟩
      · by_cases h0 : i = 0
        · rw [fixB_exec_end s _ k (Or.inl (by omega)), hx_ev k i (by omega) hi]
          omega
        · rw [fixB_exec_hi s _ k (i - 1) (by omega) (by omega), max_eq_true,
            hx_od _ (i - 1) (by omega) rfl,
            hx_ev _ i (by omega) (show 2 * (i - 1) + 2 = 2 * i by omega)]
          omega
      · by_cases hlast : k.val + 1 = 2 ^ (s + 1)
        · rw [fixB_exec_end s _ k (Or.inr hlast), hx_od k i (by omega) hi]
          omega
        · rw [fixB_exec_lo s _ k i (by omega) hi, min_eq_true, hx_od _ i (by omega) rfl,
            hx_ev _ (i + 1) (by omega) (show 2 * i + 2 = 2 * (i + 1) by omega)]
          omega
    intro a b hab
    cases h : (ssSort (s + 1)).exec v a
    · exact Bool.false_le _
    · have := (hy b).2 (((hy a).1 h).trans (Fin.le_iff_val_le_val.1 hab))
      rw [this]

/-- **The two-run sorter sorts every two-run input** (any linear order; 0-1 principle restricted to
two-run inputs, which are closed under monotone maps). -/
theorem ssSort_sorts (s : ℕ) {α : Type*} [LinearOrder α] (v : Fin (2 ^ s) → α) (hv : TwoRun v) :
    Monotone ((ssSort s).exec v) := by
  by_contra h_not_mono
  simp only [Monotone, not_forall, not_le] at h_not_mono
  obtain ⟨i, j, hij, hlt⟩ := h_not_mono
  have hf : Monotone fun x : α ↦ decide (((ssSort s).exec v) j < x) := fun a b hab ↦ by
    by_cases ha : ((ssSort s).exec v) j < a
    · simp [ha, lt_of_lt_of_le ha hab]
    · simp [ha]
  have h_sorted := ssSort_sorts_bool s _ (hv.comp_monotone hf) hij
  have hcomm := congr_fun ((ssSort s).exec_comp_monotone hf v)
  simp only [Function.comp] at hcomm
  rw [← hcomm i, ← hcomm j] at h_sorted
  simp [hlt] at h_sorted
  exact absurd h_sorted (by decide)

/-! ### Blocks of two runs -/

/-- Every aligned block `[c 2^s, (c+1) 2^s)` of `v` is two sorted runs. -/
def BlockTwoRun (s : ℕ) {m : ℕ} {α : Type*} [Preorder α] (v : Fin m → α) : Prop :=
  ∀ c : ℕ, ∃ p : ℕ,
    (∀ i j : Fin m, i.val / 2 ^ s = c → j.val / 2 ^ s = c → i ≤ j → j.val < p → v i ≤ v j) ∧
    (∀ i j : Fin m, i.val / 2 ^ s = c → j.val / 2 ^ s = c → p ≤ i.val → i ≤ j → v i ≤ v j)

theorem BlockTwoRun.comp_monotone {s m : ℕ} {α β : Type*} [Preorder α] [Preorder β] {f : α → β}
    (hf : Monotone f) {v : Fin m → α} (hv : BlockTwoRun s v) : BlockTwoRun s (f ∘ v) := by
  intro c
  obtain ⟨p, h1, h2⟩ := hv c
  exact ⟨p, fun i j a b c d => hf (h1 i j a b c d), fun i j a b c d => hf (h2 i j a b c d)⟩

theorem BlockTwoRun.twoRun {s : ℕ} {α : Type*} [Preorder α] {v : Fin (2 ^ (s + 0)) → α}
    (hv : BlockTwoRun s v) : TwoRun v := by
  obtain ⟨p, h1, h2⟩ := hv 0
  have hdiv : ∀ i : Fin (2 ^ (s + 0)), i.val / 2 ^ s = 0 := fun i =>
    Nat.div_eq_of_lt (by simp)
  exact ⟨p, fun i j hij hj => h1 i j (hdiv i) (hdiv j) hij hj,
    fun i j hi hij => h2 i j (hdiv i) (hdiv j) hi hij⟩

theorem blockTwoRun_halves {s k n : ℕ} {α : Type*} [Preorder α]
    (hn : 2 ^ (s + k) + 2 ^ (s + k) = n) (v : Fin n → α) (hv : BlockTwoRun s v) :
    BlockTwoRun s (lowH hn v) ∧ BlockTwoRun s (upH hn v) := by
  obtain ⟨c0, hc⟩ : 2 ^ s ∣ 2 ^ (s + k) := pow_dvd_pow 2 (Nat.le_add_right s k)
  have hpos : 0 < 2 ^ s := by positivity
  have key : ∀ a : ℕ, (2 ^ (s + k) + a) / 2 ^ s = c0 + a / 2 ^ s := fun a => by
    rw [hc]; exact Nat.mul_add_div hpos c0 a
  refine ⟨fun c => ?_, fun c => ?_⟩
  · obtain ⟨p, h1, h2⟩ := hv c
    exact ⟨p, fun i j hi hj hij hjp => h1 _ _ hi hj hij hjp,
      fun i j hi hj hp hij => h2 _ _ hi hj hp hij⟩
  · obtain ⟨p, h1, h2⟩ := hv (c0 + c)
    refine ⟨p - 2 ^ (s + k), fun i j hi hj hij hjp => h1 _ _ ?_ ?_ ?_ ?_,
      fun i j hi hj hp hij => h2 _ _ ?_ ?_ ?_ ?_⟩
    · show (2 ^ (s + k) + i.val) / 2 ^ s = c0 + c
      rw [key, hi]
    · show (2 ^ (s + k) + j.val) / 2 ^ s = c0 + c
      rw [key, hj]
    · show 2 ^ (s + k) + i.val ≤ 2 ^ (s + k) + j.val
      have : i.val ≤ j.val := hij
      omega
    · show 2 ^ (s + k) + j.val < p
      omega
    · show (2 ^ (s + k) + i.val) / 2 ^ s = c0 + c
      rw [key, hi]
    · show (2 ^ (s + k) + j.val) / 2 ^ s = c0 + c
      rw [key, hj]
    · show p ≤ 2 ^ (s + k) + i.val
      omega
    · show 2 ^ (s + k) + i.val ≤ 2 ^ (s + k) + j.val
      have : i.val ≤ j.val := hij
      omega

/-- `ssSort s` on every aligned `2^s` block of `2^(s+k)` wires. -/
def ssBlocks (s : ℕ) : (k : ℕ) → ComparatorNetwork (2 ^ (s + k))
  | 0 => ssSort s
  | k + 1 => par (two_pow_succ' (s + k)) (ssBlocks s k) (ssBlocks s k)

theorem ssBlocks_depth_le (s : ℕ) : ∀ k, (ssBlocks s k).depth ≤ (ssSort s).depth
  | 0 => le_rfl
  | k + 1 => depth_par _ _ _ _ (ssBlocks_depth_le s k) (ssBlocks_depth_le s k)

/-- **Block two-run sorts make the input run-sorted.** -/
theorem ssBlocks_runSorted (s : ℕ) {α : Type*} [LinearOrder α] :
    ∀ (k : ℕ) (v : Fin (2 ^ (s + k)) → α), BlockTwoRun s v → RunSorted s ((ssBlocks s k).exec v)
  | 0, v, hv => fun i j hij _ => ssSort_sorts s v hv.twoRun hij
  | k + 1, v, hv => by
    have hn := two_pow_succ' (s + k)
    obtain ⟨b0, b1⟩ := blockTwoRun_halves (k := k) hn v hv
    obtain ⟨p1, p2⟩ := par_exec hn (ssBlocks s k) (ssBlocks s k) v
    show RunSorted s ((par hn (ssBlocks s k) (ssBlocks s k)).exec v)
    exact runSorted_of_halves (k := k) hn _ (by rw [p1]; exact ssBlocks_runSorted s k _ b0)
      (by rw [p2]; exact ssBlocks_runSorted s k _ b1)

/-! ### The unaligned run merge -/

/-- Two-run sorts of the aligned `2^s` blocks, then the run merge from length `2^s`. -/
def uRunMerge (s k : ℕ) : ComparatorNetwork (2 ^ (s + k)) :=
  (ssBlocks s k).append (runMerge s k)

theorem uRunMerge_sorts (s k : ℕ) {α : Type*} [LinearOrder α] (v : Fin (2 ^ (s + k)) → α)
    (hv : BlockTwoRun s v) : Monotone ((uRunMerge s k).exec v) := by
  rw [show (uRunMerge s k).exec v = (runMerge s k).exec ((ssBlocks s k).exec v) from
    exec_append _ _ v]
  exact runMerge_sorts s k _ (ssBlocks_runSorted s k v hv)

/-- **Depth** at block length `2^(s+1)`: the run merge from `2^(s+1)` plus `2(s+1) - 1` levels. -/
theorem uRunMerge_depth_le (s k : ℕ) :
    (uRunMerge (s + 1) k).depth + bitonicDepthBudget (s + 1) ≤
      2 * s + 1 + bitonicDepthBudget (s + 1 + k) := by
  have h1 := depth_append_le (ssBlocks (s + 1) k) (runMerge (s + 1) k)
  have h2 := ssBlocks_depth_le (s + 1) k
  have h3 := ssSort_depth_le s
  have h4 := runMerge_depth_le (s + 1) k
  unfold uRunMerge
  omega

/-- The unaligned run merge on any number `m` of wires (padding with `true`). -/
def uRunMergeNetwork (s m : ℕ) : ComparatorNetwork m :=
  (uRunMerge s (Nat.clog 2 m - s)).restrictWires m
    ((Nat.le_pow_clog (by omega) m).trans (Nat.pow_le_pow_right (by omega) (by omega)))

theorem uRunMergeNetwork_depth_le (s m : ℕ) :
    (uRunMergeNetwork (s + 1) m).depth + bitonicDepthBudget (s + 1) ≤
      2 * s + 1 + bitonicDepthBudget (s + 1 + (Nat.clog 2 m - (s + 1))) :=
  (Nat.add_le_add_right (restrictWires_depth_le _ _ _) _).trans (uRunMerge_depth_le s _)

theorem uRunMergeNetwork_sorts_bool (s m : ℕ) (v : Fin m → Bool) (hv : BlockTwoRun s v) :
    Monotone ((uRunMergeNetwork s m).exec v) := by
  intro i j hij
  unfold uRunMergeNetwork
  rw [restrictWires_exec_pad, restrictWires_exec_pad]
  refine uRunMerge_sorts s _ _ ?_ (show (⟨i.val, _⟩ : Fin _) ≤ ⟨j.val, _⟩ from hij)
  intro c
  obtain ⟨p, h1, h2⟩ := hv c
  refine ⟨p, fun a b ha hb hab hbp => ?_, fun a b ha hb hpa hab => ?_⟩
  · have hab' : a.val ≤ b.val := hab
    by_cases hbm : b.val < m
    · have ham : a.val < m := lt_of_le_of_lt hab' hbm
      simp only [ham, hbm, dite_true]
      exact h1 ⟨a.val, ham⟩ ⟨b.val, hbm⟩ ha hb hab hbp
    · simp only [hbm, dite_false]
      exact Bool.le_true _
  · have hab' : a.val ≤ b.val := hab
    by_cases hbm : b.val < m
    · have ham : a.val < m := lt_of_le_of_lt hab' hbm
      simp only [ham, hbm, dite_true]
      exact h2 ⟨a.val, ham⟩ ⟨b.val, hbm⟩ ha hb hpa hab
    · simp only [hbm, dite_false]
      exact Bool.le_true _

/-- **The unaligned run merge sorts every block-two-run input on any number of wires.** -/
theorem uRunMergeNetwork_sorts (s m : ℕ) {α : Type*} [LinearOrder α] (v : Fin m → α)
    (hv : BlockTwoRun s v) : Monotone ((uRunMergeNetwork s m).exec v) := by
  by_contra h_not_mono
  simp only [Monotone, not_forall, not_le] at h_not_mono
  obtain ⟨i, j, hij, hlt⟩ := h_not_mono
  have hf : Monotone fun x : α ↦ decide (((uRunMergeNetwork s m).exec v) j < x) := fun a b hab ↦ by
    by_cases ha : ((uRunMergeNetwork s m).exec v) j < a
    · simp [ha, lt_of_lt_of_le ha hab]
    · simp [ha]
  have h_sorted := uRunMergeNetwork_sorts_bool s m _ (hv.comp_monotone hf) hij
  have hcomm := congr_fun ((uRunMergeNetwork s m).exec_comp_monotone hf v)
  simp only [Function.comp] at hcomm
  rw [← hcomm i, ← hcomm j] at h_sorted
  simp [hlt] at h_sorted
  exact absurd h_sorted (by decide)

/-! ### Runs with arbitrary boundaries -/

/-- Any two descents of `v` are at least `R` apart: `v` is a concatenation of sorted runs, every
interior run of length `≥ R`, with arbitrary (unaligned) boundaries. -/
def DescentsApart (R : ℕ) {m : ℕ} {α : Type*} [Preorder α] (v : Fin m → α) : Prop :=
  ∀ (p q : ℕ) (hp : p + 1 < m) (hq : q + 1 < m), p < q →
    ¬ v ⟨p, by omega⟩ ≤ v ⟨p + 1, hp⟩ → ¬ v ⟨q, by omega⟩ ≤ v ⟨q + 1, hq⟩ → R ≤ q - p

theorem DescentsApart.comp_monotone {R m : ℕ} {α β : Type*} [Preorder α] [Preorder β] {f : α → β}
    (hf : Monotone f) {v : Fin m → α} (hv : DescentsApart R v) : DescentsApart R (f ∘ v) :=
  fun p q hp hq hpq dp dq => hv p q hp hq hpq (fun h => dp (hf h)) (fun h => dq (hf h))

/-- Adjacent steps `≤` on `[i, j]` give `v i ≤ v j`. -/
theorem chain_le {m : ℕ} {α : Type*} [Preorder α] (v : Fin m → α) (i j : Fin m) (hij : i ≤ j)
    (h : ∀ (k : ℕ) (hk : k + 1 < m), i.val ≤ k → k < j.val → v ⟨k, by omega⟩ ≤ v ⟨k + 1, hk⟩) :
    v i ≤ v j := by
  have hij' : i.val ≤ j.val := Fin.le_iff_val_le_val.1 hij
  have key : ∀ d : ℕ, ∀ hd : i.val + d < m, i.val + d ≤ j.val → v i ≤ v ⟨i.val + d, hd⟩ := by
    intro d
    induction d with
    | zero => intro hd _; exact le_of_eq (congrArg v (Fin.ext (by simp)))
    | succ d ih =>
      intro hd hdj
      exact (ih (by omega) (by omega)).trans (h (i.val + d) (by omega) (by omega) (by omega))
  have := key (j.val - i.val) (by omega) (by omega)
  rwa [show (⟨i.val + (j.val - i.val), by omega⟩ : Fin m) = j from Fin.ext (by simp; omega)] at this

theorem sub_lt_of_div_eq {B i j : ℕ} (hB : 0 < B) (h : i / B = j / B) (hij : i ≤ j) : j - i < B := by
  have hi := Nat.div_add_mod i B
  have hj := Nat.div_add_mod j B
  have hmi := Nat.mod_lt i hB
  have hmj := Nat.mod_lt j hB
  rw [h] at hi
  generalize B * (j / B) = X at hi hj
  omega

/-- **Runs of length `≥ R` with arbitrary boundaries are block-two-run** at block length `2^s`,
`2^s ≤ R + 1`: an aligned block of `2^s` positions holds at most one descent. -/
theorem blockTwoRun_of_descentsApart {s R m : ℕ} {α : Type*} [Preorder α] (hR : 2 ^ s ≤ R + 1)
    (v : Fin m → α) (hv : DescentsApart R v) : BlockTwoRun s v := by
  classical
  have hB : 0 < 2 ^ s := by positivity
  intro c
  have inblk : ∀ a b k : ℕ, a / 2 ^ s = c → b / 2 ^ s = c → a ≤ k → k ≤ b → k / 2 ^ s = c :=
    fun a b k ha hb h1 h2 =>
      le_antisymm (hb ▸ Nat.div_le_div_right h2) (ha ▸ Nat.div_le_div_right h1)
  have uniq : ∀ (p q : ℕ) (hp : p + 1 < m) (hq : q + 1 < m), p / 2 ^ s = c → (q + 1) / 2 ^ s = c →
      p < q → ¬ v ⟨p, by omega⟩ ≤ v ⟨p + 1, hp⟩ → ¬ v ⟨q, by omega⟩ ≤ v ⟨q + 1, hq⟩ → False := by
    intro p q hp hq hpc hqc hpq dp dq
    have h1 := hv p q hp hq hpq dp dq
    have h2 := sub_lt_of_div_eq hB (hpc.trans hqc.symm) (by omega)
    omega
  by_cases hD : ∃ (p : ℕ) (hp : p + 1 < m), p / 2 ^ s = c ∧ (p + 1) / 2 ^ s = c ∧
      ¬ v ⟨p, by omega⟩ ≤ v ⟨p + 1, hp⟩
  · obtain ⟨p, hp, hpc, hpc1, dp⟩ := hD
    refine ⟨p + 1, fun i j hi hj hij hjp => chain_le v i j hij fun k hk h1 h2 => ?_,
      fun i j hi hj hpi hij => chain_le v i j hij fun k hk h1 h2 => ?_⟩
    · by_contra dk
      exact uniq k p hk hp (inblk i.val p k hi hpc h1 (by omega)) hpc1 (by omega) dk dp
    · by_contra dk
      exact uniq p k hp hk hpc (inblk i.val j.val (k + 1) hi hj (by omega) (by omega)) (by omega)
        dp dk
  · refine ⟨0, fun i j _ _ _ hjp => absurd hjp (Nat.not_lt_zero _),
      fun i j hi hj _ hij => chain_le v i j hij fun k hk h1 h2 => ?_⟩
    by_contra dk
    exact hD ⟨k, hk, inblk i.val j.val k hi hj h1 (by omega),
      inblk i.val j.val (k + 1) hi hj (by omega) (by omega), dk⟩

/-- **The unaligned run merge sorts every input whose descents are `R` apart**, `2^s ≤ R + 1`
(sorted runs of length `≥ R` with arbitrary boundaries), on any number of wires, any linear order. -/
theorem uRunMergeNetwork_sorts_of_descentsApart {s R : ℕ} (hR : 2 ^ s ≤ R + 1) (m : ℕ)
    {α : Type*} [LinearOrder α] (v : Fin m → α) (hv : DescentsApart R v) :
    Monotone ((uRunMergeNetwork s m).exec v) :=
  uRunMergeNetwork_sorts s m v (blockTwoRun_of_descentsApart hR v hv)

end Bitonic

end
