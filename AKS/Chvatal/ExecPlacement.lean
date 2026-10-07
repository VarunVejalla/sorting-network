module
/-
  # Execution-defined placement of the Chvátal tree network

  Source: V. Chvátal, *Lecture Notes on the New AKS Sorting Network*,
  Rutgers DCS-TR-294 (1992), §3. Running the stage networks `stageNet (wireSets F t) (nets t)`
  one after another on a permutation `v` of distinct keys, `X v t` is the key sitting on each
  wire after `t` stages.  A comparator network only permutes values, so `X v t = v ∘ ρ`; the keys
  on node `b`'s wires, `(wireSets F t b).image (X v t)`, form a `Placement`.  We also record
  which keys are sent up and down in stage `t`, that node networks keep keys inside the node,
  and a dictionary between cells of a node network and wires/keys.

  Main results: `ComparatorNetwork.exec_eq_comp_perm`, `X_eq_comp_perm` (E1), `execPlacement`
  (E2), `execPlacement_succ_regs` (E3a), `stage_preserves_node_keys` (E4),
  `fromChildrenK_subset`/`fromParentK_subset` (E3b), `rankIn_orderEmb`, `mem_blockOf_iff`,
  `mem_image_blockOf_iff` (E5).
-/

public import AKS.Chvatal.WireFlow
public import AKS.Chvatal.StageNet

@[expose] public section

namespace Chvatal

open Finset

/-! **E1: comparator networks permute values** -/

theorem Comparator.apply_eq_comp_perm {n : ℕ} {α : Type*} [LinearOrder α]
    (c : Comparator n) (v : Fin n → α) : ∃ ρ : Equiv.Perm (Fin n), c.apply v = v ∘ ρ := by
  by_cases h : v c.i ≤ v c.j
  · refine ⟨1, ?_⟩
    ext k; unfold Comparator.apply
    by_cases hki : k = c.i
    · subst hki; rw [if_pos rfl, min_eq_left h]; rfl
    · rw [if_neg hki]
      by_cases hkj : k = c.j
      · subst hkj; rw [if_pos rfl, max_eq_right h]; rfl
      · rw [if_neg hkj]; rfl
  · push_neg at h
    refine ⟨Equiv.swap c.i c.j, ?_⟩
    ext k; unfold Comparator.apply; simp only [Function.comp]
    by_cases hki : k = c.i
    · subst hki; rw [if_pos rfl, min_eq_right h.le, Equiv.swap_apply_left]
    · rw [if_neg hki]
      by_cases hkj : k = c.j
      · subst hkj; rw [if_pos rfl, max_eq_left h.le, Equiv.swap_apply_right]
      · rw [if_neg hkj, Equiv.swap_apply_of_ne_of_ne hki hkj]

theorem foldl_apply_eq_comp_perm {n : ℕ} {α : Type*} [LinearOrder α]
    (cs : List (Comparator n)) (v : Fin n → α) :
    ∃ ρ : Equiv.Perm (Fin n), cs.foldl (fun acc c => c.apply acc) v = v ∘ ρ := by
  induction cs generalizing v with
  | nil => exact ⟨1, rfl⟩
  | cons c cs ih =>
    obtain ⟨ρ₁, h₁⟩ := Comparator.apply_eq_comp_perm c v
    obtain ⟨ρ₂, h₂⟩ := ih (c.apply v)
    refine ⟨ρ₁ * ρ₂, ?_⟩
    simp only [List.foldl_cons]
    rw [h₂, h₁]
    rfl

/-- A comparator network's output is the input composed with a permutation of the wires. -/
theorem ComparatorNetwork.exec_eq_comp_perm {n : ℕ} {α : Type*} [LinearOrder α]
    (net : ComparatorNetwork n) (v : Fin n → α) :
    ∃ ρ : Equiv.Perm (Fin n), net.exec v = v ∘ ρ :=
  foldl_apply_eq_comp_perm net.comparators v

/-! **The execution** -/

variable {d tf : ℕ}

/-- The key on each wire after `t` stages: `X v 0 = v`, `X v (t+1) = (stage t).exec (X v t)`,
where `stage t = stageNet (wireSets F t) (nets t)`. -/
noncomputable def X (F : FlowSizes d tf)
    (nets : ℕ → (b : KBag 64 d) → (n : ℕ) → ComparatorNetwork n)
    (v : Equiv.Perm (Fin (64 ^ d))) : ℕ → Fin (64 ^ d) → Fin (64 ^ d)
  | 0 => fun w => v w
  | t + 1 => (stageNet (wireSets F t) (nets t)).exec (X F nets v t)

section Exec

variable (F : FlowSizes d tf) (nets : ℕ → (b : KBag 64 d) → (n : ℕ) → ComparatorNetwork n)
  (v : Equiv.Perm (Fin (64 ^ d)))

theorem X_zero : X F nets v 0 = fun w => v w := rfl

theorem X_succ (t : ℕ) :
    X F nets v (t + 1) = (stageNet (wireSets F t) (nets t)).exec (X F nets v t) := rfl

/-- E1. -/
theorem X_eq_comp_perm : ∀ t, ∃ ρ : Equiv.Perm (Fin (64 ^ d)), X F nets v t = v ∘ ρ
  | 0 => ⟨1, rfl⟩
  | t + 1 => by
    obtain ⟨ρ₁, h₁⟩ := X_eq_comp_perm t
    obtain ⟨ρ₂, h₂⟩ := ComparatorNetwork.exec_eq_comp_perm
      (stageNet (wireSets F t) (nets t)) (X F nets v t)
    refine ⟨ρ₁ * ρ₂, ?_⟩
    rw [X_succ, h₂, h₁]
    rfl

theorem X_injective (t : ℕ) : Function.Injective (X F nets v t) := by
  obtain ⟨ρ, h⟩ := X_eq_comp_perm F nets v t
  rw [h]
  exact v.injective.comp ρ.injective

theorem X_surjective (t : ℕ) : Function.Surjective (X F nets v t) :=
  Finite.injective_iff_surjective.1 (X_injective F nets v t)

/-! **E2: the execution-defined placement** -/

/-- The keys sitting on node `b`'s wires after `t` stages. -/
noncomputable def execPlacement (t : ℕ) (ht : t ≤ tf) : Placement 64 d where
  regs b := (wireSets F t b).image (X F nets v t)
  disjoint a b hab := by
    rw [Finset.disjoint_image (X_injective F nets v t)]
    exact wireSets_disjoint F ht a b hab
  complete i := by
    obtain ⟨w, rfl⟩ := X_surjective F nets v t i
    obtain ⟨b, hb⟩ := wireSets_complete F ht w
    exact ⟨b, Finset.mem_image_of_mem _ hb⟩

theorem execPlacement_card (t : ℕ) (ht : t ≤ tf) (b : KBag 64 d) :
    (((execPlacement F nets v t ht).regs b)).card = F.a b.l t := by
  show ((wireSets F t b).image (X F nets v t)).card = _
  rw [Finset.card_image_of_injective _ (X_injective F nets v t)]
  exact wireSets_card F ht b

/-! **E3: keys sent in stage `t`** -/

/-- Keys that the parent's separator sent down to `b` (values after stage `t`). -/
noncomputable def fromParentK (t : ℕ) (b : KBag 64 d) : Finset (Fin (64 ^ d)) :=
  (downSet (wireSets F t b.parent) (F.up (b.l - 1) t) (F.down (b.l - 1) t) (b.x % 64)).image
    (X F nets v (t + 1))

/-- Keys that the children's separators sent up to `b` (values after stage `t`). -/
noncomputable def fromChildrenK (t : ℕ) (b : KBag 64 d) : Finset (Fin (64 ^ d)) :=
  if h : b.l < d then
    Finset.univ.biUnion (fun j : Fin 64 =>
      (upSet (wireSets F t (b.child j.val j.isLt h)) (F.up (b.l + 1) t)).image
        (X F nets v (t + 1)))
  else ∅

/-- E3a (nodes below the root). -/
theorem execPlacement_succ_regs (t : ℕ) (ht : t < tf) (b : KBag 64 d) (hb : 1 ≤ b.l) :
    (execPlacement F nets v (t + 1) ht).regs b =
      fromParentK F nets v t b ∪ fromChildrenK F nets v t b := by
  show (wireSets F (t + 1) b).image (X F nets v (t + 1)) = _
  rw [wireSets_succ_eq, Finset.image_union]
  unfold parentPart childPart fromParentK fromChildrenK
  rw [if_pos hb]
  congr 1
  split_ifs with h
  · ext k; simp only [Finset.mem_image, Finset.mem_biUnion, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨w, ⟨j, hj⟩, rfl⟩; exact ⟨j, w, hj, rfl⟩
    · rintro ⟨j, w, hj, rfl⟩; exact ⟨w, ⟨j, hj⟩, rfl⟩
  · simp

/-- E3a (root). -/
theorem execPlacement_succ_regs_root (t : ℕ) (ht : t < tf) (b : KBag 64 d) (hb : b.l = 0) :
    (execPlacement F nets v (t + 1) ht).regs b = fromChildrenK F nets v t b := by
  show (wireSets F (t + 1) b).image (X F nets v (t + 1)) = _
  rw [wireSets_succ_eq, Finset.image_union]
  unfold parentPart childPart fromChildrenK
  rw [if_neg (by omega)]
  simp only [Finset.image_empty, Finset.empty_union]
  split_ifs with h
  · ext k; simp only [Finset.mem_image, Finset.mem_biUnion, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨w, ⟨j, hj⟩, rfl⟩; exact ⟨j, w, hj, rfl⟩
    · rintro ⟨j, w, hj, rfl⟩; exact ⟨w, ⟨j, hj⟩, rfl⟩
  · simp

/-! **E4: node networks keep keys inside the node** -/

theorem exists_orderEmb_eq {N : ℕ} {s : Finset (Fin N)} {w : Fin N} (hw : w ∈ s) :
    ∃ c : Fin s.card, s.orderEmbOfFin rfl c = w := by
  have : w ∈ Set.range (s.orderEmbOfFin rfl) := by
    rw [Finset.range_orderEmbOfFin]; exact hw
  exact this

/-- The key on the `c`-th cell of node `q` after stage `t` is the output of the node network
on the node's input vector. -/
theorem X_succ_inside (t : ℕ) (ht : t < tf) (q : KBag 64 d) (c : Fin (wireSets F t q).card) :
    X F nets v (t + 1) ((wireSets F t q).orderEmbOfFin rfl c) =
      (nets t q (wireSets F t q).card).exec
        (fun i => X F nets v t ((wireSets F t q).orderEmbOfFin rfl i)) c := by
  rw [X_succ]
  exact stageNet_exec_inside (wireSets F t) (wireSets_disjoint F ht.le) (nets t)
    (X F nets v t) q c

/-- E4. -/
theorem stage_preserves_node_keys (t : ℕ) (ht : t < tf) (q : KBag 64 d) :
    (wireSets F t q).image (X F nets v (t + 1)) = (wireSets F t q).image (X F nets v t) := by
  apply Finset.eq_of_subset_of_card_le
  · intro k hk
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.1 hk
    obtain ⟨c, rfl⟩ := exists_orderEmb_eq hw
    rw [X_succ_inside F nets v t ht q c]
    obtain ⟨ρ, hρ⟩ := ComparatorNetwork.exec_eq_comp_perm (nets t q (wireSets F t q).card)
      (fun i => X F nets v t ((wireSets F t q).orderEmbOfFin rfl i))
    rw [hρ]
    exact Finset.mem_image_of_mem _ (Finset.orderEmbOfFin_mem _ rfl _)
  · rw [Finset.card_image_of_injective _ (X_injective F nets v t),
      Finset.card_image_of_injective _ (X_injective F nets v (t + 1))]

/-- E3b: keys sent up came from the children's registers. -/
theorem fromChildrenK_subset (t : ℕ) (ht : t < tf) (b : KBag 64 d) (h : b.l < d) :
    fromChildrenK F nets v t b ⊆
      Finset.univ.biUnion (fun j : Fin 64 =>
        (execPlacement F nets v t ht.le).regs (b.child j.val j.isLt h)) := by
  unfold fromChildrenK
  rw [dif_pos h]
  intro k hk
  simp only [Finset.mem_biUnion, Finset.mem_univ, true_and] at hk ⊢
  obtain ⟨j, hj⟩ := hk
  refine ⟨j, ?_⟩
  show k ∈ (wireSets F t _).image (X F nets v t)
  rw [← stage_preserves_node_keys F nets v t ht]
  exact Finset.image_subset_image upSet_subset hj

theorem fromChildrenK_of_not_lt (t : ℕ) (b : KBag 64 d) (h : ¬ b.l < d) :
    fromChildrenK F nets v t b = ∅ := by
  unfold fromChildrenK; rw [dif_neg h]

/-- E3b: keys sent down came from the parent's register. -/
theorem fromParentK_subset (t : ℕ) (ht : t < tf) (b : KBag 64 d) :
    fromParentK F nets v t b ⊆ (execPlacement F nets v t ht.le).regs b.parent := by
  unfold fromParentK
  show _ ⊆ (wireSets F t _).image (X F nets v t)
  rw [← stage_preserves_node_keys F nets v t ht]
  exact Finset.image_subset_image downSet_subset

end Exec

/-! **E5: dictionary between cells, wires and keys** -/

section Dict

variable {n : ℕ} {s : Finset (Fin n)}

theorem rankIn_orderEmb (c : Fin s.card) :
    rankIn s (s.orderEmbOfFin rfl c) = c.val := by
  have h : s.filter (· < s.orderEmbOfFin rfl c) = (Finset.Iio c).image (s.orderEmbOfFin rfl) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_Iio]
    constructor
    · rintro ⟨hx, hlt⟩
      obtain ⟨j, rfl⟩ := exists_orderEmb_eq hx
      exact ⟨j, (s.orderEmbOfFin rfl).lt_iff_lt.1 hlt, rfl⟩
    · rintro ⟨j, hj, rfl⟩
      exact ⟨Finset.orderEmbOfFin_mem _ rfl _, (s.orderEmbOfFin rfl).lt_iff_lt.2 hj⟩
  unfold rankIn
  rw [h, Finset.card_image_of_injective _ (s.orderEmbOfFin rfl).injective]
  simp

theorem mem_blockOf_iff {lo hi : ℕ} {w : Fin n} :
    w ∈ blockOf s lo hi ↔
      ∃ c : Fin s.card, lo ≤ c.val ∧ c.val < hi ∧ w = s.orderEmbOfFin rfl c := by
  rw [mem_blockOf]
  constructor
  · rintro ⟨hw, h1, h2⟩
    obtain ⟨c, rfl⟩ := exists_orderEmb_eq hw
    rw [rankIn_orderEmb] at h1 h2
    exact ⟨c, h1, h2, rfl⟩
  · rintro ⟨c, h1, h2, rfl⟩
    rw [rankIn_orderEmb]
    exact ⟨Finset.orderEmbOfFin_mem _ rfl _, h1, h2⟩

/-- The block of ranks `[lo, hi)` as the image of the cells `[lo, hi) ∩ [0, card)`. -/
theorem blockOf_eq_image (lo hi : ℕ) :
    blockOf s lo hi = ((Finset.univ : Finset (Fin s.card)).filter
      (fun c => lo ≤ c.val ∧ c.val < hi)).image (s.orderEmbOfFin rfl) := by
  ext w
  rw [mem_blockOf_iff]
  simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨c, h1, h2, rfl⟩; exact ⟨c, ⟨h1, h2⟩, rfl⟩
  · rintro ⟨c, ⟨h1, h2⟩, rfl⟩; exact ⟨c, h1, h2, rfl⟩

end Dict

section KeyDict

variable {d tf : ℕ} (F : FlowSizes d tf)
  (nets : ℕ → (b : KBag 64 d) → (n : ℕ) → ComparatorNetwork n)
  (v : Equiv.Perm (Fin (64 ^ d)))

/-- A key lies in the image (after stage `t`) of a rank block of node `q` iff it is the output of
the node network on a cell in that block, fed with the node's input vector. -/
theorem mem_image_blockOf_iff (t : ℕ) (ht : t < tf) (q : KBag 64 d) (lo hi : ℕ)
    (k : Fin (64 ^ d)) :
    k ∈ (blockOf (wireSets F t q) lo hi).image (X F nets v (t + 1)) ↔
      ∃ c : Fin (wireSets F t q).card, lo ≤ c.val ∧ c.val < hi ∧
        k = (nets t q (wireSets F t q).card).exec
          (fun i => X F nets v t ((wireSets F t q).orderEmbOfFin rfl i)) c := by
  rw [Finset.mem_image]
  constructor
  · rintro ⟨w, hw, rfl⟩
    obtain ⟨c, h1, h2, rfl⟩ := mem_blockOf_iff.1 hw
    exact ⟨c, h1, h2, X_succ_inside F nets v t ht q c⟩
  · rintro ⟨c, h1, h2, rfl⟩
    exact ⟨_, mem_blockOf_iff.2 ⟨c, h1, h2, rfl⟩, X_succ_inside F nets v t ht q c⟩

/-- Keys sent down to child `j`: outputs of the node network on cells of the `j`-th middle block. -/
theorem mem_image_downSet_iff (t : ℕ) (ht : t < tf) (q : KBag 64 d) (π τ j : ℕ)
    (k : Fin (64 ^ d)) :
    k ∈ (downSet (wireSets F t q) π τ j).image (X F nets v (t + 1)) ↔
      ∃ c : Fin (wireSets F t q).card, π / 2 + j * τ ≤ c.val ∧ c.val < π / 2 + (j + 1) * τ ∧
        k = (nets t q (wireSets F t q).card).exec
          (fun i => X F nets v t ((wireSets F t q).orderEmbOfFin rfl i)) c :=
  mem_image_blockOf_iff F nets v t ht q _ _ k

/-- Keys sent up: outputs of the node network on the first `π/2` or last `π/2` cells. -/
theorem mem_image_upSet_iff (t : ℕ) (ht : t < tf) (q : KBag 64 d) (π : ℕ)
    (k : Fin (64 ^ d)) :
    k ∈ (upSet (wireSets F t q) π).image (X F nets v (t + 1)) ↔
      ∃ c : Fin (wireSets F t q).card,
        (c.val < π / 2 ∨ (wireSets F t q).card - π / 2 ≤ c.val) ∧
        k = (nets t q (wireSets F t q).card).exec
          (fun i => X F nets v t ((wireSets F t q).orderEmbOfFin rfl i)) c := by
  unfold upSet
  rw [Finset.image_union, Finset.mem_union, mem_image_blockOf_iff F nets v t ht,
    mem_image_blockOf_iff F nets v t ht]
  constructor
  · rintro (⟨c, h1, h2, h3⟩ | ⟨c, h1, h2, h3⟩)
    · exact ⟨c, Or.inl h2, h3⟩
    · exact ⟨c, Or.inr h1, h3⟩
  · rintro ⟨c, h1 | h1, h3⟩
    · exact Or.inl ⟨c, Nat.zero_le _, h1, h3⟩
    · exact Or.inr ⟨c, h1, c.isLt, h3⟩

end KeyDict

end Chvatal
