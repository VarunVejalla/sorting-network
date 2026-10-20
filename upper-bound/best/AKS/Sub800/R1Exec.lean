import AKS.Sub800.R1Wire

/-! # Stage networks and the execution-defined placement at branching factor 16 (W1, step 3)

Port of the package's `StageNet` (the `br`-specific part) and UB-12's generic `ExecPlacement`. -/

namespace R1T

open Chvatal (KBag Placement nodeList mem_nodeList nodeList_nodup flatMap_scatter_exec_inside
  orderEmb_disjoint)

/-- The stage network: node networks `nodeNet b (S b).card`, each embedded along
`(S b).orderEmbOfFin rfl` (comparator `⟨i,j,h⟩ ↦ ⟨e i, e j, e.lt_iff_lt.2 h⟩`, i.e.
`scatterEmbed`), concatenated over all nodes. -/
noncomputable def stageNet {d : ℕ} (S : KBag 16 d → Finset (Fin (16 ^ d)))
    (nodeNet : (b : KBag 16 d) → (n : ℕ) → ComparatorNetwork n) : ComparatorNetwork (16 ^ d) :=
  ⟨(nodeList 16 d).flatMap fun b =>
    ((nodeNet b (S b).card).scatterEmbed (16 ^ d) ((S b).orderEmbOfFin rfl)).comparators⟩

/-- On the wires of node `b`, the stage network runs `nodeNet b (S b).card` on the local view. -/
theorem stageNet_exec_inside {d : ℕ} {α : Type*} [LinearOrder α]
    (S : KBag 16 d → Finset (Fin (16 ^ d)))
    (hS : ∀ b b', b ≠ b' → Disjoint (S b) (S b'))
    (nodeNet : (b : KBag 16 d) → (n : ℕ) → ComparatorNetwork n)
    (v : Fin (16 ^ d) → α) (b : KBag 16 d) (k : Fin (S b).card) :
    (stageNet S nodeNet).exec v (((S b).orderEmbOfFin rfl) k) =
      (nodeNet b (S b).card).exec (fun i => v (((S b).orderEmbOfFin rfl) i)) k := by
  have hflat := ComparatorNetwork.exec_flatMap (nodeList 16 d)
    (fun a => (nodeNet a (S a).card).scatterEmbed (16 ^ d) ((S a).orderEmbOfFin rfl)) v
  change (⟨(nodeList 16 d).flatMap fun a =>
    ((nodeNet a (S a).card).scatterEmbed (16 ^ d) ((S a).orderEmbOfFin rfl)).comparators⟩ :
      ComparatorNetwork (16 ^ d)).exec v _ = _
  rw [hflat]
  exact flatMap_scatter_exec_inside (m := fun a => (S a).card)
    (fun a => (S a).orderEmbOfFin rfl) (fun a => nodeNet a (S a).card)
    (nodeList 16 d) v (nodeList_nodup 16 d)
    (fun a _ c _ hne i j => orderEmb_disjoint (hS a c hne) i j) b (mem_nodeList b) k

/-- Wire-disjoint concatenation has depth at most the maximum of the parts. -/
theorem stageNet_depth_le {d D : ℕ} (S : KBag 16 d → Finset (Fin (16 ^ d)))
    (hS : ∀ b b', b ≠ b' → Disjoint (S b) (S b'))
    (nodeNet : (b : KBag 16 d) → (n : ℕ) → ComparatorNetwork n)
    (hD : ∀ b, (nodeNet b (S b).card).depth ≤ D) :
    (stageNet S nodeNet).depth ≤ D := by
  refine depth_flatMap_disjoint (nodeList 16 d)
    (fun a => ((nodeNet a (S a).card).scatterEmbed (16 ^ d)
      ((S a).orderEmbOfFin rfl)).comparators) D ?_ ?_
  · intro b _
    exact (depth_scatterEmbed_le _ _ _).trans (hD b)
  · refine List.Pairwise.imp ?_ ((List.nodup_iff_pairwise_ne).mp (nodeList_nodup 16 d))
    intro a c hne c1 hc1 c2 hc2
    obtain ⟨d1, _, rfl⟩ := List.mem_map.mp hc1
    obtain ⟨d2, _, rfl⟩ := List.mem_map.mp hc2
    have h := fun i j => orderEmb_disjoint (hS a c hne) i j
    exact ⟨⟨h _ _, h _ _⟩, ⟨h _ _, h _ _⟩⟩




open Finset

theorem Comparator.apply_eq_comp_perm {n : ℕ} {α : Type*} [LinearOrder α]
    (c : Comparator n) (v : Fin n → α) : ∃ ρ : Equiv.Perm (Fin n), c.apply v = v ∘ ρ := by
  have hij := c.h.ne
  rcases le_total (v c.i) (v c.j) with h | h
  · refine ⟨1, funext fun k => ?_⟩
    unfold Comparator.apply
    split_ifs with h1 h2 <;> simp_all
  · refine ⟨Equiv.swap c.i c.j, funext fun k => ?_⟩
    unfold Comparator.apply
    split_ifs with h1 h2 <;> simp_all [Equiv.swap_apply_of_ne_of_ne]

/-- A comparator network's output is the input composed with a permutation of the wires. -/
theorem ComparatorNetwork.exec_eq_comp_perm {n : ℕ} {α : Type*} [LinearOrder α]
    (net : ComparatorNetwork n) (v : Fin n → α) :
    ∃ ρ : Equiv.Perm (Fin n), net.exec v = v ∘ ρ := by
  obtain ⟨cs⟩ := net
  induction cs generalizing v with
  | nil => exact ⟨1, rfl⟩
  | cons c cs ih =>
    obtain ⟨ρ₁, h₁⟩ := Comparator.apply_eq_comp_perm c v
    obtain ⟨ρ₂, h₂⟩ := ih (c.apply v)
    exact ⟨ρ₁ * ρ₂, by
      show ComparatorNetwork.exec ⟨cs⟩ (c.apply v) = _
      rw [h₂, h₁]; rfl⟩

variable {d tf : ℕ}

/-- The key on each wire after `t` stages: `X v 0 = v`, `X v (t+1) = (stage t).exec (X v t)`,
where `stage t = stageNet (wireSets F t) (nets t)`. -/
noncomputable def X (F : FlowTableB d tf)
    (nets : ℕ → (b : KBag 16 d) → (n : ℕ) → ComparatorNetwork n)
    (v : Equiv.Perm (Fin (16 ^ d))) : ℕ → Fin (16 ^ d) → Fin (16 ^ d)
  | 0 => fun w => v w
  | t + 1 => (stageNet (wireSets F t) (nets t)).exec (X F nets v t)

section Exec

variable (F : FlowTableB d tf) (nets : ℕ → (b : KBag 16 d) → (n : ℕ) → ComparatorNetwork n)
  (v : Equiv.Perm (Fin (16 ^ d)))

theorem X_succ (t : ℕ) :
    X F nets v (t + 1) = (stageNet (wireSets F t) (nets t)).exec (X F nets v t) := rfl

theorem X_eq_comp_perm : ∀ t, ∃ ρ : Equiv.Perm (Fin (16 ^ d)), X F nets v t = v ∘ ρ
  | 0 => ⟨1, rfl⟩
  | t + 1 => by
    obtain ⟨ρ₁, h₁⟩ := X_eq_comp_perm t
    obtain ⟨ρ₂, h₂⟩ := ComparatorNetwork.exec_eq_comp_perm
      (stageNet (wireSets F t) (nets t)) (X F nets v t)
    exact ⟨ρ₁ * ρ₂, by rw [X_succ, h₂, h₁]; rfl⟩

theorem X_injective (t : ℕ) : Function.Injective (X F nets v t) := by
  obtain ⟨ρ, h⟩ := X_eq_comp_perm F nets v t
  exact h ▸ v.injective.comp ρ.injective

theorem X_surjective (t : ℕ) : Function.Surjective (X F nets v t) :=
  Finite.injective_iff_surjective.1 (X_injective F nets v t)

/-- The keys sitting on node `b`'s wires after `t` stages. -/
noncomputable def execPlacement (t : ℕ) (ht : t ≤ tf) : Placement 16 d where
  regs b := (wireSets F t b).image (X F nets v t)
  disjoint a b hab := by
    rw [Finset.disjoint_image (X_injective F nets v t)]
    exact wireSets_disjoint F ht a b hab
  complete i := by
    obtain ⟨w, rfl⟩ := X_surjective F nets v t i
    obtain ⟨b, hb⟩ := wireSets_complete F ht w
    exact ⟨b, Finset.mem_image_of_mem _ hb⟩

theorem execPlacement_card (t : ℕ) (ht : t ≤ tf) (b : KBag 16 d) :
    (((execPlacement F nets v t ht).regs b)).card = F.a t b := by
  show ((wireSets F t b).image (X F nets v t)).card = _
  rw [Finset.card_image_of_injective _ (X_injective F nets v t)]
  exact wireSets_card F ht b

/-- Keys that the parent's separator sent down to `b` (values after stage `t`). -/
noncomputable def fromParentK (t : ℕ) (b : KBag 16 d) : Finset (Fin (16 ^ d)) :=
  (downSetB (wireSets F t b.parent) (F.up t b.parent) (F.off t b.parent) (b.x % 16)).image
    (X F nets v (t + 1))

/-- Keys that the children's separators sent up to `b` (values after stage `t`). -/
noncomputable def fromChildrenK (t : ℕ) (b : KBag 16 d) : Finset (Fin (16 ^ d)) :=
  if h : b.l < d then
    Finset.univ.biUnion (fun j : Fin 16 =>
      (upSet (wireSets F t (b.child j.val j.isLt h)) (F.up t (b.child j.val j.isLt h))).image
        (X F nets v (t + 1)))
  else ∅

/-- E3a (nodes below the root). -/
theorem execPlacement_succ_regs (t : ℕ) (ht : t < tf) (b : KBag 16 d) (hb : 1 ≤ b.l) :
    (execPlacement F nets v (t + 1) ht).regs b =
      fromParentK F nets v t b ∪ fromChildrenK F nets v t b := by
  show (wireSets F (t + 1) b).image (X F nets v (t + 1)) = _
  rw [wireSets_succ_eq, Finset.image_union]
  unfold parentPart childPart fromParentK fromChildrenK
  rw [if_pos hb]
  congr 1
  split_ifs
  · exact Finset.biUnion_image
  · simp

theorem exists_orderEmb_eq {N : ℕ} {s : Finset (Fin N)} {w : Fin N} (hw : w ∈ s) :
    ∃ c : Fin s.card, s.orderEmbOfFin rfl c = w := by
  rw [← Set.mem_range, Finset.range_orderEmbOfFin]; exact hw

/-- The key on the `c`-th cell of node `q` after stage `t` is the output of the node network
on the node's input vector. -/
theorem X_succ_inside (t : ℕ) (ht : t < tf) (q : KBag 16 d) (c : Fin (wireSets F t q).card) :
    X F nets v (t + 1) ((wireSets F t q).orderEmbOfFin rfl c) =
      (nets t q (wireSets F t q).card).exec
        (fun i => X F nets v t ((wireSets F t q).orderEmbOfFin rfl i)) c := by
  rw [X_succ]
  exact stageNet_exec_inside (wireSets F t) (wireSets_disjoint F ht.le) (nets t)
    (X F nets v t) q c

/-- E4. -/
theorem stage_preserves_node_keys (t : ℕ) (ht : t < tf) (q : KBag 16 d) :
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
theorem fromChildrenK_subset (t : ℕ) (ht : t < tf) (b : KBag 16 d) (h : b.l < d) :
    fromChildrenK F nets v t b ⊆
      Finset.univ.biUnion (fun j : Fin 16 =>
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

theorem fromChildrenK_of_not_lt (t : ℕ) (b : KBag 16 d) (h : ¬ b.l < d) :
    fromChildrenK F nets v t b = ∅ := by
  unfold fromChildrenK; rw [dif_neg h]

end Exec

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

end Dict

section KeyDict

variable {d tf : ℕ} (F : FlowTableB d tf)
  (nets : ℕ → (b : KBag 16 d) → (n : ℕ) → ComparatorNetwork n)
  (v : Equiv.Perm (Fin (16 ^ d)))

/-- Keys sent down to child `j`: outputs of the node network on cells of the `j`-th middle block,
fed with the node's input vector. -/
theorem mem_image_downSet_iff (t : ℕ) (ht : t < tf) (q : KBag 16 d) (π : ℕ) (off : ℕ → ℕ) (j : ℕ)
    (k : Fin (16 ^ d)) :
    k ∈ (downSetB (wireSets F t q) π off j).image (X F nets v (t + 1)) ↔
      ∃ c : Fin (wireSets F t q).card, π / 2 + off j ≤ c.val ∧ c.val < π / 2 + off (j + 1) ∧
        k = (nets t q (wireSets F t q).card).exec
          (fun i => X F nets v t ((wireSets F t q).orderEmbOfFin rfl i)) c := by
  rw [Finset.mem_image]
  constructor
  · rintro ⟨w, hw, rfl⟩
    obtain ⟨c, h1, h2, rfl⟩ := mem_blockOf_iff.1 hw
    exact ⟨c, h1, h2, X_succ_inside F nets v t ht q c⟩
  · rintro ⟨c, h1, h2, rfl⟩
    exact ⟨_, mem_blockOf_iff.2 ⟨c, h1, h2, rfl⟩, X_succ_inside F nets v t ht q c⟩

end KeyDict


end R1T
