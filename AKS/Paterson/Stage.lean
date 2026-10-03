module

public import AKS.Paterson.BagSeparator

/-! # A concrete parallel Paterson bag transition

The network and register reassignment are defined independently of the
unfinished cold-storage schedule. Every local separator acts on the actual
registers of its bag; all these disjoint networks have depth at most 989.
-/

@[expose] public section

namespace Paterson.Bags

open Finset

noncomputable def parallel {k : ℕ} (pl : Placement k) : ComparatorNetwork (2 ^ k) :=
  ⟨(allBags k).flatMap fun b ↦ (bagSeparator (pl.regs b)).comparators⟩

theorem bagSeparator_wire_mem {k : ℕ} (regs : Finset (Fin (2 ^ k)))
    (c : Comparator (2 ^ k)) (hc : c ∈ (bagSeparator regs).comparators) :
    c.i ∈ regs ∧ c.j ∈ regs := by
  obtain ⟨d, _, rfl⟩ := List.mem_map.mp hc
  exact ⟨orderEmbOfFin_mem regs rfl d.i, orderEmbOfFin_mem regs rfl d.j⟩

theorem parallel_depth_le {k : ℕ} (pl : Placement k) : (parallel pl).depth ≤ 989 := by
  apply depth_flatMap_disjoint
  · intro b _
    exact bagSeparator_depth_le _
  · apply allBags_nodup.pairwise_of_forall_ne
    intro a _ b _ hab c hc d hd
    obtain ⟨hi, hj⟩ := bagSeparator_wire_mem _ c hc
    obtain ⟨hi', hj'⟩ := bagSeparator_wire_mem _ d hd
    have h := disjoint_left.mp (pl.disjoint a b hab)
    exact ⟨⟨fun heq ↦ h hi (heq ▸ hi'), fun heq ↦ h hi (heq ▸ hj')⟩,
      ⟨fun heq ↦ h hj (heq ▸ hi'), fun heq ↦ h hj (heq ▸ hj')⟩⟩

theorem parallel_local {k : ℕ} (pl : Placement k) (b : Bag k)
    (c : Comparator (2 ^ k)) (hc : c ∈ (parallel pl).comparators) :
    (c.i ∈ pl.regs b ∧ c.j ∈ pl.regs b) ∨
      (c.i ∉ pl.regs b ∧ c.j ∉ pl.regs b) := by
  obtain ⟨a, _, ha⟩ := List.mem_flatMap.mp hc
  obtain ⟨hi, hj⟩ := bagSeparator_wire_mem _ c ha
  by_cases hab : a = b
  · subst a
    exact Or.inl ⟨hi, hj⟩
  · have h := disjoint_left.mp (pl.disjoint a b hab)
    exact Or.inr ⟨fun h' ↦ h hi h', fun h' ↦ h hj h'⟩

/-- Each bag's view of the parallel network is exactly its local separator. -/
theorem parallel_exec_view {k : ℕ} (pl : Placement k) (b : Bag k)
    (w : Fin (2 ^ k) → Fin (2 ^ k)) (i : Fin (pl.regs b).card) :
    (parallel pl).exec w ((pl.regs b).orderEmbOfFin rfl i) =
      (separatorNetwork (pl.regs b).card).exec
        (w ∘ (pl.regs b).orderEmbOfFin rfl) i := by
  let regs := pl.regs b
  let emb := regs.orderEmbOfFin rfl
  let r := emb i
  have hr : r ∈ regs := orderEmbOfFin_mem regs rfl i
  have hout : ∀ a : Bag k, a ≠ b → ∀ s ∈ regs,
      ∀ c ∈ (bagSeparator (pl.regs a)).comparators, s ≠ c.i ∧ s ≠ c.j := by
    intro a hab s hs c hc
    obtain ⟨hi, hj⟩ := bagSeparator_wire_mem _ c hc
    have h := disjoint_left.mp (pl.disjoint b a hab.symm)
    exact ⟨fun heq ↦ h hs (heq ▸ hi), fun heq ↦ h hs (heq ▸ hj)⟩
  obtain ⟨before, after, hlist⟩ := List.append_of_mem b.mem_allBags
  have hnd := allBags_nodup (k := k)
  rw [hlist, List.nodup_append] at hnd
  obtain ⟨_, hnd', hne⟩ := hnd
  have hbefore : ∀ a ∈ before, a ≠ b :=
    fun a ha ↦ hne a ha b List.mem_cons_self
  have hafter : ∀ a ∈ after, a ≠ b := by
    intro a ha heq
    subst a
    exact (List.nodup_cons.mp hnd').1 ha
  change (⟨(allBags k).flatMap fun a ↦
    (bagSeparator (pl.regs a)).comparators⟩ : ComparatorNetwork (2 ^ k)).exec w r = _
  rw [ComparatorNetwork.exec_flatMap, hlist, List.foldl_append, List.foldl_cons]
  have hbefore_eq : ∀ s ∈ regs,
      before.foldl (fun v a ↦ (bagSeparator (pl.regs a)).exec v) w s = w s :=
    ComparatorNetwork.foldl_exec_outside_set before (fun a ↦ bagSeparator (pl.regs a))
      w regs (fun a ha s hs c hc ↦ hout a (hbefore a ha) s hs c hc)
  rw [ComparatorNetwork.foldl_exec_outside after (fun a ↦ bagSeparator (pl.regs a))
    _ r (fun a ha c hc ↦ hout a (hafter a ha) r hr c hc)]
  change ((separatorNetwork regs.card).scatterEmbed (2 ^ k) emb).exec _ (emb i) = _
  rw [ComparatorNetwork.scatterEmbed_exec_inside]
  congr 1
  funext s
  exact hbefore_eq (emb s) (orderEmbOfFin_mem regs rfl s)

/-- Routing is an actual register partition, for any supplied fringe schedule
that sends no middle registers below the leaves. -/
def route {k : ℕ} (pl : Placement k) (f : Bag k → ℕ)
    (hleaf : ∀ b : Bag k, ¬ b.l < k → (pl.regs b).card / 2 ≤ f b) : Placement k :=
  let parts := fun b ↦ split (pl.regs b) (f b)
  ⟨stageRegs parts,
    stageRegs_disjoint pl parts
      (fun _ ↦ split_toParent_subset _ _)
      (fun _ ↦ split_toLeft_subset _ _)
      (fun _ ↦ split_toRight_subset _ _)
      (fun _ ↦ split_toParent_toLeft_disjoint _ _)
      (fun _ ↦ split_toParent_toRight_disjoint _ _)
      (fun _ ↦ split_toLeft_toRight_disjoint _ _),
    stageRegs_complete pl parts
      (fun _ _ hi ↦ split_covers _ _ hi)
      (fun b hb ↦ split_leaf _ _ (hleaf b hb))⟩

/-- No old-stranger filtering hypothesis is needed for a full lattice bag:
it follows from its support bound and the concrete parallel execution. -/
theorem parallel_filters {k : ℕ} (pl : Placement k) (b : Bag k)
    (hdvd : 32 ∣ (pl.regs b).card) (f : ℕ)
    (hf : (pl.regs b).card / 32 ≤ f) (hhalf : f ≤ (pl.regs b).card / 2)
    (w : Fin (2 ^ k) → Fin (2 ^ k)) (hw : Function.Injective w)
    (j : ℕ) (hj : 1 ≤ j)
    (hs : (b.strangers j w (pl.regs b) : ℝ) ≤
      (patersonMu : ℝ) * (pl.regs b).card) :
    (b.strangers j ((parallel pl).exec w)
      ((split (pl.regs b) f).toLeft ∪ (split (pl.regs b) f).toRight) : ℝ) ≤
      (patersonTailError : ℝ) * b.strangers j w (pl.regs b) :=
  bagSeparator_filters _ hdvd f hf hhalf w _ hw (parallel_exec_view pl b w) b j hj hs

end Paterson.Bags
