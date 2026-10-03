module

public import AKS.Paterson.ColdAllocation

/-! # Parallel comparison stages with cold storage

The local networks may differ between full and partial bags. Storage is
untouched, and the depth is the maximum local depth, not their sum.
-/

@[expose] public section

namespace Paterson.Bags.StoredPlacement

open Finset

def compare {k : ℕ} (pl : StoredPlacement k)
    (nets : (b : Bag k) → ComparatorNetwork (pl.regs b).card) : ComparatorNetwork (2 ^ k) :=
  ⟨(allBags k).flatMap fun b ↦
    ((nets b).scatterEmbed (2 ^ k) ((pl.regs b).orderEmbOfFin rfl)).comparators⟩

theorem scatter_wire_mem {k : ℕ} (pl : StoredPlacement k)
    (nets : (b : Bag k) → ComparatorNetwork (pl.regs b).card) (b : Bag k)
    (c : Comparator (2 ^ k))
    (hc : c ∈ ((nets b).scatterEmbed (2 ^ k) ((pl.regs b).orderEmbOfFin rfl)).comparators) :
    c.i ∈ pl.regs b ∧ c.j ∈ pl.regs b := by
  obtain ⟨d, _, rfl⟩ := List.mem_map.mp hc
  exact ⟨orderEmbOfFin_mem _ rfl d.i, orderEmbOfFin_mem _ rfl d.j⟩

theorem compare_depth_le {k : ℕ} (pl : StoredPlacement k)
    (nets : (b : Bag k) → ComparatorNetwork (pl.regs b).card) (depth : ℕ)
    (hd : ∀ b, (nets b).depth ≤ depth) : (pl.compare nets).depth ≤ depth := by
  apply depth_flatMap_disjoint
  · intro b _
    exact (depth_scatterEmbed_le _ _ _).trans (hd b)
  · apply allBags_nodup.pairwise_of_forall_ne
    intro a _ b _ hab c hc d hd
    obtain ⟨hi, hj⟩ := pl.scatter_wire_mem nets a c hc
    obtain ⟨hi', hj'⟩ := pl.scatter_wire_mem nets b d hd
    have h := disjoint_left.mp (pl.disjoint a b hab)
    exact ⟨⟨fun heq ↦ h hi (heq ▸ hi'), fun heq ↦ h hi (heq ▸ hj')⟩,
      ⟨fun heq ↦ h hj (heq ▸ hi'), fun heq ↦ h hj (heq ▸ hj')⟩⟩

theorem compare_local {k : ℕ} (pl : StoredPlacement k)
    (nets : (b : Bag k) → ComparatorNetwork (pl.regs b).card) (b : Bag k)
    (c : Comparator (2 ^ k)) (hc : c ∈ (pl.compare nets).comparators) :
    (c.i ∈ pl.regs b ∧ c.j ∈ pl.regs b) ∨
      (c.i ∉ pl.regs b ∧ c.j ∉ pl.regs b) := by
  obtain ⟨a, _, ha⟩ := List.mem_flatMap.mp hc
  obtain ⟨hi, hj⟩ := pl.scatter_wire_mem nets a c ha
  by_cases hab : a = b
  · subst a
    exact Or.inl ⟨hi, hj⟩
  · have h := disjoint_left.mp (pl.disjoint a b hab)
    exact Or.inr ⟨fun h' ↦ h hi h', fun h' ↦ h hj h'⟩

theorem compare_cold_exec {k ambient : ℕ} (pl : StoredPlacement k)
    (nets : (b : Bag k) → ComparatorNetwork (pl.regs b).card)
    (w : Fin (2 ^ k) → Fin ambient) {i} (hi : i ∈ pl.cold) :
    (pl.compare nets).exec w i = w i := by
  apply foldl_comparators_outside
  intro c hc
  obtain ⟨a, _, ha⟩ := List.mem_flatMap.mp hc
  obtain ⟨hi', hj'⟩ := pl.scatter_wire_mem nets a c ha
  have h := disjoint_left.mp (pl.cold_disjoint a)
  exact ⟨fun heq ↦ h hi (heq ▸ hi'), fun heq ↦ h hi (heq ▸ hj')⟩

theorem compare_exec_view {k : ℕ} (pl : StoredPlacement k)
    (nets : (b : Bag k) → ComparatorNetwork (pl.regs b).card) (b : Bag k)
    (w : Fin (2 ^ k) → Fin (2 ^ k)) (i : Fin (pl.regs b).card) :
    (pl.compare nets).exec w ((pl.regs b).orderEmbOfFin rfl i) =
      (nets b).exec
        (w ∘ (pl.regs b).orderEmbOfFin rfl) i := by
  let regs := pl.regs b
  let emb := regs.orderEmbOfFin rfl
  let r := emb i
  have hr : r ∈ regs := orderEmbOfFin_mem regs rfl i
  have hout : ∀ a : Bag k, a ≠ b → ∀ s ∈ regs,
      ∀ c ∈ ((nets a).scatterEmbed (2 ^ k) ((pl.regs a).orderEmbOfFin rfl)).comparators, s ≠ c.i ∧ s ≠ c.j := by
    intro a hab s hs c hc
    obtain ⟨hi, hj⟩ := pl.scatter_wire_mem nets a c hc
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
    ((nets a).scatterEmbed (2 ^ k) ((pl.regs a).orderEmbOfFin rfl)).comparators⟩ : ComparatorNetwork (2 ^ k)).exec w r = _
  rw [ComparatorNetwork.exec_flatMap, hlist, List.foldl_append, List.foldl_cons]
  have hbefore_eq : ∀ s ∈ regs,
      before.foldl (fun v a ↦ ((nets a).scatterEmbed (2 ^ k) ((pl.regs a).orderEmbOfFin rfl)).exec v) w s = w s :=
    ComparatorNetwork.foldl_exec_outside_set before (fun a ↦ (nets a).scatterEmbed (2 ^ k) ((pl.regs a).orderEmbOfFin rfl))
      w regs (fun a ha s hs c hc ↦ hout a (hbefore a ha) s hs c hc)
  rw [ComparatorNetwork.foldl_exec_outside after (fun a ↦ (nets a).scatterEmbed (2 ^ k) ((pl.regs a).orderEmbOfFin rfl))
    _ r (fun a ha c hc ↦ hout a (hafter a ha) r hr c hc)]
  change ((nets b).scatterEmbed (2 ^ k) emb).exec _ (emb i) = _
  rw [ComparatorNetwork.scatterEmbed_exec_inside]
  congr 1
  funext s
  exact hbefore_eq (emb s) (orderEmbOfFin_mem regs rfl s)

end Paterson.Bags.StoredPlacement
