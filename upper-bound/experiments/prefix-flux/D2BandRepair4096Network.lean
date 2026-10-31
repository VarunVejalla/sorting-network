import D2Slope35Physical4096
import D2TwoGridPhysicalBand
import AKS.Chvatal.StageNet
import AKS.Chvatal.ExecPlacement
import AKS.Chvatal.SortedColumnDecode

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000

namespace Chvatal.D2BandRepair4096Network

open Chvatal.D2Slope35Physical4096
open Chvatal.D2TwoGridPhysicalBand
open Chvatal.D2TwoGridBandInterface

abbrev Col := Fin 64
abbrev Row := Fin 4096
abbrev Wire := Fin (4096 * 64)

private def alignedRow (b i : Fin 64) : Row :=
  ⟨64 * b.val + i.val, by have := b.isLt; have := i.isLt; omega⟩

private def shiftedRow (b : Fin 63) (i : Fin 64) : Row :=
  ⟨32 + 64 * b.val + i.val, by have := b.isLt; have := i.isLt; omega⟩

private def alignedSegment (b c : Fin 64) : Fin 64 ↪o Wire :=
  OrderEmbedding.ofStrictMono
    (fun i => matrixWire 4096 64 (alignedRow b i) c)
    (by
      intro i j hij
      apply (matrixWire_row_lt_iff (by omega) c).2
      change 64 * b.val + i.val < 64 * b.val + j.val
      omega)

private def shiftedSegment (b : Fin 63) (c : Fin 64) : Fin 64 ↪o Wire :=
  OrderEmbedding.ofStrictMono
    (fun i => matrixWire 4096 64 (shiftedRow b i) c)
    (by
      intro i j hij
      apply (matrixWire_row_lt_iff (by omega) c).2
      change 32 + 64 * b.val + i.val < 32 + 64 * b.val + j.val
      omega)

private theorem row_eq_alignedRow (r : Row) :
    ∃ b i : Fin 64, alignedRow b i = r := by
  let b : Fin 64 := ⟨r.val / 64, by have := r.isLt; omega⟩
  let i : Fin 64 := ⟨r.val % 64, Nat.mod_lt _ (by omega)⟩
  refine ⟨b, i, ?_⟩
  apply Fin.ext
  have hdiv := Nat.div_add_mod r.val 64
  change 64 * b.val + i.val = r.val
  dsimp [b, i]
  omega

private theorem row_eq_shiftedRow (r : Row) (hrlo : 32 ≤ r.val)
    (hrhi : r.val < 4064) : ∃ b : Fin 63, ∃ i : Fin 64, shiftedRow b i = r := by
  let q := r.val - 32
  let b : Fin 63 := ⟨q / 64, by dsimp [q]; omega⟩
  let i : Fin 64 := ⟨q % 64, Nat.mod_lt _ (by omega)⟩
  refine ⟨b, i, ?_⟩
  apply Fin.ext
  have hdiv := Nat.div_add_mod q 64
  change 32 + 64 * b.val + i.val = r.val
  dsimp [b, i, q]
  omega

private theorem matrixWire_eq_alignedSegment (r : Row) (c : Col)
    (b i : Fin 64) (h : alignedRow b i = r) :
    matrixWire 4096 64 r c = alignedSegment b c i := by
  change matrixWire 4096 64 r c = matrixWire 4096 64 (alignedRow b i) c
  rw [h]

private theorem matrixWire_eq_shiftedSegment (r : Row) (c : Col)
    (b : Fin 63) (i : Fin 64) (h : shiftedRow b i = r) :
    matrixWire 4096 64 r c = shiftedSegment b c i := by
  change matrixWire 4096 64 r c = matrixWire 4096 64 (shiftedRow b i) c
  rw [h]

private def alignedSegmentNet (b c : Fin 64) : ComparatorNetwork (4096 * 64) :=
  (bitonicNetwork 64).scatterEmbed (4096 * 64) (alignedSegment b c)

private def shiftedSegmentNet (b : Fin 63) (c : Fin 64) : ComparatorNetwork (4096 * 64) :=
  (bitonicNetwork 64).scatterEmbed (4096 * 64) (shiftedSegment b c)

private noncomputable def alignedChunks : List (Fin 64 × Fin 64) :=
  (Finset.univ : Finset (Fin 64 × Fin 64)).toList

private noncomputable def shiftedChunks : List (Fin 63 × Fin 64) :=
  (Finset.univ : Finset (Fin 63 × Fin 64)).toList

noncomputable def alignedGrid : ComparatorNetwork (4096 * 64) :=
  ⟨alignedChunks.flatMap fun p => (alignedSegmentNet p.1 p.2).comparators⟩

noncomputable def shiftedGrid : ComparatorNetwork (4096 * 64) :=
  ⟨shiftedChunks.flatMap fun p => (shiftedSegmentNet p.1 p.2).comparators⟩

noncomputable def twoGridRepair : ComparatorNetwork (4096 * 64) := alignedGrid.append shiftedGrid

theorem twoGridRepair_exec {α : Type*} [LinearOrder α] (v : Wire → α) :
    twoGridRepair.exec v = shiftedGrid.exec (alignedGrid.exec v) := by
  rw [twoGridRepair]
  unfold ComparatorNetwork.append
  exact ComparatorNetwork.exec_append alignedGrid shiftedGrid v

private theorem falseCount_preserved {n : Nat} (net : ComparatorNetwork n)
    (v : Fin n → Bool) :
    (Finset.univ.filter fun i : Fin n => net.exec v i = false).card =
      (Finset.univ.filter fun i : Fin n => v i = false).card := by
  obtain ⟨ρ, hρ⟩ := ComparatorNetwork.exec_eq_comp_perm net v
  refine Finset.card_bij (fun i _ => ρ i) ?_ ?_ ?_
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    have hpoint : net.exec v i = v (ρ i) := by
      simpa [Function.comp] using congrFun hρ i
    rw [← hpoint]
    exact hi
  · intro i hi j hj heq
    exact ρ.injective heq
  · intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
    refine ⟨ρ.symm j, ?_, by simp⟩
    rw [hρ, Function.comp_apply, Equiv.apply_symm_apply]
    exact hj

theorem comparatorNetwork_falseCount_preserved {n : Nat}
    (net : ComparatorNetwork n) (v : Fin n -> Bool) :
    (Finset.univ.filter fun i : Fin n => net.exec v i = false).card =
      (Finset.univ.filter fun i : Fin n => v i = false).card :=
  falseCount_preserved net v

private theorem sorted_false_prefix (s : Fin 64 → Bool) (hs : Monotone s)
    (hcount : 32 ≤ (Finset.univ.filter fun i : Fin 64 => s i = false).card)
    (i : Fin 64) (hi : i.val < 32) : s i = false := by
  by_contra hnot
  have htrue : s i = true := by cases h : s i <;> simp_all
  have hsub : (Finset.univ.filter fun j : Fin 64 => s j = false) ⊆ Finset.Iio i := by
    intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
    simp only [Finset.mem_Iio]
    by_contra hji
    have hij : i ≤ j := le_of_not_gt hji
    have hmono := hs hij
    rw [htrue] at hmono
    cases hsj : s j
    · have hbad : ¬ (true ≤ false) := by decide
      rw [hsj] at hmono
      exact hbad hmono
    · simp [hsj] at hj
  have hcard := Finset.card_le_card hsub
  have hIio : (Finset.Iio i).card = i.val := by simp
  omega

private theorem sorted_true_suffix (s : Fin 64 → Bool) (hs : Monotone s)
    (hcount : (Finset.univ.filter fun i : Fin 64 => s i = false).card ≤ 32)
    (i : Fin 64) (hi : 32 ≤ i.val) : s i = true := by
  by_contra hnot
  have hfalse : s i = false := by cases h : s i <;> simp_all
  have hsub : Finset.Iic i ⊆ Finset.univ.filter fun j : Fin 64 => s j = false := by
    intro j hj
    simp only [Finset.mem_Iic] at hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    have hmono := hs hj
    rw [hfalse] at hmono
    cases hsj : s j
    · rfl
    · have hbad : ¬ (true ≤ false) := by decide
      rw [hsj] at hmono
      exact False.elim (hbad hmono)
  have hcard := Finset.card_le_card hsub
  have hIic : (Finset.Iic i).card = i.val + 1 := by simp
  omega

private theorem aligned_disjoint (p q : Fin 64 × Fin 64) (hpq : p ≠ q)
    (c₁ : Comparator (4096 * 64)) (hc₁ : c₁ ∈ (alignedSegmentNet p.1 p.2).comparators)
    (c₂ : Comparator (4096 * 64)) (hc₂ : c₂ ∈ (alignedSegmentNet q.1 q.2).comparators) :
    (c₁.i ≠ c₂.i ∧ c₁.i ≠ c₂.j) ∧ (c₁.j ≠ c₂.i ∧ c₁.j ≠ c₂.j) := by
  simp only [alignedSegmentNet, ComparatorNetwork.scatterEmbed, List.mem_map] at hc₁ hc₂
  obtain ⟨a, _, rfl⟩ := hc₁
  obtain ⟨d, _, rfl⟩ := hc₂
  have hcoords (i j : Fin 64) (he : alignedSegment p.1 p.2 i = alignedSegment q.1 q.2 j) :
      p.1 = q.1 ∧ p.2 = q.2 := by
    have hmc := matrixWire_injective (by omega) he
    have hrow : alignedRow p.1 i = alignedRow q.1 j := hmc.1
    have hcol : p.2 = q.2 := hmc.2
    have hblock : p.1 = q.1 := by
      apply Fin.ext
      have hr := congrArg Fin.val hrow
      simp only [alignedRow] at hr
      change 64 * p.1.val + i.val = 64 * q.1.val + j.val at hr
      omega
    exact ⟨hblock, hcol⟩
  have hne (i j : Fin 64) : alignedSegment p.1 p.2 i ≠ alignedSegment q.1 q.2 j := by
    intro he
    exact hpq (Prod.ext (hcoords i j he).1 (hcoords i j he).2)
  exact ⟨⟨fun h => hne a.i d.i h, fun h => hne a.i d.j h⟩,
    ⟨fun h => hne a.j d.i h, fun h => hne a.j d.j h⟩⟩

private theorem shifted_disjoint (p q : Fin 63 × Fin 64) (hpq : p ≠ q)
    (c₁ : Comparator (4096 * 64)) (hc₁ : c₁ ∈ (shiftedSegmentNet p.1 p.2).comparators)
    (c₂ : Comparator (4096 * 64)) (hc₂ : c₂ ∈ (shiftedSegmentNet q.1 q.2).comparators) :
    (c₁.i ≠ c₂.i ∧ c₁.i ≠ c₂.j) ∧ (c₁.j ≠ c₂.i ∧ c₁.j ≠ c₂.j) := by
  simp only [shiftedSegmentNet, ComparatorNetwork.scatterEmbed, List.mem_map] at hc₁ hc₂
  obtain ⟨a, _, rfl⟩ := hc₁
  obtain ⟨d, _, rfl⟩ := hc₂
  have hcoords (i j : Fin 64) (he : shiftedSegment p.1 p.2 i = shiftedSegment q.1 q.2 j) :
      p.1 = q.1 ∧ p.2 = q.2 := by
    have hmc := matrixWire_injective (by omega) he
    have hrow : shiftedRow p.1 i = shiftedRow q.1 j := hmc.1
    have hcol : p.2 = q.2 := hmc.2
    have hblock : p.1 = q.1 := by
      apply Fin.ext
      have hr := congrArg Fin.val hrow
      simp only [shiftedRow] at hr
      change 32 + 64 * p.1.val + i.val = 32 + 64 * q.1.val + j.val at hr
      omega
    exact ⟨hblock, hcol⟩
  have hne (i j : Fin 64) : shiftedSegment p.1 p.2 i ≠ shiftedSegment q.1 q.2 j := by
    intro he
    exact hpq (Prod.ext (hcoords i j he).1 (hcoords i j he).2)
  exact ⟨⟨fun h => hne a.i d.i h, fun h => hne a.i d.j h⟩,
    ⟨fun h => hne a.j d.i h, fun h => hne a.j d.j h⟩⟩

private theorem aligned_segments_separated (p q : Fin 64 × Fin 64) (hpq : p ≠ q)
    (i j : Fin 64) : alignedSegment p.1 p.2 i ≠ alignedSegment q.1 q.2 j := by
  intro he
  have hmc := matrixWire_injective (by omega) he
  have hrow : alignedRow p.1 i = alignedRow q.1 j := hmc.1
  have hcol : p.2 = q.2 := hmc.2
  have hblock : p.1 = q.1 := by
    apply Fin.ext
    have hr := congrArg Fin.val hrow
    simp only [alignedRow] at hr
    change 64 * p.1.val + i.val = 64 * q.1.val + j.val at hr
    omega
  exact hpq (Prod.ext hblock hcol)

private theorem shifted_segments_separated (p q : Fin 63 × Fin 64) (hpq : p ≠ q)
    (i j : Fin 64) : shiftedSegment p.1 p.2 i ≠ shiftedSegment q.1 q.2 j := by
  intro he
  have hmc := matrixWire_injective (by omega) he
  have hrow : shiftedRow p.1 i = shiftedRow q.1 j := hmc.1
  have hcol : p.2 = q.2 := hmc.2
  have hblock : p.1 = q.1 := by
    apply Fin.ext
    have hr := congrArg Fin.val hrow
    simp only [shiftedRow] at hr
    change 32 + 64 * p.1.val + i.val = 32 + 64 * q.1.val + j.val at hr
    omega
  exact hpq (Prod.ext hblock hcol)

private theorem shiftedGrid_comparator_row_bounds (cmp : Comparator (4096 * 64))
    (hc : cmp ∈ shiftedGrid.comparators) :
    32 ≤ (matrixRow 4096 64 (by omega) cmp.i).val ∧
      (matrixRow 4096 64 (by omega) cmp.i).val < 4064 ∧
    32 ≤ (matrixRow 4096 64 (by omega) cmp.j).val ∧
      (matrixRow 4096 64 (by omega) cmp.j).val < 4064 := by
  simp only [shiftedGrid, List.mem_flatMap] at hc
  rcases hc with ⟨p, hp, hcmp⟩
  simp only [shiftedSegmentNet, ComparatorNetwork.scatterEmbed, List.mem_map] at hcmp
  rcases hcmp with ⟨cc, hcc, rfl⟩
  have hirow : matrixRow 4096 64 (by omega)
      (shiftedSegment p.1 p.2 cc.i) = shiftedRow p.1 cc.i := by
    simp [shiftedSegment, matrixWire_row_col]
  have hjrow : matrixRow 4096 64 (by omega)
      (shiftedSegment p.1 p.2 cc.j) = shiftedRow p.1 cc.j := by
    simp [shiftedSegment, matrixWire_row_col]
  constructor
  · rw [hirow]
    simp [shiftedRow]
    omega
  constructor
  · rw [hirow]
    simp [shiftedRow]
    have := p.1.isLt
    have := cc.i.isLt
    omega
  constructor
  · rw [hjrow]
    simp [shiftedRow]
    omega
  · rw [hjrow]
    simp [shiftedRow]
    have := p.1.isLt
    have := cc.j.isLt
    omega

theorem shiftedGrid_exec_edge_unchanged {α : Type*} [LinearOrder α]
    (v : Wire → α) (r : Row) (c : Col)
    (hedge : r.val < 32 ∨ 4064 ≤ r.val) :
    shiftedGrid.exec v (matrixWire 4096 64 r c) = v (matrixWire 4096 64 r c) := by
  unfold shiftedGrid ComparatorNetwork.exec
  apply foldl_comparators_outside
  intro cmp hcmp
  have hrows := shiftedGrid_comparator_row_bounds cmp hcmp
  constructor
  · intro heq
    have heqrow := congrArg (fun w =>
      (matrixRow 4096 64 (by omega) w).val) heq
    change (matrixRow 4096 64 (by omega) (matrixWire 4096 64 r c)).val =
      (matrixRow 4096 64 (by omega) cmp.i).val at heqrow
    have hwire : (matrixRow 4096 64 (by omega) (matrixWire 4096 64 r c)).val = r.val := by
      rw [(matrixWire_row_col (by omega) r c).1]
    rw [hwire] at heqrow
    rcases hedge with hlow | hhigh
    · omega
    · omega
  · intro heq
    have heqrow := congrArg (fun w =>
      (matrixRow 4096 64 (by omega) w).val) heq
    change (matrixRow 4096 64 (by omega) (matrixWire 4096 64 r c)).val =
      (matrixRow 4096 64 (by omega) cmp.j).val at heqrow
    have hwire : (matrixRow 4096 64 (by omega) (matrixWire 4096 64 r c)).val = r.val := by
      rw [(matrixWire_row_col (by omega) r c).1]
    rw [hwire] at heqrow
    rcases hedge with hlow | hhigh
    · omega
    · omega

/-- The first grid's action on any one aligned segment is exactly the
embedded 64-wire bitonic sort. -/
theorem alignedGrid_exec_segment {α : Type*} [LinearOrder α]
    (v : Wire → α) (b c i : Fin 64) :
    alignedGrid.exec v (alignedSegment b c i) =
      (bitonicNetwork 64).exec (v ∘ alignedSegment b c) i := by
  have hflat := ComparatorNetwork.exec_flatMap alignedChunks
    (fun p => alignedSegmentNet p.1 p.2) v
  change alignedGrid.exec v =
    alignedChunks.foldl (fun v' p => (alignedSegmentNet p.1 p.2).exec v') v at hflat
  rw [hflat]
  have hact := flatMap_scatter_exec_inside
    (m := fun _ : Fin 64 × Fin 64 => 64)
    (fun p => alignedSegment p.1 p.2)
    (fun _ => bitonicNetwork 64)
    alignedChunks v (Finset.nodup_toList _) (by
      intro p hp q hq hpq i' j'
      exact aligned_segments_separated p q hpq i' j')
    (b, c) (Finset.mem_toList.mpr (Finset.mem_univ _)) i
  simpa [alignedSegmentNet] using hact

/-- The shifted grid's action on any one segment is exactly the embedded
64-wire bitonic sort. -/
theorem shiftedGrid_exec_segment {α : Type*} [LinearOrder α]
    (v : Wire → α) (b : Fin 63) (c i : Fin 64) :
    shiftedGrid.exec v (shiftedSegment b c i) =
      (bitonicNetwork 64).exec (v ∘ shiftedSegment b c) i := by
  have hflat := ComparatorNetwork.exec_flatMap shiftedChunks
    (fun p => shiftedSegmentNet p.1 p.2) v
  change shiftedGrid.exec v =
    shiftedChunks.foldl (fun v' p => (shiftedSegmentNet p.1 p.2).exec v') v at hflat
  rw [hflat]
  have hact := flatMap_scatter_exec_inside
    (m := fun _ : Fin 63 × Fin 64 => 64)
    (fun p => shiftedSegment p.1 p.2)
    (fun _ => bitonicNetwork 64)
    shiftedChunks v (Finset.nodup_toList _) (by
      intro p hp q hq hpq i' j'
      exact shifted_segments_separated p q hpq i' j')
    (b, c) (Finset.mem_toList.mpr (Finset.mem_univ _)) i
  simpa [shiftedSegmentNet] using hact

theorem shiftedGrid_column_eq_of_monotone {α : Type*} [LinearOrder α]
    (v : Wire → α) (c : Col)
    (hmono : Monotone (fun r : Row => v (matrixWire 4096 64 r c)))
    (r : Row) :
    shiftedGrid.exec v (matrixWire 4096 64 r c) = v (matrixWire 4096 64 r c) := by
  by_cases hedge : r.val < 32 ∨ 4064 ≤ r.val
  · exact shiftedGrid_exec_edge_unchanged v r c hedge
  · have hrlo : 32 ≤ r.val := by omega
    have hrhi : r.val < 4064 := by omega
    obtain ⟨b, i, hrow⟩ := row_eq_shiftedRow r hrlo hrhi
    have hlocal : Monotone (v ∘ shiftedSegment b c) := by
      intro x y hxy
      apply hmono
      apply Fin.le_iff_val_le_val.mpr
      simp [shiftedRow]
      exact Fin.le_iff_val_le_val.mp hxy
    have hfix := ComparatorNetwork.exec_eq_of_monotone (bitonicNetwork 64) hlocal
    rw [matrixWire_eq_shiftedSegment r c b i hrow, shiftedGrid_exec_segment, hfix]
    change v (shiftedSegment b c i) = v (shiftedSegment b c i)
    rfl

theorem alignedGrid_falseCount_segment (v : Wire → Bool) (b c : Fin 64) :
    (Finset.univ.filter fun i : Fin 64 =>
      alignedGrid.exec v (alignedSegment b c i) = false).card =
    (Finset.univ.filter fun i : Fin 64 =>
      v (alignedSegment b c i) = false).card := by
  simp_rw [alignedGrid_exec_segment]
  exact falseCount_preserved (bitonicNetwork 64) (v ∘ alignedSegment b c)

theorem shiftedGrid_falseCount_segment (v : Wire → Bool) (b : Fin 63) (c : Fin 64) :
    (Finset.univ.filter fun i : Fin 64 =>
      shiftedGrid.exec v (shiftedSegment b c i) = false).card =
    (Finset.univ.filter fun i : Fin 64 =>
      v (shiftedSegment b c i) = false).card := by
  simp_rw [shiftedGrid_exec_segment]
  exact falseCount_preserved (bitonicNetwork 64) (v ∘ shiftedSegment b c)

theorem alignedSegment_const (v : Wire → Bool) (b c : Fin 64) (value : Bool)
    (hin : ∀ i : Fin 64, v (alignedSegment b c i) = value) (i : Fin 64) :
    alignedGrid.exec v (alignedSegment b c i) = value := by
  have hmono : Monotone (v ∘ alignedSegment b c) := by
    intro x y hxy
    change v (alignedSegment b c x) ≤ v (alignedSegment b c y)
    rw [hin x, hin y]
  have hfix := ComparatorNetwork.exec_eq_of_monotone (bitonicNetwork 64) hmono
  rw [alignedGrid_exec_segment, hfix]
  exact hin i

theorem shiftedSegment_const (v : Wire → Bool) (b : Fin 63) (c : Fin 64)
    (value : Bool) (hin : ∀ i : Fin 64, v (shiftedSegment b c i) = value) (i : Fin 64) :
    shiftedGrid.exec v (shiftedSegment b c i) = value := by
  have hmono : Monotone (v ∘ shiftedSegment b c) := by
    intro x y hxy
    change v (shiftedSegment b c x) ≤ v (shiftedSegment b c y)
    rw [hin x, hin y]
  have hfix := ComparatorNetwork.exec_eq_of_monotone (bitonicNetwork 64) hmono
  rw [shiftedGrid_exec_segment, hfix]
  exact hin i

theorem alignedGrid_sorts_each_segment {α : Type*} [LinearOrder α]
    (v : Wire → α) (b c : Fin 64) (i j : Fin 64) (hij : i ≤ j) :
    alignedGrid.exec v (alignedSegment b c i) ≤
      alignedGrid.exec v (alignedSegment b c j) := by
  have hflat := ComparatorNetwork.exec_flatMap alignedChunks
    (fun p => alignedSegmentNet p.1 p.2) v
  change alignedGrid.exec v =
    alignedChunks.foldl (fun v' p => (alignedSegmentNet p.1 p.2).exec v') v at hflat
  rw [hflat]
  have hact_i := flatMap_scatter_exec_inside
    (m := fun _ : Fin 64 × Fin 64 => 64)
    (fun p => alignedSegment p.1 p.2)
    (fun _ => bitonicNetwork 64)
    alignedChunks v (Finset.nodup_toList _) (by
      intro p hp q hq hpq i' j'
      exact aligned_segments_separated p q hpq i' j')
    (b, c) (Finset.mem_toList.mpr (Finset.mem_univ _)) i
  have hact_j := flatMap_scatter_exec_inside
    (m := fun _ : Fin 64 × Fin 64 => 64)
    (fun p => alignedSegment p.1 p.2)
    (fun _ => bitonicNetwork 64)
    alignedChunks v (Finset.nodup_toList _) (by
      intro p hp q hq hpq i' j'
      exact aligned_segments_separated p q hpq i' j')
    (b, c) (Finset.mem_toList.mpr (Finset.mem_univ _)) j
  have hmono : Monotone ((bitonicNetwork 64).exec (v ∘ alignedSegment b c)) :=
    bitonicNetwork_sorts 64 α (v ∘ alignedSegment b c)
  calc
    _ = (bitonicNetwork 64).exec (v ∘ alignedSegment b c) i := by
      simpa [alignedSegmentNet] using hact_i
    _ ≤ (bitonicNetwork 64).exec (v ∘ alignedSegment b c) j := hmono hij
    _ = _ := by simpa [alignedSegmentNet] using hact_j.symm

theorem shiftedGrid_sorts_each_segment {α : Type*} [LinearOrder α]
    (v : Wire → α) (b : Fin 63) (c : Fin 64) (i j : Fin 64) (hij : i ≤ j) :
    shiftedGrid.exec v (shiftedSegment b c i) ≤
      shiftedGrid.exec v (shiftedSegment b c j) := by
  have hflat := ComparatorNetwork.exec_flatMap shiftedChunks
    (fun p => shiftedSegmentNet p.1 p.2) v
  change shiftedGrid.exec v =
    shiftedChunks.foldl (fun v' p => (shiftedSegmentNet p.1 p.2).exec v') v at hflat
  rw [hflat]
  have hact_i := flatMap_scatter_exec_inside
    (m := fun _ : Fin 63 × Fin 64 => 64)
    (fun p => shiftedSegment p.1 p.2)
    (fun _ => bitonicNetwork 64)
    shiftedChunks v (Finset.nodup_toList _) (by
      intro p hp q hq hpq i' j'
      exact shifted_segments_separated p q hpq i' j')
    (b, c) (Finset.mem_toList.mpr (Finset.mem_univ _)) i
  have hact_j := flatMap_scatter_exec_inside
    (m := fun _ : Fin 63 × Fin 64 => 64)
    (fun p => shiftedSegment p.1 p.2)
    (fun _ => bitonicNetwork 64)
    shiftedChunks v (Finset.nodup_toList _) (by
      intro p hp q hq hpq i' j'
      exact shifted_segments_separated p q hpq i' j')
    (b, c) (Finset.mem_toList.mpr (Finset.mem_univ _)) j
  have hmono : Monotone ((bitonicNetwork 64).exec (v ∘ shiftedSegment b c)) :=
    bitonicNetwork_sorts 64 α (v ∘ shiftedSegment b c)
  calc
    _ = (bitonicNetwork 64).exec (v ∘ shiftedSegment b c) i := by
      simpa [shiftedSegmentNet] using hact_i
    _ ≤ (bitonicNetwork 64).exec (v ∘ shiftedSegment b c) j := hmono hij
    _ = _ := by simpa [shiftedSegmentNet] using hact_j.symm

/-- At least 32 false inputs in an aligned block force the first half of its
sorted output to be false. -/
theorem alignedSegment_first32_false (v : Wire → Bool) (b c : Fin 64)
    (hin : ∀ i : Fin 64, i.val < 32 → v (alignedSegment b c i) = false)
    (i : Fin 64) (hi : i.val < 32) :
    alignedGrid.exec v (alignedSegment b c i) = false := by
  let s : Fin 64 → Bool := fun j => alignedGrid.exec v (alignedSegment b c j)
  have hmono : Monotone s := by
    intro x y hxy
    exact alignedGrid_sorts_each_segment v b c x y hxy
  have hprefix : (Finset.Iio (⟨32, by omega⟩ : Fin 64)).card = 32 := by simp
  have hsubset : Finset.Iio (⟨32, by omega⟩ : Fin 64) ⊆
      Finset.univ.filter fun j : Fin 64 => v (alignedSegment b c j) = false := by
    intro j hj
    simp only [Finset.mem_Iio] at hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact hin j hj
  have hinput : 32 ≤
      (Finset.univ.filter fun j : Fin 64 => v (alignedSegment b c j) = false).card := by
    rw [← hprefix]
    exact Finset.card_le_card hsubset
  have hcount := alignedGrid_falseCount_segment v b c
  have hout : 32 ≤ (Finset.univ.filter fun j : Fin 64 => s j = false).card := by
    change 32 ≤ (Finset.univ.filter fun j : Fin 64 =>
      alignedGrid.exec v (alignedSegment b c j) = false).card
    rw [hcount]
    exact hinput
  exact sorted_false_prefix s hmono hout i hi

/-- At least 32 true inputs in an aligned block force the last half of its
sorted output to be true. -/
theorem alignedSegment_last32_true (v : Wire → Bool) (b c : Fin 64)
    (hin : ∀ i : Fin 64, 32 ≤ i.val → v (alignedSegment b c i) = true)
    (i : Fin 64) (hi : 32 ≤ i.val) :
    alignedGrid.exec v (alignedSegment b c i) = true := by
  let s : Fin 64 → Bool := fun j => alignedGrid.exec v (alignedSegment b c j)
  have hmono : Monotone s := by
    intro x y hxy
    exact alignedGrid_sorts_each_segment v b c x y hxy
  have hprefix : (Finset.Iio (⟨32, by omega⟩ : Fin 64)).card = 32 := by simp
  have hsubset : (Finset.univ.filter fun j : Fin 64 =>
      v (alignedSegment b c j) = false) ⊆ Finset.Iio (⟨32, by omega⟩ : Fin 64) := by
    intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
    simp only [Finset.mem_Iio]
    by_contra hnot
    have hj32Fin : (⟨32, by omega⟩ : Fin 64) ≤ j := le_of_not_gt hnot
    have hj32 : 32 ≤ j.val := Fin.le_iff_val_le_val.mp hj32Fin
    rw [hin j hj32] at hj
    cases hj
  have hinput :
      (Finset.univ.filter fun j : Fin 64 => v (alignedSegment b c j) = false).card ≤ 32 := by
    calc
      _ ≤ (Finset.Iio (⟨32, by omega⟩ : Fin 64)).card := Finset.card_le_card hsubset
      _ = 32 := hprefix
  have hcount := alignedGrid_falseCount_segment v b c
  have hout : (Finset.univ.filter fun j : Fin 64 => s j = false).card ≤ 32 := by
    change (Finset.univ.filter fun j : Fin 64 =>
      alignedGrid.exec v (alignedSegment b c j) = false).card ≤ 32
    rw [hcount]
    exact hinput
  exact sorted_true_suffix s hmono hout i hi

/-- If a dirty interval straddles the aligned boundary after column block `k`,
then after the aligned pass the 32 rows immediately before the shifted repair
segment are all false and the 32 rows immediately after it are all true. -/
theorem aligned_crossing_boundary_has_uniform_halves
    (v : Wire → Bool) (c : Fin 64) (k : Fin 64) (hk : 0 < k.val)
    (hbelow : ∀ r : Row, r.val < 64 * k.val - 32 →
      v (matrixWire 4096 64 r c) = false)
    (habove : ∀ r : Row, 64 * k.val + 32 ≤ r.val →
      v (matrixWire 4096 64 r c) = true)
    (i : Fin 64) :
    (i.val < 32 →
      alignedGrid.exec v (matrixWire 4096 64
        ⟨64 * (k.val - 1) + i.val, by have := k.isLt; omega⟩ c) = false) ∧
    (32 ≤ i.val →
      alignedGrid.exec v (matrixWire 4096 64
        ⟨64 * k.val + i.val, by have := k.isLt; have := i.isLt; omega⟩ c) = true) := by
  let kl : Fin 64 := ⟨k.val - 1, by omega⟩
  constructor
  · intro hi
    have hinput : ∀ j : Fin 64, j.val < 32 →
        v (alignedSegment kl c j) = false := by
      intro j hj
      apply hbelow
      simp [alignedRow, kl]
      omega
    have hout := alignedSegment_first32_false v kl c hinput i hi
    simpa [alignedSegment, alignedRow, kl] using hout
  · intro hi
    have hinput : ∀ j : Fin 64, 32 ≤ j.val →
        v (alignedSegment k c j) = true := by
      intro j hj
      apply habove
      simp [alignedRow]
      omega
    have hout := alignedSegment_last32_true v k c hinput i hi
    simpa [alignedSegment, alignedRow] using hout

theorem alignedGrid_false_before_crossing
    (v : Wire → Bool) (c : Fin 64) (k : Fin 64) (hk : 0 < k.val)
    (hbelow : ∀ r : Row, r.val < 64 * k.val - 32 →
      v (matrixWire 4096 64 r c) = false)
    (r : Row) (hr : r.val < 64 * k.val - 32) :
    alignedGrid.exec v (matrixWire 4096 64 r c) = false := by
  obtain ⟨b, i, hrow⟩ := row_eq_alignedRow r
  have hrowVal : 64 * b.val + i.val = r.val := by
    have hh := congrArg Fin.val hrow
    simpa [alignedRow] using hh
  have hb : b.val ≤ k.val - 1 := by omega
  have hwire := matrixWire_eq_alignedSegment r c b i hrow
  rw [hwire]
  by_cases heq : b.val = k.val - 1
  · have hi : i.val < 32 := by omega
    have hinput : ∀ j : Fin 64, j.val < 32 →
        v (alignedSegment b c j) = false := by
      intro j hj
      apply hbelow
      simp [alignedRow]
      omega
    exact alignedSegment_first32_false v b c hinput i hi
  · apply alignedSegment_const v b c false
    · intro j
      apply hbelow
      simp [alignedRow]
      omega

theorem alignedGrid_true_after_crossing
    (v : Wire → Bool) (c : Fin 64) (k : Fin 64)
    (habove : ∀ r : Row, 64 * k.val + 32 ≤ r.val →
      v (matrixWire 4096 64 r c) = true)
    (r : Row) (hr : 64 * k.val + 32 ≤ r.val) :
    alignedGrid.exec v (matrixWire 4096 64 r c) = true := by
  obtain ⟨b, i, hrow⟩ := row_eq_alignedRow r
  have hrowVal : 64 * b.val + i.val = r.val := by
    have hh := congrArg Fin.val hrow
    simpa [alignedRow] using hh
  have hb : k.val ≤ b.val := by omega
  have hwire := matrixWire_eq_alignedSegment r c b i hrow
  rw [hwire]
  by_cases heq : b.val = k.val
  · have hi : 32 ≤ i.val := by omega
    have hinput : ∀ j : Fin 64, 32 ≤ j.val →
        v (alignedSegment b c j) = true := by
      intro j hj
      apply habove
      simp [alignedRow]
      omega
    exact alignedSegment_last32_true v b c hinput i hi
  · apply alignedSegment_const v b c true
    · intro j
      apply habove
      simp [alignedRow]
      omega

theorem alignedGrid_column_monotone_if_band_inside_block
    (v : Wire → Bool) (c : Fin 64) (q : Fin 64)
    (hbelow : ∀ r : Row, r.val < 64 * q.val →
      v (matrixWire 4096 64 r c) = false)
    (habove : ∀ r : Row, 64 * (q.val + 1) ≤ r.val →
      v (matrixWire 4096 64 r c) = true) :
    Monotone (fun r : Row => alignedGrid.exec v (matrixWire 4096 64 r c)) := by
  intro r s hrs
  change alignedGrid.exec v (matrixWire 4096 64 r c) ≤
    alignedGrid.exec v (matrixWire 4096 64 s c)
  obtain ⟨b, i, hrow⟩ := row_eq_alignedRow r
  obtain ⟨d, j, hrow'⟩ := row_eq_alignedRow s
  have hrval : 64 * b.val + i.val = r.val := by
    have h := congrArg Fin.val hrow
    simpa [alignedRow] using h
  have hsval : 64 * d.val + j.val = s.val := by
    have h := congrArg Fin.val hrow'
    simpa [alignedRow] using h
  have hrsval : r.val ≤ s.val := Fin.le_iff_val_le_val.mp hrs
  have hbd : b.val ≤ d.val := by
    have hi := i.isLt
    have hj := j.isLt
    omega
  have hwire : matrixWire 4096 64 r c = alignedSegment b c i :=
    matrixWire_eq_alignedSegment r c b i hrow
  have hwire' : matrixWire 4096 64 s c = alignedSegment d c j :=
    matrixWire_eq_alignedSegment s c d j hrow'
  rw [hwire, hwire']
  by_cases hbq : b.val < q.val
  · have hconst : ∀ x : Fin 64, v (alignedSegment b c x) = false := by
      intro x
      apply hbelow
      simp [alignedRow]
      omega
    rw [alignedSegment_const v b c false hconst i]
    exact Bool.false_le _
  · by_cases hqb : q.val < b.val
    · have hconst : ∀ x : Fin 64, v (alignedSegment b c x) = true := by
        intro x
        apply habove
        simp [alignedRow]
        omega
      rw [alignedSegment_const v b c true hconst i,
        alignedSegment_const v d c true (by
          intro x
          apply habove
          simp [alignedRow]
          omega) j]
    · have hbqeq : b.val = q.val := by omega
      have hdq : q.val ≤ d.val := by omega
      by_cases hdgt : q.val < d.val
      · have hconst : ∀ x : Fin 64, v (alignedSegment d c x) = true := by
          intro x
          apply habove
          simp [alignedRow]
          omega
        rw [alignedSegment_const v d c true hconst j]
        exact Bool.le_true _
      · have hdqeq : d.val = q.val := by omega
        have hbEq : b = q := Fin.ext hbqeq
        have hdEq : d = q := Fin.ext hdqeq
        subst b
        subst d
        exact alignedGrid_sorts_each_segment v q c i j
          (Fin.le_iff_val_le_val.mpr (by omega))

theorem twoGrid_column_false_before_crossing
    (v : Wire → Bool) (c : Fin 64) (k : Fin 64) (hk : 0 < k.val)
    (hbelow : ∀ r : Row, r.val < 64 * k.val - 32 →
      v (matrixWire 4096 64 r c) = false)
    (r : Row) (hr : r.val < 64 * k.val - 32) :
    twoGridRepair.exec v (matrixWire 4096 64 r c) = false := by
  have hfirst := alignedGrid_false_before_crossing v c k hk hbelow r hr
  rw [twoGridRepair]
  unfold ComparatorNetwork.append
  rw [ComparatorNetwork.exec_append]
  by_cases hedge : r.val < 32 ∨ 4064 ≤ r.val
  · rw [shiftedGrid_exec_edge_unchanged (alignedGrid.exec v) r c hedge]
    exact hfirst
  · have hrlo : 32 ≤ r.val := by omega
    have hrhi : r.val < 4064 := by omega
    obtain ⟨b, i, hrow⟩ := row_eq_shiftedRow r hrlo hrhi
    have hb : b.val < k.val - 1 := by
      have hh := congrArg Fin.val hrow
      simp only [shiftedRow] at hh
      omega
    have hconst : ∀ j : Fin 64,
        alignedGrid.exec v (shiftedSegment b c j) = false := by
      intro j
      have hrowleft : (shiftedRow b j).val < 64 * k.val - 32 := by
        simp [shiftedRow]
        omega
      have hval := alignedGrid_false_before_crossing v c k hk hbelow
        (shiftedRow b j) hrowleft
      simpa [shiftedSegment, shiftedRow] using hval
    have hout := shiftedSegment_const (alignedGrid.exec v) b c false hconst i
    rw [matrixWire_eq_shiftedSegment r c b i hrow]
    exact hout

theorem twoGrid_column_true_after_crossing
    (v : Wire → Bool) (c : Fin 64) (k : Fin 64)
    (habove : ∀ r : Row, 64 * k.val + 32 ≤ r.val →
      v (matrixWire 4096 64 r c) = true)
    (r : Row) (hr : 64 * k.val + 32 ≤ r.val) :
    twoGridRepair.exec v (matrixWire 4096 64 r c) = true := by
  have hfirst := alignedGrid_true_after_crossing v c k habove r hr
  rw [twoGridRepair]
  unfold ComparatorNetwork.append
  rw [ComparatorNetwork.exec_append]
  by_cases hedge : r.val < 32 ∨ 4064 ≤ r.val
  · rw [shiftedGrid_exec_edge_unchanged (alignedGrid.exec v) r c hedge]
    exact hfirst
  · have hrlo : 32 ≤ r.val := by omega
    have hrhi : r.val < 4064 := by omega
    obtain ⟨b, i, hrow⟩ := row_eq_shiftedRow r hrlo hrhi
    have hb : k.val ≤ b.val := by
      have hh := congrArg Fin.val hrow
      simp only [shiftedRow] at hh
      change 32 + 64 * b.val + i.val = r.val at hh
      have hi := i.isLt
      omega
    have hconst : ∀ j : Fin 64,
        alignedGrid.exec v (shiftedSegment b c j) = true := by
      intro j
      have hrowright : 64 * k.val + 32 ≤ (shiftedRow b j).val := by
        simp [shiftedRow]
        omega
      have hval := alignedGrid_true_after_crossing v c k habove
        (shiftedRow b j) hrowright
      simpa [shiftedSegment, shiftedRow] using hval
    have hout := shiftedSegment_const (alignedGrid.exec v) b c true hconst i
    rw [matrixWire_eq_shiftedSegment r c b i hrow]
    exact hout

theorem twoGridRepair_sorts_crossing_band
    (v : Wire → Bool) (c : Fin 64) (k : Fin 64) (hk : 0 < k.val)
    (hbelow : ∀ r : Row, r.val < 64 * k.val - 32 →
      v (matrixWire 4096 64 r c) = false)
    (habove : ∀ r : Row, 64 * k.val + 32 ≤ r.val →
      v (matrixWire 4096 64 r c) = true) :
    Monotone (fun r : Row => twoGridRepair.exec v (matrixWire 4096 64 r c)) := by
  have hklt := k.isLt
  have hlo : ∀ r : Row, r.val < 64 * k.val - 32 →
      twoGridRepair.exec v (matrixWire 4096 64 r c) = false :=
    fun r hr => twoGrid_column_false_before_crossing v c k hk hbelow r hr
  have hhi : ∀ r : Row, 64 * k.val + 32 ≤ r.val →
      twoGridRepair.exec v (matrixWire 4096 64 r c) = true :=
    fun r hr => twoGrid_column_true_after_crossing v c k habove r hr
  have hmiddle : ∀ r s : Row,
      64 * k.val - 32 ≤ r.val → s.val < 64 * k.val + 32 → r ≤ s →
      twoGridRepair.exec v (matrixWire 4096 64 r c) ≤
        twoGridRepair.exec v (matrixWire 4096 64 s c) := by
    intro r s hr hs hrs
    have hrsVal : r.val ≤ s.val := Fin.le_iff_val_le_val.mp hrs
    rw [twoGridRepair_exec]
    let b : Fin 63 := ⟨k.val - 1, by omega⟩
    let i : Fin 64 := ⟨r.val - (64 * k.val - 32), by omega⟩
    let j : Fin 64 := ⟨s.val - (64 * k.val - 32), by omega⟩
    have hri : shiftedRow b i = r := by
      apply Fin.ext
      simp [shiftedRow, b, i]
      omega
    have hsj : shiftedRow b j = s := by
      apply Fin.ext
      simp [shiftedRow, b, j]
      omega
    have hij : i ≤ j := by
      apply Fin.le_iff_val_le_val.mpr
      simp [i, j]
      omega
    rw [matrixWire_eq_shiftedSegment r c b i hri,
      matrixWire_eq_shiftedSegment s c b j hsj]
    exact shiftedGrid_sorts_each_segment (alignedGrid.exec v) b c i j hij
  intro r s hrs
  change twoGridRepair.exec v (matrixWire 4096 64 r c) ≤
    twoGridRepair.exec v (matrixWire 4096 64 s c)
  have hrsVal : r.val ≤ s.val := Fin.le_iff_val_le_val.mp hrs
  by_cases hrlo : r.val < 64 * k.val - 32
  · have hro := hlo r hrlo
    by_cases hslo : s.val < 64 * k.val - 32
    · rw [hro, hlo s hslo]
    · by_cases hshi : 64 * k.val + 32 ≤ s.val
      · rw [hro, hhi s hshi]
        decide
      · rw [hro]
        exact Bool.false_le _
  · by_cases hrhi : 64 * k.val + 32 ≤ r.val
    · have hro := hhi r hrhi
      by_cases hshi : 64 * k.val + 32 ≤ s.val
      · rw [hro, hhi s hshi]
      · omega
    · by_cases hshi : 64 * k.val + 32 ≤ s.val
      · rw [hhi s hshi]
        exact Bool.le_true _
      · apply hmiddle r s (by omega) (by omega) hrs

theorem twoGridRepair_sorts_band_inside_aligned_block
    (v : Wire → Bool) (c q : Fin 64) (a b : Nat)
    (hbelow : ∀ r : Row, r.val < a → v (matrixWire 4096 64 r c) = false)
    (habove : ∀ r : Row, b ≤ r.val → v (matrixWire 4096 64 r c) = true)
    (hleft : 64 * q.val ≤ a) (hright : b ≤ 64 * (q.val + 1)) :
    Monotone (fun r : Row => twoGridRepair.exec v (matrixWire 4096 64 r c)) := by
  have hfirst := alignedGrid_column_monotone_if_band_inside_block v c q
    (by
      intro r hr
      exact hbelow r (Nat.lt_of_lt_of_le hr hleft))
    (by
      intro r hr
      exact habove r (Nat.le_trans hright hr))
  have hfinal : ∀ r : Row,
      twoGridRepair.exec v (matrixWire 4096 64 r c) =
        alignedGrid.exec v (matrixWire 4096 64 r c) := by
    intro r
    rw [twoGridRepair_exec]
    exact shiftedGrid_column_eq_of_monotone (alignedGrid.exec v) c hfirst r
  intro r s hrs
  change twoGridRepair.exec v (matrixWire 4096 64 r c) ≤
    twoGridRepair.exec v (matrixWire 4096 64 s c)
  rw [hfinal r, hfinal s]
  exact hfirst hrs

theorem interval_width_le_32_cases (a b : Nat) (hab : a ≤ b)
    (hwidth : b - a ≤ 32) (hb : b ≤ 4096) :
    (∃ q : Fin 64, 64 * q.val ≤ a ∧ b ≤ 64 * (q.val + 1)) ∨
    (∃ k : Fin 64, 0 < k.val ∧ 64 * k.val - 32 ≤ a ∧
      b ≤ 64 * k.val + 32) := by
  have ha : a ≤ 4096 := le_trans hab hb
  by_cases haeq : a = 4096
  · left
    refine ⟨⟨63, by omega⟩, ?_, ?_⟩ <;> simp <;> omega
  · have halt : a < 4096 := by omega
    let q : Fin 64 := ⟨a / 64, by omega⟩
    have hdiv := Nat.div_add_mod a 64
    have hmod : a % 64 < 64 := Nat.mod_lt a (by norm_num)
    by_cases hcontained : b ≤ 64 * (q.val + 1)
    · left
      refine ⟨q, ?_, hcontained⟩
      have hmul : 64 * (a / 64) ≤ a := by omega
      simpa [q] using hmul
    · right
      have hcross : 64 * (q.val + 1) < b := by omega
      have hkbound : q.val + 1 < 64 := by omega
      let k : Fin 64 := ⟨q.val + 1, by omega⟩
      have hcross' : 64 * (a / 64 + 1) < b := by simpa [q] using hcross
      have hba : b ≤ a + 32 := by omega
      refine ⟨k, by simp [k], ?_, ?_⟩
      · have hmul : 64 * (a / 64) ≤ a := by omega
        have hrem : a < 64 * (a / 64 + 1) := by omega
        simp [k, q]
        omega
      · have hrem : a < 64 * (a / 64 + 1) := by omega
        simp [k, q]
        omega

theorem twoGridRepair_sorts_threshold_band
    (v : Wire → Bool) (c : Fin 64) (a b : Nat)
    (hab : a ≤ b) (hwidth : b - a ≤ 32) (hb : b ≤ 4096)
    (hbelow : ∀ r : Row, r.val < a → v (matrixWire 4096 64 r c) = false)
    (habove : ∀ r : Row, b ≤ r.val → v (matrixWire 4096 64 r c) = true) :
    Monotone (fun r : Row => twoGridRepair.exec v (matrixWire 4096 64 r c)) := by
  rcases interval_width_le_32_cases a b hab hwidth hb with
    ⟨q, hleft, hright⟩ | ⟨k, hk, hleft, hright⟩
  · exact twoGridRepair_sorts_band_inside_aligned_block v c q a b hbelow habove
      hleft hright
  · exact twoGridRepair_sorts_crossing_band v c k hk
      (fun r hr => hbelow r (Nat.lt_of_lt_of_le hr hleft))
      (fun r hr => habove r (Nat.le_trans hright hr))

theorem physical_twoGridRepair_restores_columnMonotone
    (h : Col → Nat) (hbound : ∀ c, h c ≤ 4096)
    (perm : Row → Equiv.Perm Col) :
    ∀ c : Col, Monotone (fun r : Row =>
      twoGridRepair.exec (fullHeightAfterRowPermutation h perm)
        (matrixWire 4096 64 r c)) := by
  intro c
  have horder := lowBoundary_le_highBoundary h
  have hband := band_width_le_thirteen h hbound
  have hupper := highBoundary_le_4096 h
  have hwidth : highBoundary h - lowBoundary h ≤ 32 := by omega
  exact twoGridRepair_sorts_threshold_band
    (fullHeightAfterRowPermutation h perm) c
    (lowBoundary h) (highBoundary h) horder hwidth hupper
    (by
      intro r hr
      exact fullHeightAfterRowPermutation_false_below_band h perm r hr c)
    (by
      intro r hr
      exact fullHeightAfterRowPermutation_true_above_band h perm r hr c)

theorem alignedGrid_columnLocal :
    Chvatal.ColumnLocalNetwork 4096 64 alignedGrid := by
  intro cmp hc
  simp only [alignedGrid, List.mem_flatMap] at hc
  rcases hc with ⟨p, hp, hcmp⟩
  simp only [alignedSegmentNet, ComparatorNetwork.scatterEmbed,
    List.mem_map] at hcmp
  rcases hcmp with ⟨localCmp, hlocal, rfl⟩
  refine ⟨p.2, alignedRow p.1 localCmp.i, alignedRow p.1 localCmp.j, ?_, ?_⟩
  · change alignedSegment p.1 p.2 localCmp.i =
      matrixWire 4096 64 (alignedRow p.1 localCmp.i) p.2
    rfl
  · change alignedSegment p.1 p.2 localCmp.j =
      matrixWire 4096 64 (alignedRow p.1 localCmp.j) p.2
    rfl

theorem shiftedGrid_columnLocal :
    Chvatal.ColumnLocalNetwork 4096 64 shiftedGrid := by
  intro cmp hc
  simp only [shiftedGrid, List.mem_flatMap] at hc
  rcases hc with ⟨p, hp, hcmp⟩
  simp only [shiftedSegmentNet, ComparatorNetwork.scatterEmbed,
    List.mem_map] at hcmp
  rcases hcmp with ⟨localCmp, hlocal, rfl⟩
  refine ⟨p.2, shiftedRow p.1 localCmp.i, shiftedRow p.1 localCmp.j, ?_, ?_⟩
  · change shiftedSegment p.1 p.2 localCmp.i =
      matrixWire 4096 64 (shiftedRow p.1 localCmp.i) p.2
    rfl
  · change shiftedSegment p.1 p.2 localCmp.j =
      matrixWire 4096 64 (shiftedRow p.1 localCmp.j) p.2
    rfl

theorem twoGridRepair_columnLocal :
    Chvatal.ColumnLocalNetwork 4096 64 twoGridRepair := by
  intro cmp hc
  simp only [twoGridRepair, ComparatorNetwork.append,
    List.mem_append] at hc
  rcases hc with hc | hc
  · exact alignedGrid_columnLocal cmp hc
  · exact shiftedGrid_columnLocal cmp hc

/-- A monotone Boolean column is the bottom-suffix unary profile determined
by its number of true entries. -/
theorem monotone_bool_eq_bottomUnaryProfile {n : Nat} (s : Fin n → Bool)
    (hs : Monotone s) (r : Fin n) :
    s r = decide (n - (Finset.univ.filter fun i : Fin n => s i = true).card
      ≤ r.val) := by
  let count := (Finset.univ.filter fun i : Fin n => s i = true).card
  by_cases hr : s r = true
  · have hsub : Finset.Ici r ⊆ Finset.univ.filter fun i : Fin n => s i = true := by
      intro i hi
      simp only [Finset.mem_Ici] at hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      have hmono := hs hi
      rw [hr] at hmono
      cases h : s i
      · have hbad : ¬ (true ≤ false) := by decide
        exact False.elim (hbad (by simpa [h] using hmono))
      · exact rfl
    have hcard := Finset.card_le_card hsub
    have hIci : (Finset.Ici r).card = n - r.val := by simp
    have hcount : n - count ≤ r.val := by
      dsimp [count] at hcard ⊢
      omega
    rw [hr]
    exact (decide_eq_true hcount).symm
  · have hfalse : s r = false := by cases h : s r <;> simp_all
    have hsub : Finset.univ.filter (fun i : Fin n => s i = true) ⊆
        Finset.Ioi r := by
      intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
      simp only [Finset.mem_Ioi]
      by_contra hir
      have hle : i ≤ r := le_of_not_gt hir
      have hmono := hs hle
      rw [hfalse] at hmono
      have hbad : ¬ (true ≤ false) := by decide
      exact False.elim (hbad (by simpa [hi] using hmono))
    have hcard := Finset.card_le_card hsub
    have hIoi : (Finset.Ioi r).card = n - (r.val + 1) := by
      simp
      omega
    have hcount : r.val < n - count := by
      dsimp [count] at hcard ⊢
      omega
    rw [hfalse]
    exact (decide_eq_false (Nat.not_le.mpr hcount)).symm

/-- The repaired physical stage is represented as a bottom-unary matrix by
the exact column counts of its pre-repair scrambled input. Column-local
network preservation proves that these are also the repaired output counts. -/
noncomputable def physicalTwoGridRepairHeight (h : Col → Nat)
    (perm : Row → Equiv.Perm Col) (c : Col) : Nat :=
  Chvatal.matrixColumnTrueCount c (fullHeightAfterRowPermutation h perm)

def heightColumnSums (h : Col → Nat)
    (hbound : ∀ c, h c ≤ 4096) : Chvatal.MonotoneColumnSums 4096 64 :=
  fun c => ⟨h c, Nat.lt_succ_of_le (hbound c)⟩

theorem bottomUnaryProfile_eq_monotoneMatrixBool (h : Col → Nat)
    (hbound : ∀ c, h c ≤ 4096) :
    bottomUnaryProfile h =
      Chvatal.monotoneMatrixBool (by omega)
        (heightColumnSums h hbound) := by
  funext w
  rw [← matrixWire_matrixRow_col (by omega) w]
  simp only [bottomUnaryProfile, Chvatal.monotoneMatrixBool,
    Chvatal.monotoneRowOnes, matrixWire_row_col, Finset.mem_filter,
    Finset.mem_univ, true_and]
  have hrow := matrixRow 4096 64 (by omega) w
  have hcol := matrixCol 4096 64 (by omega) w
  have hiff : 4096 - h hcol ≤ hrow.val ↔
      4096 - hrow.val ≤ h hcol := by omega
  simp [heightColumnSums]
  omega

theorem physical_twoGridRepairHeight_eq_scrambled_column_count
    (h : Col → Nat) (perm : Row → Equiv.Perm Col) (c : Col) :
    physicalTwoGridRepairHeight h perm c =
      Chvatal.matrixColumnTrueCount c
        (twoGridRepair.exec (fullHeightAfterRowPermutation h perm)) := by
  unfold physicalTwoGridRepairHeight
  symm
  exact Chvatal.matrixColumnTrueCount_exec_eq (by omega) c twoGridRepair
    twoGridRepair_columnLocal (fullHeightAfterRowPermutation h perm)

theorem physical_twoGridRepairHeight_eq_rowScrambled_sum
    (h : Col → Nat) (perm : Row → Equiv.Perm Col) (c : Col) :
    physicalTwoGridRepairHeight h perm c =
      (Finset.univ.filter fun r : Row =>
        rowScrambledUnary h perm r c = true).card := by
  unfold physicalTwoGridRepairHeight Chvatal.matrixColumnTrueCount
  apply congrArg Finset.card
  ext r
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [fullHeightAfterRowPermutation_matrixWire]

theorem physical_twoGridRepairHeight_eq_scrambledColSum
    (h : Col → Nat) (hbound : ∀ c, h c ≤ 4096)
    (perm : Row → Equiv.Perm Col) (c : Col) :
    physicalTwoGridRepairHeight h perm c =
      Chvatal.scrambledColSum
        (heightColumnSums (fullHeightTwoShuffle h)
          (fullHeightTwoShuffle_le_4096 h hbound))
        (fun r => (perm r).symm) c := by
  unfold physicalTwoGridRepairHeight
  let sums := heightColumnSums (fullHeightTwoShuffle h)
    (fullHeightTwoShuffle_le_4096 h hbound)
  let sigma : Row → Equiv.Perm Col := fun r => (perm r).symm
  have hinput : fullHeightAfterRowPermutation h perm =
      Function.comp (Chvatal.monotoneMatrixBool (by omega) sums)
        (rowScrambleWirePerm 4096 64 (by omega) sigma).symm := by
    change Function.comp (bottomUnaryProfile (fullHeightTwoShuffle h))
        (rowScrambleWirePerm 4096 64 (by omega) sigma).symm = _
    rw [bottomUnaryProfile_eq_monotoneMatrixBool (fullHeightTwoShuffle h)
      (fullHeightTwoShuffle_le_4096 h hbound)]
  rw [hinput]
  exact (Chvatal.scrambledColSum_eq_matrixColumnTrueCount (by omega)
    sigma sums c).symm

theorem physical_slope25TwoGridRepairHeight_eq_scrambledColSum
    (h : Col → Nat) (hbound : ∀ c, h c ≤ 4096) (c : Col) :
    physicalTwoGridRepairHeight h
      (fun r => (affine25 r).symm) c =
      Chvatal.scrambledColSum
        (heightColumnSums (fullHeightTwoShuffle h)
          (fullHeightTwoShuffle_le_4096 h hbound))
        affine25 c := by
  exact physical_twoGridRepairHeight_eq_scrambledColSum
    h hbound (fun r => (affine25 r).symm) c

theorem physical_twoGridRepairHeight_range_le_thirteen
    (h : Col → Nat) (hbound : ∀ c, h c ≤ 4096)
    (perm : Row → Equiv.Perm Col) (c d : Col) :
    physicalTwoGridRepairHeight h perm c ≤
      physicalTwoGridRepairHeight h perm d + 13 := by
  have hlow : lowBoundary h ≤ highBoundary h :=
    lowBoundary_le_highBoundary h
  have hhigh : highBoundary h ≤ 4096 := highBoundary_le_4096 h
  have hwidth := band_width_le_thirteen h hbound
  have hupper (j : Col) :
      physicalTwoGridRepairHeight h perm j ≤ 4096 - lowBoundary h := by
    change (Finset.univ.filter fun r : Row =>
      fullHeightAfterRowPermutation h perm (matrixWire 4096 64 r j) = true).card ≤ _
    have hsubset : (Finset.univ.filter fun r : Row =>
        fullHeightAfterRowPermutation h perm (matrixWire 4096 64 r j) = true) ⊆
        Finset.univ.filter (fun r : Row => lowBoundary h ≤ r.val) := by
      intro r hr
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hr ⊢
      by_contra hnot
      have hbelow := fullHeightAfterRowPermutation_false_below_band
        h perm r (by omega) j
      rw [hbelow] at hr
      cases hr
    calc
      _ ≤ (Finset.univ.filter (fun r : Row => lowBoundary h ≤ r.val)).card :=
        Finset.card_le_card hsubset
      _ = 4096 - lowBoundary h :=
        card_filter_val_ge 4096 (lowBoundary h) (by omega)
  have hlower (j : Col) :
      4096 - highBoundary h ≤ physicalTwoGridRepairHeight h perm j := by
    change _ ≤ (Finset.univ.filter fun r : Row =>
      fullHeightAfterRowPermutation h perm (matrixWire 4096 64 r j) = true).card
    have hsubset : Finset.univ.filter
        (fun r : Row => highBoundary h ≤ r.val) ⊆
        Finset.univ.filter (fun r : Row =>
          fullHeightAfterRowPermutation h perm (matrixWire 4096 64 r j) = true) := by
      intro r hr
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hr ⊢
      exact fullHeightAfterRowPermutation_true_above_band h perm r hr j
    calc
      4096 - highBoundary h =
          (Finset.univ.filter (fun r : Row => highBoundary h ≤ r.val)).card :=
        (card_filter_val_ge 4096 (highBoundary h) (by omega)).symm
      _ ≤ _ := Finset.card_le_card hsubset
  have hu := hupper c
  have hd := hlower d
  omega

/-- One complete local profile step: the two-shuffle height transition,
followed by the affine slope-25 row permutation and physical two-grid repair.
The repair preserves the column counts, so this is exactly the repaired
output height, not an abstract proxy. -/
noncomputable def d2LocalProfileStep (h : Col -> Nat) : Col -> Nat :=
  physicalTwoGridRepairHeight h (fun r => (affine25 r).symm)

theorem d2LocalProfileStep_le_4096 (h : Col -> Nat) (c : Col) :
    d2LocalProfileStep h c <= 4096 := by
  rw [d2LocalProfileStep, physical_twoGridRepairHeight_eq_scrambled_column_count]
  exact Chvatal.matrixColumnTrueCount_le c
    (twoGridRepair.exec (fullHeightAfterRowPermutation h
      (fun r => (affine25 r).symm)))

/-- The local height transition closes the range-13 invariant in both
directions, for every valid source profile. -/
theorem d2LocalProfileStep_range_le_thirteen (h : Col -> Nat)
    (hbound : forall c, h c <= 4096) (c d : Col) :
    d2LocalProfileStep h c <= d2LocalProfileStep h d + 13 := by
  exact physical_twoGridRepairHeight_range_le_thirteen h hbound
    (fun r => (affine25 r).symm) c d

noncomputable def d2LocalProfileIterate : Nat -> (Col -> Nat) -> Col -> Nat
  | 0, h, c => h c
  | n + 1, h, c => d2LocalProfileStep (d2LocalProfileIterate n h) c

theorem d2LocalProfileIterate_le_4096 (n : Nat) (h : Col -> Nat)
    (hbound : forall c, h c <= 4096) (c : Col) :
    d2LocalProfileIterate n h c <= 4096 := by
  induction n with
  | zero => exact hbound c
  | succ n ih =>
      exact d2LocalProfileStep_le_4096 (d2LocalProfileIterate n h) c

/-- After every positive number of local stages, the full 64-column height
profile again lies in the range-13 state space. This is an all-depth
invariant for the scalar local transition. -/
theorem d2LocalProfileIterate_range_le_thirteen (n : Nat) (h : Col -> Nat)
    (hbound : forall c, h c <= 4096) (hn : 0 < n) (c d : Col) :
    d2LocalProfileIterate n h c <= d2LocalProfileIterate n h d + 13 := by
  cases n with
  | zero => omega
  | succ n =>
      change d2LocalProfileStep (d2LocalProfileIterate n h) c <=
        d2LocalProfileStep (d2LocalProfileIterate n h) d + 13
      apply d2LocalProfileStep_range_le_thirteen
      intro j
      exact d2LocalProfileIterate_le_4096 n h hbound j


theorem physical_twoGridRepair_eq_bottomUnaryProfile
    (h : Col → Nat) (hbound : ∀ c, h c ≤ 4096)
    (perm : Row → Equiv.Perm Col) :
    ∀ r : Row, ∀ c : Col,
      twoGridRepair.exec (fullHeightAfterRowPermutation h perm)
        (matrixWire 4096 64 r c) =
      decide (4096 - physicalTwoGridRepairHeight h perm c ≤ r.val) := by
  intro r c
  have hmono := physical_twoGridRepair_restores_columnMonotone h hbound perm c
  have hprofile := monotone_bool_eq_bottomUnaryProfile
    (fun r' : Row => twoGridRepair.exec (fullHeightAfterRowPermutation h perm)
      (matrixWire 4096 64 r' c)) hmono r
  have hcount := physical_twoGridRepairHeight_eq_scrambled_column_count h perm c
  have hcount' : physicalTwoGridRepairHeight h perm c =
      (Finset.univ.filter fun r' : Row =>
        twoGridRepair.exec (fullHeightAfterRowPermutation h perm)
          (matrixWire 4096 64 r' c) = true).card := by
    simpa [Chvatal.matrixColumnTrueCount] using hcount
  rw [← hcount'] at hprofile
  exact hprofile

set_option maxHeartbeats 10000000 in
/-- For each input height profile, the repaired Boolean matrix has one
common dirty row band across all 64 columns. Its height is at most 13 rows;
outside the band every column agrees (all false below, all true above). -/
theorem physical_twoGridRepair_common_band
    (h : Col -> Nat) (hbound : forall c, h c <= 4096)
    (perm : Row -> Equiv.Perm Col) :
    exists a b, b - a <= 13 /\ a <= b /\ a <= 4096 /\ b <= 4096 /\
      (forall r : Row, forall c : Col, r.val < a ->
        twoGridRepair.exec (fullHeightAfterRowPermutation h perm)
          (matrixWire 4096 64 r c) = false) /\
      (forall r : Row, forall c : Col, b <= r.val ->
        twoGridRepair.exec (fullHeightAfterRowPermutation h perm)
          (matrixWire 4096 64 r c) = true) := by
  let x : Col -> Nat := physicalTwoGridRepairHeight h perm
  let vals : Finset Nat := Finset.univ.image x
  have hvals : vals.Nonempty := Finset.image_nonempty.mpr Finset.univ_nonempty
  let lo : Nat := vals.min' hvals
  let hi : Nat := vals.max' hvals
  have hlo : forall c, lo <= x c := by
    intro c
    have hm : x c ∈ vals := Finset.mem_image.mpr (Exists.intro c (And.intro (Finset.mem_univ _) rfl))
    simpa [lo, vals] using Finset.min'_le (s := Finset.univ.image x) (x c) hm
  have hhi : forall c, x c <= hi := by
    intro c
    have hm : x c ∈ vals := Finset.mem_image.mpr (Exists.intro c (And.intro (Finset.mem_univ _) rfl))
    simpa [hi, vals] using Finset.le_max' (s := Finset.univ.image x) (x c) hm
  have hminmem := Finset.min'_mem vals hvals
  have hmaxmem := Finset.max'_mem vals hvals
  let cmin : Col := Classical.choose (Finset.mem_image.mp hminmem)
  let cmax : Col := Classical.choose (Finset.mem_image.mp hmaxmem)
  have hmin : x cmin = lo := (Classical.choose_spec (Finset.mem_image.mp hminmem)).2
  have hmax : x cmax = hi := (Classical.choose_spec (Finset.mem_image.mp hmaxmem)).2
  have hrange : x cmax <= x cmin + 13 := by
    simpa [x] using physical_twoGridRepairHeight_range_le_thirteen
      h hbound perm cmax cmin
  have hrange' : hi - lo <= 13 := by
    rw [hmax, hmin] at hrange
    omega
  have hhiBound : hi <= 4096 := by
    calc
      hi = x cmax := hmax.symm
      _ <= 4096 := by
        dsimp [x]
        rw [physical_twoGridRepairHeight_eq_scrambled_column_count]
        exact Chvatal.matrixColumnTrueCount_le cmax
          (twoGridRepair.exec (fullHeightAfterRowPermutation h perm))
  have hlohi : lo <= hi := by
    calc
      lo <= x cmax := hlo cmax
      _ = hi := hmax
  let a := 4096 - hi
  let b := 4096 - lo
  refine Exists.intro a (Exists.intro b
    (And.intro ?_ (And.intro ?_ (And.intro ?_ (And.intro ?_ (And.intro ?_ ?_))))))
  case refine_1 =>
    dsimp [a, b]
    omega
  case refine_2 =>
    dsimp [a, b]
    omega
  case refine_3 =>
    dsimp [a]
    omega
  case refine_4 =>
    dsimp [b]
    omega
  case refine_5 =>
    intro r c hr
    have hxb : x c <= hi := hhi c
    have hthreshold : r.val < 4096 - x c := by omega
    have hprofile := physical_twoGridRepair_eq_bottomUnaryProfile h hbound perm r c
    rw [hprofile]
    exact decide_eq_false (Nat.not_le.mpr hthreshold)
  case refine_6 =>
    intro r c hr
    have hxl : lo <= x c := hlo c
    have hthreshold : 4096 - x c <= r.val := by omega
    have hprofile := physical_twoGridRepair_eq_bottomUnaryProfile h hbound perm r c
    rw [hprofile]
    exact decide_eq_true hthreshold

/-- The common row band is contiguous in row-major wire order and occupies
at most 832 wires. Thus each threshold output is already sorted outside one
input-dependent interval of a fixed maximum size. -/
theorem physical_twoGridRepair_common_wire_band
    (h : Col -> Nat) (hbound : forall c, h c <= 4096)
    (perm : Row -> Equiv.Perm Col) :
    exists a b, 64 * (b - a) <= 832 /\ a <= b /\
      64 * a <= 4096 * 64 /\ 64 * b <= 4096 * 64 /\
      (forall w : Wire, w.val < 64 * a ->
        twoGridRepair.exec (fullHeightAfterRowPermutation h perm) w = false) /\
      (forall w : Wire, 64 * b <= w.val ->
        twoGridRepair.exec (fullHeightAfterRowPermutation h perm) w = true) := by
  obtain ⟨a, b, hab, hab', ha, hb, hlo, hhi⟩ :=
    physical_twoGridRepair_common_band h hbound perm
  refine ⟨a, b, ?_, ?_, ?_, ?_, ?_, ?_⟩
  case refine_1 => omega
  case refine_2 =>
    exact hab'
  case refine_3 =>
    calc
      64 * a <= 64 * 4096 := Nat.mul_le_mul_left 64 ha
      _ = 4096 * 64 := by ring
  case refine_4 =>
    calc
      64 * b <= 64 * 4096 := Nat.mul_le_mul_left 64 hb
      _ = 4096 * 64 := by ring
  case refine_5 =>
    intro w hw
    let r := matrixRow 4096 64 (by omega) w
    let c := matrixCol 4096 64 (by omega) w
    have hwire : w.val = r.val * 64 + c.val := by
      have heq := congrArg Fin.val (matrixWire_matrixRow_col (by omega) w)
      dsimp [r, c] at heq
      simpa [matrixWire_row] using heq.symm
    have hr : r.val < a := by omega
    have hrewrite : w = matrixWire 4096 64 r c :=
      (matrixWire_matrixRow_col (by omega) w).symm
    rw [hrewrite]
    exact hlo r c hr
  case refine_6 =>
    intro w hw
    let r := matrixRow 4096 64 (by omega) w
    let c := matrixCol 4096 64 (by omega) w
    have hwire : w.val = r.val * 64 + c.val := by
      have heq := congrArg Fin.val (matrixWire_matrixRow_col (by omega) w)
      dsimp [r, c] at heq
      simpa [matrixWire_row] using heq.symm
    have hr : b <= r.val := by omega
    have hrewrite : w = matrixWire 4096 64 r c :=
      (matrixWire_matrixRow_col (by omega) w).symm
    rw [hrewrite]
    exact hhi r c hr

theorem alignedGrid_depth_le_21 : alignedGrid.depth ≤ 21 := by
  have hdepth : ∀ p ∈ alignedChunks, (alignedSegmentNet p.1 p.2).depth ≤ 21 := by
    intro p hp
    dsimp [alignedSegmentNet]
    exact (depth_scatterEmbed_le _ _ _).trans (by
      have hlog : Nat.clog 2 64 = 6 := by decide
      have hb := bitonicNetwork_depth_le_budget 64
      rw [hlog, bitonicDepthBudget_eq] at hb
      norm_num [bitonicDepthBudget] at hb ⊢
      exact hb)
  have hdisj : alignedChunks.Pairwise (fun p q =>
      ∀ c₁ ∈ (alignedSegmentNet p.1 p.2).comparators,
      ∀ c₂ ∈ (alignedSegmentNet q.1 q.2).comparators,
        (c₁.i ≠ c₂.i ∧ c₁.i ≠ c₂.j) ∧ (c₁.j ≠ c₂.i ∧ c₁.j ≠ c₂.j)) := by
    have hpair : alignedChunks.Pairwise (fun p q => p ≠ q) :=
      (List.nodup_iff_pairwise_ne).mp (Finset.nodup_toList _)
    exact hpair.imp (by
      intro p q hpq c₁ hc₁ c₂ hc₂
      exact aligned_disjoint p q hpq c₁ hc₁ c₂ hc₂)
  simpa [alignedGrid] using depth_flatMap_disjoint alignedChunks
    (fun p => (alignedSegmentNet p.1 p.2).comparators) 21 hdepth hdisj

theorem shiftedGrid_depth_le_21 : shiftedGrid.depth ≤ 21 := by
  have hdepth : ∀ p ∈ shiftedChunks, (shiftedSegmentNet p.1 p.2).depth ≤ 21 := by
    intro p hp
    dsimp [shiftedSegmentNet]
    exact (depth_scatterEmbed_le _ _ _).trans (by
      have hlog : Nat.clog 2 64 = 6 := by decide
      have hb := bitonicNetwork_depth_le_budget 64
      rw [hlog, bitonicDepthBudget_eq] at hb
      norm_num [bitonicDepthBudget] at hb ⊢
      exact hb)
  have hdisj : shiftedChunks.Pairwise (fun p q =>
      ∀ c₁ ∈ (shiftedSegmentNet p.1 p.2).comparators,
      ∀ c₂ ∈ (shiftedSegmentNet q.1 q.2).comparators,
        (c₁.i ≠ c₂.i ∧ c₁.i ≠ c₂.j) ∧ (c₁.j ≠ c₂.i ∧ c₁.j ≠ c₂.j)) := by
    have hpair : shiftedChunks.Pairwise (fun p q => p ≠ q) :=
      (List.nodup_iff_pairwise_ne).mp (Finset.nodup_toList _)
    exact hpair.imp (by
      intro p q hpq c₁ hc₁ c₂ hc₂
      exact shifted_disjoint p q hpq c₁ hc₁ c₂ hc₂)
  simpa [shiftedGrid] using depth_flatMap_disjoint shiftedChunks
    (fun p => (shiftedSegmentNet p.1 p.2).comparators) 21 hdepth hdisj

theorem twoGridRepair_depth_le_42 : twoGridRepair.depth ≤ 42 := by
  unfold twoGridRepair
  exact (ComparatorNetwork.depth_append_le alignedGrid shiftedGrid).trans
    (Nat.add_le_add alignedGrid_depth_le_21 shiftedGrid_depth_le_21)

end Chvatal.D2BandRepair4096Network
