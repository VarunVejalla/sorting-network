module

public import AKS.Paterson.RootRebuildInvariant

/-! # Two fixed child register sets with exact native-half separation -/

@[expose] public section

namespace Paterson.Bags

open Finset

def assignedHalf {k : ℕ} (pl : StoredPlacement k) (s : Fin 2) (i : Fin (2 ^ k)) : Prop :=
  assignedPrefix pl 1 (s.val + 1) i ∧ ¬ assignedPrefix pl 1 s.val i

instance {k : ℕ} (pl : StoredPlacement k) (s : Fin 2) : DecidablePred (assignedHalf pl s) :=
  fun i ↦ by unfold assignedHalf; infer_instance

def childRegisters {k : ℕ} (pl : StoredPlacement k) (hk : 6 ≤ k) (s : Fin 2) :
    Finset (Fin (2 ^ k)) :=
  positionalBin (upperRegisters pl (by omega)) 1 s.val ∪
    (deepRegisters pl hk).filter (assignedHalf pl s)

theorem positionalBin_halves_cover {k : ℕ} (U : Finset (Fin (2 ^ k))) (hd : 2 ∣ U.card) :
    positionalBin U 1 0 ∪ positionalBin U 1 1 = U := by
  apply subset_antisymm
  · exact union_subset (positionalBin_subset U 1 0) (positionalBin_subset U 1 1)
  · intro i hi
    have hin : i ∈ Set.range (U.orderEmbOfFin rfl) := by rw [range_orderEmbOfFin]; exact hi
    obtain ⟨j, rfl⟩ := hin
    have hsize := Nat.mul_div_cancel' hd
    have hj := j.isLt
    by_cases hl : j.val < U.card / 2
    · apply mem_union_left
      apply mem_image.mpr
      refine ⟨j, mem_filter.mpr ⟨mem_univ _, ?_⟩, rfl⟩
      simpa using hl
    · apply mem_union_right
      apply mem_image.mpr
      refine ⟨j, mem_filter.mpr ⟨mem_univ _, ?_⟩, rfl⟩
      norm_num only
      constructor <;> omega

theorem deep_assigned_halves_cover {k : ℕ} (pl : StoredPlacement k) (hk : 6 ≤ k) :
    (deepRegisters pl hk).filter (assignedHalf pl 0) ∪
      (deepRegisters pl hk).filter (assignedHalf pl 1) = deepRegisters pl hk := by
  ext i
  constructor
  · intro hi
    rcases mem_union.mp hi with h | h <;> exact (mem_filter.mp h).1
  · intro hi
    obtain ⟨x, _, hx⟩ := mem_biUnion.mp hi
    have h0 : ¬ assignedPrefix pl 1 0 i := by
      rw [assignedPrefix_on_subtree pl hk (by omega : 1 ≤ 6) 0 x hx]
      simp
    have h2 : assignedPrefix pl 1 2 i := by
      rw [assignedPrefix_on_subtree pl hk (by omega : 1 ≤ 6) 2 x hx]
      simpa using x.isLt
    by_cases h1 : assignedPrefix pl 1 1 i
    · exact mem_union_left _ (mem_filter.mpr ⟨hi, h1, h0⟩)
    · exact mem_union_right _ (mem_filter.mpr ⟨hi, h2, h1⟩)

theorem childRegisters_cover {root : ℚ} (hr : 0 ≤ root) {k t : ℕ} (hk : 6 ≤ k)
    (hc : fastParams.minCapacity ≤ capacity fastParams root t 0)
    (pl : StoredPlacement k) (ha : AllocationInvariant root t pl) (hp : t % 2 = 0) :
    childRegisters pl hk 0 ∪ childRegisters pl hk 1 = univ := by
  have hd : 2 ∣ (upperRegisters pl (by omega)).card :=
    dvd_trans (by norm_num) (upperRegisters_dvd64 hr hk hc pl ha hp)
  unfold childRegisters
  norm_num only [Fin.val_zero, Fin.val_one]
  rw [union_union_union_comm, positionalBin_halves_cover _ hd,
    deep_assigned_halves_cover pl hk, upper_deep_complete hk pl ha hp]

theorem childRegisters_pure {root : ℚ} (hr : 0 ≤ root) {k t : ℕ} (hk : 6 ≤ k)
    (hc : fastParams.minCapacity ≤ capacity fastParams root t 0)
    (hceil : capacity fastParams root t 0 ≤ rootCeiling)
    (pl : StoredPlacement k) (ha : AllocationInvariant root t pl) (hp : t % 2 = 0)
    (w : Fin (2 ^ k) → Fin (2 ^ k)) (hw : Function.Injective w)
    (hi : Invariant fastParams (fun c ↦ capacity fastParams root t c.l) pl.regs w)
    (s : Fin 2) :
    let U := upperRegisters pl (by omega)
    let w' := ((bitonicNetwork U.card).scatterEmbed (2 ^ k) (U.orderEmbOfFin rfl)).exec w
    ∀ i ∈ childRegisters pl hk s, nativeBagIdx k 1 (w' i).val = s.val := by
  dsimp only
  intro i hiS
  rcases mem_union.mp hiS with hiU | hiD
  · exact upper_sorted_half_pure hr hk hc hceil pl ha hp w hw hi s i hiU
  · obtain ⟨hiD, hs⟩ := mem_filter.mp hiD
    have he : i ∉ deepErrors pl w 1 := by rw [deepErrors_one_empty hr hceil pl w hi]; simp
    have haLo := (deep_prefix_agreement hk (by omega : 1 ≤ 6) pl ha hp w s.val hiD he)
    have haHi := (deep_prefix_agreement hk (by omega : 1 ≤ 6) pl ha hp w (s.val + 1) hiD he)
    have hwrong : nativeBagIdx k 1 (w i).val = s.val := by
      obtain ⟨hsHi, hsLo⟩ := hs
      have hHi := haHi.mpr hsHi
      have hLo : ¬ nativeBagIdx k 1 (w i).val < s.val := fun h ↦ hsLo (haLo.mp h)
      omega
    have hout : i ∉ Set.range ((upperRegisters pl (by omega)).orderEmbOfFin rfl) := by
      rw [range_orderEmbOfFin]
      exact fun hu ↦ disjoint_left.mp (deepRegisters_disjoint_upper hk pl ha hp) hiD hu
    rw [ComparatorNetwork.scatterEmbed_exec_outside _ _ _ _ _ hout]
    exact hwrong

theorem childRegisters_eq_native {root : ℚ} (hr : 0 ≤ root) {k t : ℕ} (hk : 6 ≤ k)
    (hc : fastParams.minCapacity ≤ capacity fastParams root t 0)
    (hceil : capacity fastParams root t 0 ≤ rootCeiling)
    (pl : StoredPlacement k) (ha : AllocationInvariant root t pl) (hp : t % 2 = 0)
    (w : Fin (2 ^ k) → Fin (2 ^ k)) (hw : Function.Injective w)
    (hi : Invariant fastParams (fun c ↦ capacity fastParams root t c.l) pl.regs w)
    (s : Fin 2) :
    let U := upperRegisters pl (by omega)
    let w' := ((bitonicNetwork U.card).scatterEmbed (2 ^ k) (U.orderEmbOfFin rfl)).exec w
    childRegisters pl hk s = univ.filter
      (fun i ↦ (⟨1, s.val, by omega, s.isLt⟩ : Bag k).Native i w') := by
  dsimp only
  ext i
  constructor
  · intro hiS
    exact mem_filter.mpr ⟨mem_univ _, childRegisters_pure hr hk hc hceil pl ha hp w hw hi s i hiS⟩
  · intro hiN
    have htag := (mem_filter.mp hiN).2
    change nativeBagIdx k 1 _ = s.val at htag
    have hcover : i ∈ childRegisters pl hk 0 ∪ childRegisters pl hk 1 := by
      rw [childRegisters_cover hr hk hc pl ha hp]; exact mem_univ _
    rcases mem_union.mp hcover with hi0 | hi1
    · have ht := childRegisters_pure hr hk hc hceil pl ha hp w hw hi 0 i hi0
      have hs : s = 0 := Fin.ext (htag.symm.trans ht)
      simpa only [hs] using hi0
    · have ht := childRegisters_pure hr hk hc hceil pl ha hp w hw hi 1 i hi1
      have hs : s = 1 := Fin.ext (htag.symm.trans ht)
      simpa only [hs] using hi1

theorem childRegisters_card {root : ℚ} (hr : 0 ≤ root) {k t : ℕ} (hk : 6 ≤ k)
    (hc : fastParams.minCapacity ≤ capacity fastParams root t 0)
    (hceil : capacity fastParams root t 0 ≤ rootCeiling)
    (pl : StoredPlacement k) (ha : AllocationInvariant root t pl) (hp : t % 2 = 0)
    (w : Fin (2 ^ k) → Fin (2 ^ k)) (hw : Function.Injective w)
    (hi : Invariant fastParams (fun c ↦ capacity fastParams root t c.l) pl.regs w)
    (s : Fin 2) : (childRegisters pl hk s).card = 2 ^ (k - 1) := by
  rw [childRegisters_eq_native hr hk hc hceil pl ha hp w hw hi s,
    native_cohort_card _ _ (ComparatorNetwork.exec_injective _ hw)]
  change bagSize k 1 = 2 ^ (k - 1)
  exact Nat.pow_div (by omega) (by norm_num)

end Paterson.Bags
