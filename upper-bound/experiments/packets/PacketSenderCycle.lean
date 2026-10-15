import PacketRepair64
import PacketRebinning
import Mathlib.Logic.Equiv.Fin.Rotate

/-! Sender-local realization of the shifted half-packet repair on the actual
`WireFlow` port intervals. Parent port 64 and child ports 0,...,63 are fixed
independently of values. The complete packet partition and scalar-cycle
count bridge remain separate obligations. -/

namespace Chvatal.PacketAlignment

open Classical

def senderPort {N : Nat} (s : Finset (Fin N)) (up down : Nat) (i : Fin 65) :
    Finset (Fin N) :=
  if i.val < 64 then downSet s up down i.val else upSet s up

def senderRepairLeft {N : Nat} (s : Finset (Fin N)) (up down : Nat) (i : Fin 65) :
    Finset (Fin N) :=
  if i.val < 64 then blockOf s (up / 2 + i.val * down) (up / 2 + i.val * down + 32)
  else blockOf s (up / 2 - 32) (up / 2)

def senderRepairRight {N : Nat} (s : Finset (Fin N)) (up down : Nat) (i : Fin 65) :
    Finset (Fin N) :=
  if i.val < 64 then blockOf s (up / 2 + (i.val + 1) * down - 32)
    (up / 2 + (i.val + 1) * down)
  else blockOf s (s.card - up / 2) (s.card - up / 2 + 32)

def senderBoundaryCut (up down : Nat) (i : Fin 65) : Nat := up / 2 + i.val * down

def senderBoundaryPrefix {N : Nat} (s : Finset (Fin N)) (up down : Nat) (i : Fin 65) :
    Finset (Fin N) := blockOf s (senderBoundaryCut up down i - 32) (senderBoundaryCut up down i)

def senderBoundarySuffix {N : Nat} (s : Finset (Fin N)) (up down : Nat) (i : Fin 65) :
    Finset (Fin N) := blockOf s (senderBoundaryCut up down i) (senderBoundaryCut up down i + 32)

def senderBoundaryCell {N : Nat} (s : Finset (Fin N)) (up down : Nat) (i : Fin 65) :
    Finset (Fin N) := senderBoundaryPrefix s up down i ∪ senderBoundarySuffix s up down i

private theorem blockOf_adjacent_union {N : Nat} (s : Finset (Fin N)) (lo mid hi : Nat)
    (hl : lo ≤ mid) (hh : mid ≤ hi) :
    blockOf s lo mid ∪ blockOf s mid hi = blockOf s lo hi := by
  ext w
  simp only [Finset.mem_union, mem_blockOf]
  constructor
  · rintro (⟨hs, hlo, hmid⟩ | ⟨hs, hmid, hhi⟩)
    · exact ⟨hs, hlo, by omega⟩
    · exact ⟨hs, by omega, hhi⟩
  · rintro ⟨hs, hlo, hhi⟩
    by_cases hm : rankIn s w < mid
    · exact Or.inl ⟨hs, hlo, hm⟩
    · exact Or.inr ⟨hs, by omega, hhi⟩

theorem senderBoundaryCell_interval {N : Nat} (s : Finset (Fin N)) (up down : Nat) (i : Fin 65) :
    senderBoundaryCell s up down i =
      blockOf s (senderBoundaryCut up down i - 32) (senderBoundaryCut up down i + 32) := by
  exact blockOf_adjacent_union s _ _ _ (by omega) (by omega)

theorem senderBoundaryCut_residue (up down : Nat) (hshift : (up / 2) % 64 = 32)
    (hdiv : 64 ∣ down) (i : Fin 65) : (senderBoundaryCut up down i) % 64 = 32 := by
  have hm : (i.val * down) % 64 = 0 := Nat.mod_eq_zero_of_dvd (dvd_mul_of_dvd_right hdiv _)
  simp [senderBoundaryCut, Nat.add_mod, hshift, hm]

/-- Each of the 65 affected cells is one entire packet of the original rank
grid, despite being split between two outgoing ports. -/
theorem senderBoundaryCell_packet {N : Nat} (s : Finset (Fin N)) (up down : Nat)
    (hshift : (up / 2) % 64 = 32) (hdiv : 64 ∣ down) (i : Fin 65) :
    senderBoundaryCell s up down i = blockOf s
      (64 * (senderBoundaryCut up down i / 64))
      (64 * (senderBoundaryCut up down i / 64 + 1)) := by
  rw [senderBoundaryCell_interval]
  have hres := senderBoundaryCut_residue up down hshift hdiv i
  have he := Nat.mod_add_div (senderBoundaryCut up down i) 64
  rw [hres] at he
  congr 1 <;> omega

theorem senderBoundaryCells_disjoint {N : Nat} (s : Finset (Fin N)) (up down : Nat)
    (hd : 64 ≤ down) (i j : Fin 65) (hne : i ≠ j) :
    Disjoint (senderBoundaryCell s up down i) (senderBoundaryCell s up down j) := by
  rw [senderBoundaryCell_interval, senderBoundaryCell_interval]
  have hsep : ∀ a b : Fin 65, a.val < b.val →
      senderBoundaryCut up down a + 32 ≤ senderBoundaryCut up down b - 32 := by
    intro a b hab
    have hm : (a.val + 1) * down ≤ b.val * down := Nat.mul_le_mul_right down hab
    simp only [Nat.add_mul, Nat.one_mul] at hm
    dsimp [senderBoundaryCut]
    omega
  have hv : i.val ≠ j.val := fun h => hne (Fin.ext h)
  rcases lt_or_gt_of_ne hv with hlt | hlt
  · exact disjoint_blockOf (hsep i j hlt)
  · exact (disjoint_blockOf (hsep j i hlt)).symm

/-- The actual repair supports implement a cycle of complementary halves:
suffix i is paired with prefix (i+1 mod 65). The parent pair reverses their
physical listing, which has no effect on its support or total count. -/
theorem senderRepair_support_cycle {N : Nat} (s : Finset (Fin N)) (up down : Nat)
    (hs : s.card = up + 64 * down) (hu : 2 ∣ up) (i : Fin 65) :
    senderRepairLeft s up down i ∪ senderRepairRight s up down i =
      senderBoundarySuffix s up down i ∪ senderBoundaryPrefix s up down (finRotate 65 i) := by
  by_cases hi : i.val < 64
  · have hr : finRotate 65 i = ⟨i.val + 1, by omega⟩ := finRotate_of_lt hi
    simp only [senderRepairLeft, senderRepairRight, if_pos hi, hr,
      senderBoundaryPrefix, senderBoundarySuffix, senderBoundaryCut, Fin.val_mk]
  · have hi64 : i.val = 64 := by have := i.isLt; omega
    have hiLast : i = Fin.last 64 := Fin.ext hi64
    have hr : finRotate 65 i = 0 := by rw [hiLast, finRotate_last]
    have hueq : up / 2 * 2 = up := Nat.div_mul_cancel hu
    have he : s.card - up / 2 = up / 2 + 64 * down := by omega
    simp only [senderRepairLeft, senderRepairRight, if_neg hi, hr,
      senderBoundaryPrefix, senderBoundarySuffix, senderBoundaryCut, hi64, Fin.val_zero,
      Nat.zero_mul, Nat.add_zero, he]
    exact Finset.union_comm _ _

/-- All boundary halves are consumed exactly once at the support level:
the union of repaired pairs equals the union of original boundary packets. -/
theorem senderRepair_boundary_cover {N : Nat} (s : Finset (Fin N)) (up down : Nat)
    (hs : s.card = up + 64 * down) (hu : 2 ∣ up) :
    Finset.univ.biUnion (fun i : Fin 65 => senderRepairLeft s up down i ∪ senderRepairRight s up down i) =
      Finset.univ.biUnion (fun i : Fin 65 => senderBoundaryCell s up down i) := by
  ext w
  simp only [Finset.mem_biUnion, Finset.mem_univ, true_and,
    senderRepair_support_cycle s up down hs hu, senderBoundaryCell, Finset.mem_union]
  constructor
  · rintro ⟨i, hi | hi⟩
    · exact ⟨i, Or.inr hi⟩
    · exact ⟨finRotate 65 i, Or.inl hi⟩
  · rintro ⟨i, hi | hi⟩
    · refine ⟨(finRotate 65).symm i, Or.inr ?_⟩
      simpa only [Equiv.apply_symm_apply] using hi
    · exact ⟨i, Or.inl hi⟩

private theorem sender_down_bounds {N : Nat} (s : Finset (Fin N))
    (up down j : Nat) (hs : s.card = up + 64 * down) (hj : j < 64) (hd : 64 ≤ down) :
    64 ≤ (up / 2 + (j + 1) * down) - (up / 2 + j * down) ∧
      up / 2 + (j + 1) * down ≤ s.card := by
  have hmul : (j + 1) * down ≤ 64 * down := Nat.mul_le_mul_right down hj
  simp only [Nat.add_mul, Nat.one_mul] at hmul ⊢
  omega

theorem senderRepair_pair_properties {N : Nat} (s : Finset (Fin N)) (up down : Nat)
    (hs : s.card = up + 64 * down) (hu : 2 ∣ up) (hc : 64 ∣ s.card)
    (hshift : (up / 2) % 64 = 32) (hd : 64 ≤ down) (i : Fin 65) :
    (senderRepairLeft s up down i).card = 32 ∧
      (senderRepairRight s up down i).card = 32 ∧
      ∀ a ∈ senderRepairLeft s up down i, ∀ b ∈ senderRepairRight s up down i, a < b := by
  by_cases hi : i.val < 64
  · have hb := sender_down_bounds s up down i.val hs hi hd
    have hp := rankInterval_endpoint_pair s (up / 2 + i.val * down)
      (up / 2 + (i.val + 1) * down) hb.1 hb.2
    simp only [senderRepairLeft, senderRepairRight, if_pos hi]
    refine ⟨hp.2.1, hp.2.2.1, ?_⟩
    intro a ha b hb'
    exact rankInterval_endpoint_pair_ordered s _ _ hb.1 ha hb'
  · have hup : up ≤ s.card := by omega
    have hp := upFringe_endpoint_pair s up hu hc hshift hup
    simp only [senderRepairLeft, senderRepairRight, if_neg hi]
    refine ⟨hp.2.1, hp.2.2.1, ?_⟩
    intro a ha b hb
    exact upFringe_endpoint_pair_ordered s up hu hshift hup ha hb

theorem senderRepair_subset_port {N : Nat} (s : Finset (Fin N)) (up down : Nat)
    (hs : s.card = up + 64 * down) (hshift : (up / 2) % 64 = 32)
    (hd : 64 ≤ down) (i : Fin 65) :
    senderRepairLeft s up down i ∪ senderRepairRight s up down i ⊆ senderPort s up down i := by
  have hhalf : 32 ≤ up / 2 := by omega
  by_cases hi : i.val < 64
  · simp only [senderRepairLeft, senderRepairRight, senderPort, if_pos hi]
    intro w hw
    rcases Finset.mem_union.mp hw with hw | hw
    · have h := mem_blockOf.mp hw
      apply mem_blockOf.mpr
      rw [Nat.add_mul, Nat.one_mul]
      exact ⟨h.1, h.2.1, by omega⟩
    · have h := mem_blockOf.mp hw
      apply mem_blockOf.mpr
      rw [Nat.add_mul, Nat.one_mul] at h ⊢
      exact ⟨h.1, by omega, h.2.2⟩
  · simp only [senderRepairLeft, senderRepairRight, senderPort, if_neg hi]
    intro w hw
    rcases Finset.mem_union.mp hw with hw | hw
    · have h := mem_blockOf.mp hw
      exact Finset.mem_union_left _ (mem_blockOf.mpr ⟨h.1, by omega, h.2.2⟩)
    · have h := mem_blockOf.mp hw
      exact Finset.mem_union_right _ (mem_blockOf.mpr ⟨h.1, h.2.1, by omega⟩)

theorem senderPorts_disjoint {N : Nat} (s : Finset (Fin N)) (up down : Nat)
    (hs : s.card = up + 64 * down) (hu : 2 ∣ up) (i j : Fin 65) (hne : i ≠ j) :
    Disjoint (senderPort s up down i) (senderPort s up down j) := by
  by_cases hi : i.val < 64 <;> by_cases hj : j.val < 64
  · simp only [senderPort, if_pos hi, if_pos hj]
    have hv : i.val ≠ j.val := fun h => hne (Fin.ext h)
    rcases lt_or_gt_of_ne hv with hlt | hlt
    · exact disjoint_downSet hlt
    · exact (disjoint_downSet hlt).symm
  · simp only [senderPort, if_pos hi, if_neg hj]
    exact (disjoint_upSet_downSet hs hu hi).symm
  · simp only [senderPort, if_neg hi, if_pos hj]
    exact disjoint_upSet_downSet hs hu hj
  · have hi' := i.isLt
    have hj' := j.isLt
    exact False.elim (hne (Fin.ext (by omega)))

theorem senderRepair_inputs_sorted {N : Nat} {α : Type} [Preorder α]
    (s : Finset (Fin N)) (up down : Nat) (v : Fin N → α)
    (hs : s.card = up + 64 * down) (hc : 64 ∣ s.card)
    (hshift : (up / 2) % 64 = 32) (hd : 64 ≤ down) (hdiv : 64 ∣ down)
    (hp : PacketSortedOn s v) (i : Fin 65) :
    RankSortedOn (senderRepairLeft s up down i) v ∧
      RankSortedOn (senderRepairRight s up down i) v := by
  by_cases hi : i.val < 64
  · have hb := sender_down_bounds s up down i.val hs hi hd
    have hr := downSet_cut_residues (π := up) (j := i.val) hdiv
    rw [hshift] at hr
    simpa only [senderRepairLeft, senderRepairRight, if_pos hi] using
      packetSortedOn_rankInterval_endpoints s v hp _ _ hb.1 hr.1 hr.2
  · simpa only [senderRepairLeft, senderRepairRight, if_neg hi] using
      packetSortedOn_upFringe_endpoints s v hp up hc hshift (by omega)

/-- One fixed six-layer network simultaneously repairs the boundary pair of
every actual sender port, under only the source packet-sorted premise. -/
theorem senderRepair_exists {N : Nat} (s : Finset (Fin N)) (up down : Nat)
    (hs : s.card = up + 64 * down) (hu : 2 ∣ up) (hc : 64 ∣ s.card)
    (hshift : (up / 2) % 64 = 32) (hd : 64 ≤ down) (hdiv : 64 ∣ down) :
    ∃ net : ComparatorNetwork N, net.depth ≤ 6 ∧
      (∀ {α : Type} [LinearOrder α] (v : Fin N → α), PacketSortedOn s v →
        ∀ i : Fin 65, RankSortedOn
          (senderRepairLeft s up down i ∪ senderRepairRight s up down i) (net.exec v)) ∧
      (∀ {α : Type} [LinearOrder α] (v : Fin N → α) (w : Fin N),
        w ∉ Finset.univ.biUnion (fun i : Fin 65 => senderBoundaryCell s up down i) →
        net.exec v w = v w) := by
  let A := senderRepairLeft s up down
  let B := senderRepairRight s up down
  have hA : ∀ i, (A i).card = 32 := fun i =>
    (senderRepair_pair_properties s up down hs hu hc hshift hd i).1
  have hB : ∀ i, (B i).card = 32 := fun i =>
    (senderRepair_pair_properties s up down hs hu hc hshift hd i).2.1
  have hsep : ∀ i, ∀ a ∈ A i, ∀ b ∈ B i, a < b := fun i =>
    (senderRepair_pair_properties s up down hs hu hc hshift hd i).2.2
  have hdis : ∀ i ∈ List.finRange 65, ∀ j ∈ List.finRange 65,
      i ≠ j → Disjoint (A i ∪ B i) (A j ∪ B j) := by
    intro i _ j _ hne
    exact (senderPorts_disjoint s up down hs hu i j hne).mono
      (senderRepair_subset_port s up down hs hshift hd i)
      (senderRepair_subset_port s up down hs hshift hd j)
  refine ⟨parallelHalfPairRepair (List.finRange 65) A B hA hB hsep,
    parallelHalfPairRepair_depth_le _ (List.nodup_finRange 65) A B hA hB hsep hdis, ?_, ?_⟩
  · intro α _ v hp i
    obtain ⟨hl, hr⟩ := senderRepair_inputs_sorted s up down v hs hc hshift hd hdiv hp i
    exact parallelHalfPairRepair_sorts_pair _ (List.nodup_finRange 65) A B hA hB hsep hdis
      v i (List.mem_finRange i) hl hr
  · intro α _ v w hw
    unfold parallelHalfPairRepair repairOrderedHalfPair
    rw [ComparatorNetwork.exec_flatMap]
    apply ComparatorNetwork.foldl_exec_outside
    intro i _ c hc'
    apply ComparatorNetwork.scatterEmbed_comparators_outside (oddEvenMergeNet 6) N
      (orderedHalfPairEmbedding (A i) (B i) (hA i) (hB i) (hsep i)) w ?_ c hc'
    intro hwrange
    have hwpair : w ∈ A i ∪ B i := by
      rwa [orderedHalfPairEmbedding_range] at hwrange
    have hwAll : w ∈ Finset.univ.biUnion (fun j : Fin 65 =>
        senderRepairLeft s up down j ∪ senderRepairRight s up down j) :=
      Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, hwpair⟩
    rw [senderRepair_boundary_cover s up down hs hu] at hwAll
    exact hw hwAll

/-- In a sorted Boolean packet, the prefix half contains `(x-m)_+` true
entries and the suffix half contains `min(m,x)`. This links the scalar
rebinning functions to actual sorted packet values. -/
theorem sorted_bool_halves_trueCount {m : Nat} (v : Fin (m + m) → Bool)
    (hv : Monotone v) :
    boolTrueCount (fun i : Fin m => v (Fin.castAdd m i)) = boolTrueCount v - m ∧
      boolTrueCount (fun i : Fin m => v (Fin.natAdd m i)) = min m (boolTrueCount v) := by
  by_cases hm : m = 0
  · subst m
    simp [boolTrueCount]
  have hmpos : 0 < m := by omega
  let mid : Fin (m + m) := ⟨m - 1, by omega⟩
  have hsum := boolTrueCount_halves v
  have hbound (f : Fin m → Bool) : boolTrueCount f ≤ m := by
    simpa [boolTrueCount] using Fintype.card_subtype_le (fun i : Fin m => f i = true)
  cases hmid : v mid with
  | false =>
    have he : (fun i : Fin m => v (Fin.castAdd m i)) = fun _ => false := by
      funext i
      have hi := i.isLt
      have hmono := hv (show Fin.castAdd m i ≤ mid from Fin.mk_le_mk.mpr (by omega))
      rw [hmid] at hmono
      exact le_antisymm hmono (Bool.false_le _)
    have hzero : boolTrueCount (fun i : Fin m => v (Fin.castAdd m i)) = 0 := by
      rw [he]
      simp [boolTrueCount]
    have hb := hbound (fun i : Fin m => v (Fin.natAdd m i))
    constructor
    · omega
    · rw [Nat.min_eq_right (by omega)]
      omega
  | true =>
    have he : (fun i : Fin m => v (Fin.natAdd m i)) = fun _ => true := by
      funext i
      have hi := i.isLt
      have hmono := hv (show mid ≤ Fin.natAdd m i from Fin.mk_le_mk.mpr (by omega))
      rw [hmid] at hmono
      exact le_antisymm (Bool.le_true _) hmono
    have hfull : boolTrueCount (fun i : Fin m => v (Fin.natAdd m i)) = m := by
      rw [he]
      simp [boolTrueCount]
    constructor
    · omega
    · rw [Nat.min_eq_left (by omega)]
      exact hfull

/-- The ordinary scheduled, shifted sender has a fixed six-layer repair.
The positivity premise excludes the degenerate zero-down-size case. -/
theorem scheduled_senderRepair_exists (d : Nat) (hd : 7 ≤ d) (t : Nat)
    (ht2 : 2 ≤ t) (ht : t < tf7 d) (b : KBag 64 d)
    (hshift : flowUp7 d hd b.l t / 2 % 64 = 32)
    (hpos : 0 < flowDown7 d hd b.l t) :
    let s := wireSets (flowSizes7 d hd) t b
    let up := flowUp7 d hd b.l t
    let down := flowDown7 d hd b.l t
    ∃ net : ComparatorNetwork (64 ^ d), net.depth ≤ 6 ∧
      (∀ {α : Type} [LinearOrder α] (v : Fin (64 ^ d) → α), PacketSortedOn s v →
        ∀ i : Fin 65, RankSortedOn
          (senderRepairLeft s up down i ∪ senderRepairRight s up down i) (net.exec v)) ∧
      (∀ {α : Type} [LinearOrder α] (v : Fin (64 ^ d) → α) (w : Fin (64 ^ d)),
        w ∉ Finset.univ.biUnion (fun i : Fin 65 => senderBoundaryCell s up down i) →
        net.exec v w = v w) := by
  dsimp only
  have hr := refined_packet_residues hd ht2 ht (node_shape_refined d hd t b.l ht2 ht)
  have hc : 64 ∣ (wireSets (flowSizes7 d hd) t b).card := by
    rw [wireSets_card _ (Nat.le_of_lt ht)]
    exact hr.1
  apply senderRepair_exists _ _ _ ?_ ?_ hc hshift (Nat.le_of_dvd hpos hr.2.1) hr.2.1
  · rw [wireSets_card _ (Nat.le_of_lt ht)]
    exact (flowSizes7 d hd).hsplit b.l t b.hl ht
  · exact (flowSizes7 d hd).hup_even b.l t ht

end Chvatal.PacketAlignment
