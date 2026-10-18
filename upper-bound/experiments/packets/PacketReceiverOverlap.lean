import PacketInduction
import PacketHalfProfile

/-! Recovered receiver-overlap lemmas.  This source was accidentally truncated;
the proofs below rebuild the physical 4096-wire sorter and its partial-group
interface from the current checked packet modules. -/

namespace Chvatal.PacketAlignment

open Chvatal
open Classical

set_option maxRecDepth 8192
set_option maxHeartbeats 800000

/-- Sort any 4096-wire support in increasing physical-wire order with the
12-bitonic sorter. -/
def bitonicSort4096OnSupport {N : Nat} (S : Finset (Fin N))
    (hcard : S.card = 4096) : ComparatorNetwork N :=
  (Bitonic.bitonicSort 12).scatterEmbed N (S.orderEmbOfFin hcard)

theorem bitonicSort4096OnSupport_depth_le {N : Nat} (S : Finset (Fin N))
    (hcard : S.card = 4096) : (bitonicSort4096OnSupport S hcard).depth ≤ 78 := by
  unfold bitonicSort4096OnSupport
  exact (depth_scatterEmbed_le (Bitonic.bitonicSort 12) N (S.orderEmbOfFin hcard)).trans (by
    have h := Bitonic.bitonicSort_depth_le_budget 12
    norm_num [bitonicDepthBudget] at h
    exact h)

theorem bitonicSort4096OnSupport_rankSorted {N : Nat} {α : Type}
    [LinearOrder α] (S : Finset (Fin N)) (hcard : S.card = 4096)
    (v : Fin N → α) : RankSortedOn S ((bitonicSort4096OnSupport S hcard).exec v) := by
  intro x y hx hy hxy
  let e := S.orderEmbOfFin hcard
  have hsort : Monotone ((Bitonic.bitonicSort 12).exec (v ∘ e)) :=
    (Bitonic.bitonicSort_sorts 12) α (v ∘ e)
  have hxrange : (x : Fin N) ∈ Set.range e := by
    rw [Finset.range_orderEmbOfFin]
    exact hx
  have hyrange : (y : Fin N) ∈ Set.range e := by
    rw [Finset.range_orderEmbOfFin]
    exact hy
  obtain ⟨i, hi⟩ := Set.mem_range.mp hxrange
  obtain ⟨j, hj⟩ := Set.mem_range.mp hyrange
  have hij : i ≤ j := e.le_iff_le.mp (by simpa [hi, hj] using hxy)
  have hresult := hsort hij
  rw [← hi, ← hj]
  change ((Bitonic.bitonicSort 12).scatterEmbed N e).exec v (e i) ≤
    ((Bitonic.bitonicSort 12).scatterEmbed N e).exec v (e j)
  rw [ComparatorNetwork.scatterEmbed_exec_inside,
    ComparatorNetwork.scatterEmbed_exec_inside]
  exact hresult

/-- The grouped output of a four-lane boundary round has each 4096-wire
macroblock on its exact physical rank interval; sort that support physically. -/
theorem fourLaneBoundaryMatching_4096Block_physicalSort
    {r N : Nat} {α : Type} [LinearOrder α] {support : Finset (Fin N)}
    (state : IndexedPacketPhysicalRoundState (8 * (8 * r)) N α support)
    (hblockOrdered : ∀ i j, i.val / 4 < j.val / 4 → ∀ x y : Fin 64,
      state.packets i x < state.packets j y) (j : Fin r) :
    ∃ next : IndexedPacketPhysicalRoundState (8 * (8 * r)) N α support,
      next.packets = fourLaneBoundaryGroupedOutput state.packets state.disjoint ∧
      ∃ hcard : (Chvatal.blockOf support (4096 * j.val)
          (4096 * (j.val + 1))).card = 4096,
        (bitonicSort4096OnSupport
          (Chvatal.blockOf support (4096 * j.val) (4096 * (j.val + 1))) hcard).depth ≤ 78 ∧
        RankSortedOn (Chvatal.blockOf support (4096 * j.val)
          (4096 * (j.val + 1)))
          ((bitonicSort4096OnSupport
            (Chvatal.blockOf support (4096 * j.val) (4096 * (j.val + 1))) hcard).exec
            next.values) ∧
        ∀ p : Fin 64,
          RankSortedOn (Chvatal.blockOf support (4096 * j.val + 64 * p.val)
            (4096 * j.val + 64 * (p.val + 1)))
            ((bitonicSort4096OnSupport
              (Chvatal.blockOf support (4096 * j.val) (4096 * (j.val + 1))) hcard).exec
              next.values) := by
  obtain ⟨next, hpackets, hvalues, hdepth⟩ :=
    fourLaneBoundaryMatching_preservesGroupedPhysicalState state hblockOrdered
  refine ⟨next, hpackets, ?_⟩
  have hsupportCard : support.card = 4096 * r := by
    have hdisj : ∀ i k, i ≠ k →
        Disjoint (packetEmbeddingSupport (state.packets i))
          (packetEmbeddingSupport (state.packets k)) := by
      intro i k hik
      apply Finset.disjoint_left.mpr
      intro w hw hw'
      obtain ⟨x, hx⟩ := (packetEmbeddingSupport_mem_iff (state.packets i) w).mp hw
      obtain ⟨y, hy⟩ := (packetEmbeddingSupport_mem_iff (state.packets k) w).mp hw'
      exact state.disjoint i k hik x y (hx.trans hy.symm)
    have hpair : ((Finset.univ : Finset (Fin (8 * (8 * r)))) : Set (Fin (8 * (8 * r)))).PairwiseDisjoint
        (fun i => packetEmbeddingSupport (state.packets i)) := by
      intro i hi k hk hik
      exact hdisj i k hik
    rw [← state.support_eq, Finset.card_biUnion hpair]
    simp [packetEmbeddingSupport_card]
    ring
  have hcard : (Chvatal.blockOf support (4096 * j.val)
      (4096 * (j.val + 1))).card = 4096 := by
    rw [Chvatal.blockOf_card (by rw [hsupportCard]; omega)]
    rw [Nat.mul_add]
    omega
  refine ⟨hcard, bitonicSort4096OnSupport_depth_le _ hcard,
    bitonicSort4096OnSupport_rankSorted _ hcard next.values, ?_⟩
  intro p
  apply rankSortedOn_subset (s := Chvatal.blockOf support
      (4096 * j.val) (4096 * (j.val + 1)))
  · intro w hw
    have hmem := Chvatal.mem_blockOf.mp hw
    apply Chvatal.mem_blockOf.mpr
    refine ⟨hmem.1, ?_, ?_⟩ <;> omega
  · exact bitonicSort4096OnSupport_rankSorted _ hcard next.values

/-- Every stream's full 4096-rank groups are contained in the receiver, and
at most two such groups can be cut by any one receiver rank interval. -/
theorem flowA7_receiver_regular_partial_groups_bound {d : Nat} {α : Type}
    [LinearOrder α] (hd : 7 ≤ d) (t : Nat) (ht2 : 2 ≤ t)
    (ht : t < Chvatal.tf7 d) (b : Chvatal.KBag 64 d) (hb : 1 ≤ b.l)
    (hchildLevel : b.l < d) (v : Fin (64 ^ d) → α)
    (hpack : ∀ q : Chvatal.KBag 64 d,
      PacketSortedOn (Chvatal.wireSets (Chvatal.flowSizes7 d hd) t q) v) :
    ∃ stream : (Unit ⊕ Fin 64 × Bool) → CanonicalPacketFamily (64 ^ d),
    ∃ endpoint : (Unit ⊕ Fin 64) → Finset (Fin (64 ^ d)),
    ∃ D : CanonicalStreamFullBlockData stream
      (fun i => Finset.univ.biUnion (stream i).packet)
      ((flowA7_sourcePortRepairStage hd t ht2 ht).exec v),
      (∀ i, ∃ base,
        (∀ g : Fin (D.fullGroups i),
          Chvatal.blockOf (flowA7_receiver_streamSourceSupport hd t b hchildLevel i)
            (base + 4096 * g.val) (base + 4096 * (g.val + 1)) ⊆
              Chvatal.wireSets (Chvatal.flowSizes7 d hd) (t + 1) b) ∧
        ∀ lo hi, lo ≤ hi →
          hi ≤ (Chvatal.wireSets (Chvatal.flowSizes7 d hd) (t + 1) b).card →
          (partialRankIntervalIndices
            (flowA7_receiver_streamSourceSupport hd t b hchildLevel i)
            (Chvatal.wireSets (Chvatal.flowSizes7 d hd) (t + 1) b)
            base lo hi (D.fullGroups i)).card ≤ 2) ∧
      (Finset.univ.biUnion fun i => Finset.univ.biUnion (stream i).packet) ∪
        Finset.univ.biUnion endpoint =
          Chvatal.wireSets (Chvatal.flowSizes7 d hd) (t + 1) b := by
  classical
  obtain ⟨stream, endpoint, D, hcontract, hintervals, hindexed, hcover⟩ :=
    flowA7_receiver_regularFullBlocks_rankIntervals hd t ht2 ht b hb hchildLevel v hpack
  let T := Chvatal.wireSets (Chvatal.flowSizes7 d hd) (t + 1) b
  let source := flowA7_receiver_streamSourceSupport hd t b hchildLevel
  have hstream (i) : Finset.univ.biUnion (stream i).packet ⊆ T := by
    intro w hw
    have hm : w ∈
        (Finset.univ.biUnion fun i => Finset.univ.biUnion (stream i).packet) ∪
          Finset.univ.biUnion endpoint := by
      apply Finset.mem_union.mpr
      left
      exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, hw⟩
    rw [hcover] at hm
    exact hm
  refine ⟨stream, endpoint, D, ?_, hcover⟩
  intro i
  obtain ⟨base, hcells, hgroups⟩ := hindexed i
  refine ⟨base, ?_, ?_⟩
  · intro g
    obtain ⟨e, he, hrange⟩ := hgroups g
    intro w hw
    have hrange : w ∈ Set.range e := by
      rw [hrange]
      exact hw
    have hs := (D.block_subset_support i e he) hrange
    exact hstream i hs
  · intro lo hi hlo hhi
    by_cases hzero : D.fullGroups i = 0
    · rw [hzero]
      simp [partialRankIntervalIndices]
    · have hcomplete := D.rankCellStream_complete i (source i) base
        (hcontract i) hcells (by omega)
      apply partialRankIntervalIndices_card_le_two
        (source i) T base lo hi (D.fullGroups i) hcomplete
      intro g w hw
      obtain ⟨e, he, hrange⟩ := hgroups g
      have hrange : w ∈ Set.range e := by
        rw [hrange]
        exact hw
      exact hstream i ((D.block_subset_support i e he) hrange)

/-- Summing the per-stream bound gives at most 258 partially intersected
groups: there are 129 parent/child streams and each contributes at most two. -/
theorem flowA7_receiver_regular_partial_groups_sum_le_258 {d : Nat} {α : Type}
    [LinearOrder α] (hd : 7 ≤ d) (t : Nat) (ht2 : 2 ≤ t)
    (ht : t < Chvatal.tf7 d) (b : Chvatal.KBag 64 d) (hb : 1 ≤ b.l)
    (hchildLevel : b.l < d) (v : Fin (64 ^ d) → α)
    (hpack : ∀ q : Chvatal.KBag 64 d,
      PacketSortedOn (Chvatal.wireSets (Chvatal.flowSizes7 d hd) t q) v)
    (lo hi : Nat) (hlo : lo ≤ hi)
    (hhi : hi ≤ (Chvatal.wireSets (Chvatal.flowSizes7 d hd) (t + 1) b).card) :
    ∃ stream : (Unit ⊕ Fin 64 × Bool) → CanonicalPacketFamily (64 ^ d),
    ∃ endpoint : (Unit ⊕ Fin 64) → Finset (Fin (64 ^ d)),
    ∃ D : CanonicalStreamFullBlockData stream
      (fun i => Finset.univ.biUnion (stream i).packet)
      ((flowA7_sourcePortRepairStage hd t ht2 ht).exec v),
    ∃ base : (Unit ⊕ Fin 64 × Bool) → Nat,
      (∀ i (g : Fin (D.fullGroups i)), Chvatal.blockOf (flowA7_receiver_streamSourceSupport hd t b hchildLevel i)
        (base i + 4096 * g.val) (base i + 4096 * (g.val + 1)) ⊆
          Chvatal.wireSets (Chvatal.flowSizes7 d hd) (t + 1) b) ∧
      (∑ i, (partialRankIntervalIndices
        (flowA7_receiver_streamSourceSupport hd t b hchildLevel i)
        (Chvatal.wireSets (Chvatal.flowSizes7 d hd) (t + 1) b)
        (base i) lo hi (D.fullGroups i)).card) ≤ 258 ∧
      (Finset.univ.biUnion fun i => Finset.univ.biUnion (stream i).packet) ∪
        Finset.univ.biUnion endpoint =
          Chvatal.wireSets (Chvatal.flowSizes7 d hd) (t + 1) b := by
  classical
  obtain ⟨stream, endpoint, D, hbound, hcover⟩ :=
    flowA7_receiver_regular_partial_groups_bound hd t ht2 ht b hb hchildLevel v hpack
  let base : (Unit ⊕ Fin 64 × Bool) → Nat := fun i => Classical.choose (hbound i)
  have hparts (i) := Classical.choose_spec (hbound i)
  refine ⟨stream, endpoint, D, base, ?_, ?_, hcover⟩
  · intro i g
    exact (hparts i).1 g
  · calc
      (∑ i, (partialRankIntervalIndices
        (flowA7_receiver_streamSourceSupport hd t b hchildLevel i)
        (Chvatal.wireSets (Chvatal.flowSizes7 d hd) (t + 1) b)
        (base i) lo hi (D.fullGroups i)).card) ≤
        ∑ _i : (Unit ⊕ Fin 64 × Bool), 2 :=
          Finset.sum_le_sum fun i _ => (hparts i).2 lo hi hlo hhi
      _ = 258 := by simp [Fintype.card_sum, Fintype.card_unique, Fintype.card_fin]

end Chvatal.PacketAlignment
