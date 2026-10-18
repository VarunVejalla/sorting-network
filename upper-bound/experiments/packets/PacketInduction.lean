import PacketRepair64
import PacketGenMerge
import PacketMergeTreeGen
import AKS.Chvatal.RealBlocks
import Mathlib.Data.List.Perm.Subperm

/-! Canonical finite-index bridge from one generalized matching round to the
packet-family interface used by receiver induction. This file tracks logical
packet embeddings; it does not identify them with later positional
`WireFlow` cuts. -/

namespace Chvatal.PacketAlignment

/-- If a finite support is partitioned into equal-size blocks that are strictly
ordered by block index, every point of block `j` has exactly the rank range
reserved for that block. -/
theorem orderedEqualBlocks_rankIn_bounds {k n q : Nat}
    (S : Finset (Fin n)) (B : Fin k → Finset (Fin n))
    (j : Fin k) (w : Fin n)
    (hcover : ∀ z, z ∈ S ↔ ∃ i, z ∈ B i)
    (hdisj : ∀ i l, i ≠ l → Disjoint (B i) (B l))
    (hcard : ∀ i, (B i).card = q)
    (hordered : ∀ i l, i.val < l.val → ∀ x ∈ B i, ∀ y ∈ B l, x < y)
    (hw : w ∈ B j) :
    q * j.val ≤ Chvatal.rankIn S w ∧
      Chvatal.rankIn S w < q * (j.val + 1) := by
  classical
  let before := Finset.Iio j
  let through := Finset.Iic j
  let low := S.filter (fun z => z < w)
  let beforeBlocks := before.biUnion B
  let throughBlocks := through.biUnion B
  have hbeforeCard : before.card = j.val := by
    simp [before]
  have hthroughCard : through.card = j.val + 1 := by
    simp [through]
  have hbeforeDisj : ∀ i ∈ before, ∀ l ∈ before,
      i ≠ l → Disjoint (B i) (B l) := by
    intro i _ l _ hil
    exact hdisj i l hil
  have hthroughDisj : ∀ i ∈ through, ∀ l ∈ through,
      i ≠ l → Disjoint (B i) (B l) := by
    intro i _ l _ hil
    exact hdisj i l hil
  have hbeforeBlocksCard : beforeBlocks.card = q * j.val := by
    rw [Finset.card_biUnion hbeforeDisj]
    simp_rw [hcard]
    simp [hbeforeCard, Nat.mul_comm]
  have hthroughBlocksCard : throughBlocks.card = q * (j.val + 1) := by
    rw [Finset.card_biUnion hthroughDisj]
    simp_rw [hcard]
    simp [hthroughCard, Nat.mul_comm]
  have hbeforeSubset : beforeBlocks ⊆ low := by
    intro z hz
    rcases Finset.mem_biUnion.mp hz with ⟨i, hi, hzi⟩
    have hij : i.val < j.val := by simpa [before] using hi
    apply Finset.mem_filter.mpr
    refine ⟨(hcover z).2 ⟨i, hzi⟩, ?_⟩
    exact hordered i j hij z hzi w hw
  have hlowCardLower : q * j.val ≤ low.card := by
    calc
      q * j.val = beforeBlocks.card := hbeforeBlocksCard.symm
      _ ≤ low.card := Finset.card_le_card hbeforeSubset
  have hlowSubset : low ⊆ throughBlocks := by
    intro z hz
    have hzS := (Finset.mem_filter.mp hz).1
    have hzw := (Finset.mem_filter.mp hz).2
    rcases (hcover z).1 hzS with ⟨i, hzi⟩
    have hile : i.val ≤ j.val := by
      by_contra hnot
      have hji : j.val < i.val := by omega
      have horder := hordered j i hji w hw z hzi
      omega
    have hiThrough : i ∈ through := by simpa [through] using hile
    exact Finset.mem_biUnion.mpr ⟨i, hiThrough, hzi⟩
  have hwThrough : w ∈ throughBlocks := by
    have hjThrough : j ∈ through := by simp [through]
    exact Finset.mem_biUnion.mpr ⟨j, hjThrough, hw⟩
  have hwNotLow : w ∉ low := by
    simp [low]
  have hlowSSubset : low ⊂ throughBlocks := by
    refine Finset.ssubset_iff_subset_ne.mpr ⟨hlowSubset, ?_⟩
    intro heq
    have : w ∈ low := by simpa [heq] using hwThrough
    exact hwNotLow this
  have hlowCardUpper : low.card < q * (j.val + 1) := by
    calc
      low.card < throughBlocks.card := Finset.card_lt_card hlowSSubset
      _ = q * (j.val + 1) := hthroughBlocksCard
  constructor
  · simpa [low, Chvatal.rankIn] using hlowCardLower
  · simpa [low, Chvatal.rankIn] using hlowCardUpper

/-- Transpose 64 equal-length packet families into merge cohorts: the `k`th
packet from each of 64 sources becomes one 4096-wire block. Every cohort can
be sorted in the checked 57-layer batch, with disjointness and sorted output
preserved. This is the reindexing needed to group same-port packets across
the 64 children of an actual WireFlow receiver. -/
theorem packetFamily64_transpose_merge {c N : Nat} {α : Type}
    [LinearOrder α]
    (packets : Fin 64 → Fin c → Fin 64 ↪ Fin N)
    (hdis : ∀ j k j' k', (j, k) ≠ (j', k') → ∀ x y,
      packets j k x ≠ packets j' k' y)
    (v : Fin N → α)
    (hpackets : ∀ j k, Monotone (fun i => v (packets j k i))) :
    ∃ blocks : List (Fin 4096 ↪ Fin N),
      blocks.Nodup ∧
      (∀ e ∈ blocks, ∀ f ∈ blocks, e ≠ f → ∀ x y, e x ≠ f y) ∧
      (genScatterMergeTreeBatch (packetPowerTree6 (α := α)) blocks).depth ≤ 57 ∧
      (∀ e ∈ blocks, Monotone (fun i =>
        (genScatterMergeTreeBatch (packetPowerTree6 (α := α)) blocks).exec v (e i))) ∧
      (∀ e ∈ blocks, ∀ j : Fin (packetPowerTree6 (α := α)).leafCount,
        Monotone (fun i =>
          (genScatterMergeTreeBatch (packetPowerTree6 (α := α)) blocks).exec v
            (genScatterMergeTreeOutputEmbedding (packetPowerTree6 (α := α)) e j i))) ∧
      (∀ w, (∃ e ∈ blocks, w ∈ Set.range e) ↔
        ∃ j k x, packets j k x = w) := by
  let flat : Fin (c * 64) → Fin 64 ↪ Fin N := fun i =>
    packets ⟨i.val % 64, Nat.mod_lt _ (by norm_num)⟩
      ⟨i.val / 64, by have hi := i.isLt; omega⟩
  have hflatDis : ∀ a b, a ≠ b → ∀ x y, flat a x ≠ flat b y := by
    intro a b hab x y heq
    let ja : Fin 64 := ⟨a.val % 64, Nat.mod_lt _ (by norm_num)⟩
    let jb : Fin 64 := ⟨b.val % 64, Nat.mod_lt _ (by norm_num)⟩
    let ka : Fin c := ⟨a.val / 64, by have ha := a.isLt; omega⟩
    let kb : Fin c := ⟨b.val / 64, by have hb := b.isLt; omega⟩
    have hcoords : (ja, ka) ≠ (jb, kb) := by
      intro h
      have hj : ja.val = jb.val := congrArg Fin.val (congrArg Prod.fst h)
      have hk : ka.val = kb.val := congrArg Fin.val (congrArg Prod.snd h)
      apply hab
      apply Fin.ext
      have ha := Nat.mod_add_div a.val 64
      have hb := Nat.mod_add_div b.val 64
      dsimp [ja, jb, ka, kb] at hj hk
      omega
    exact hdis ja ka jb kb hcoords x y heq
  have hflatSorted : ∀ i, Monotone (fun k => v (flat i k)) := by
    intro i
    exact hpackets ⟨i.val % 64, Nat.mod_lt _ (by norm_num)⟩
      ⟨i.val / 64, by have hi := i.isLt; omega⟩
  let blocks := packetFamily64BlockList flat hflatDis
  refine ⟨blocks, packetFamily64BlockList_nodup flat hflatDis,
    packetFamily64BlockList_disjoint flat hflatDis,
    packetFamily64BlockList_merge_depth_le flat hflatDis,
    packetFamily64BlockList_merge_output_blockSorted flat hflatDis v hflatSorted,
    packetFamily64BlockList_merge_output_sorted flat hflatDis v hflatSorted, ?_⟩
  intro w
  rw [packetFamily64BlockList_support flat hflatDis w]
  constructor
  · rintro ⟨i, x, hix⟩
    let j : Fin 64 := ⟨i.val % 64, Nat.mod_lt _ (by norm_num)⟩
    let k : Fin c := ⟨i.val / 64, by have hi := i.isLt; omega⟩
    exact ⟨j, k, x, by simpa [flat, j, k] using hix⟩
  · rintro ⟨j, k, x, rfl⟩
    let i : Fin (c * 64) := ⟨k.val * 64 + j.val, by
      have hk := k.isLt
      have hj := j.isLt
      omega⟩
    have hmod : i.val % 64 = j.val := by dsimp [i]; omega
    have hdiv : i.val / 64 = k.val := by dsimp [i]; omega
    have hj : (⟨i.val % 64, Nat.mod_lt _ (by norm_num)⟩ : Fin 64) = j :=
      Fin.ext hmod
    have hk : (⟨i.val / 64, by have hi := i.isLt; omega⟩ : Fin c) = k :=
      Fin.ext hdiv
    exact ⟨i, x, by simp [flat, hj, hk]⟩

/-- Finset form of the transpose merge adapter. The input packet of index `k`
from child `j` is embedded in increasing wire order; packets are then grouped
across children at each fixed `k`. -/
theorem receiverChildFamilies_transpose_merge {c N : Nat} {α : Type}
    [LinearOrder α]
    (child : Fin 64 → Fin c → Finset (Fin N))
    (hcard : ∀ j k, (child j k).card = 64)
    (v : Fin N → α)
    (hsorted : ∀ j k, RankSortedOn (child j k) v)
    (hdis : ∀ j k j' k', (j, k) ≠ (j', k') → Disjoint (child j k) (child j' k')) :
    ∃ blocks : List (Fin 4096 ↪ Fin N),
      blocks.Nodup ∧
      (∀ e ∈ blocks, ∀ f ∈ blocks, e ≠ f → ∀ x y, e x ≠ f y) ∧
      (genScatterMergeTreeBatch (packetPowerTree6 (α := α)) blocks).depth ≤ 57 ∧
      (∀ e ∈ blocks, Monotone (fun i =>
        (genScatterMergeTreeBatch (packetPowerTree6 (α := α)) blocks).exec v (e i))) ∧
      (∀ e ∈ blocks, ∀ j : Fin (packetPowerTree6 (α := α)).leafCount,
        Monotone (fun i =>
          (genScatterMergeTreeBatch (packetPowerTree6 (α := α)) blocks).exec v
            (genScatterMergeTreeOutputEmbedding (packetPowerTree6 (α := α)) e j i))) ∧
      (∀ w, (∃ e ∈ blocks, w ∈ Set.range e) ↔
        ∃ j k, w ∈ child j k) := by
  let emb (j : Fin 64) (k : Fin c) : Fin 64 ↪ Fin N :=
    ((child j k).orderEmbOfFin (hcard j k)).toEmbedding
  have hdisEmb : ∀ j k j' k', (j, k) ≠ (j', k') → ∀ x y,
      emb j k x ≠ emb j' k' y := by
    intro j k j' k' hne x y heq
    have hx : emb j k x ∈ child j k := by
      change ((child j k).orderEmbOfFin (hcard j k)) x ∈ child j k
      exact Finset.orderEmbOfFin_mem (child j k) (hcard j k) x
    have hy : emb j' k' y ∈ child j' k' := by
      change ((child j' k').orderEmbOfFin (hcard j' k')) y ∈ child j' k'
      exact Finset.orderEmbOfFin_mem (child j' k') (hcard j' k') y
    have hx' : emb j k x ∈ child j' k' := by rw [heq]; exact hy
    exact (Finset.disjoint_left.mp (hdis j k j' k' hne) hx hx').elim
  have hsortedEmb : ∀ j k, Monotone (fun i => v (emb j k i)) := by
    intro j k x y hxy
    apply hsorted j k
    · change ((child j k).orderEmbOfFin (hcard j k)) x ∈ child j k
      exact Finset.orderEmbOfFin_mem (child j k) (hcard j k) x
    · change ((child j k).orderEmbOfFin (hcard j k)) y ∈ child j k
      exact Finset.orderEmbOfFin_mem (child j k) (hcard j k) y
    · exact Fin.le_def.mp
        (((child j k).orderEmbOfFin (hcard j k)).monotone hxy)
  obtain ⟨blocks, hnodup, hblocksDis, hdepth, hblockSorted, hsortedOut, hcover⟩ :=
    packetFamily64_transpose_merge emb hdisEmb v hsortedEmb
  refine ⟨blocks, hnodup, hblocksDis, hdepth, hblockSorted, hsortedOut, ?_⟩
  intro w
  rw [hcover]
  constructor
  · rintro ⟨j, k, i, hi⟩
    refine ⟨j, k, ?_⟩
    rw [← hi]
    exact Finset.orderEmbOfFin_mem (child j k) (hcard j k) i
  · rintro ⟨j, k, hw⟩
    have hw' : w ∈ Set.range (emb j k) := by
      change w ∈ Set.range ((child j k).orderEmbOfFin (hcard j k))
      rw [Finset.range_orderEmbOfFin]
      exact hw
    rcases hw' with ⟨i, hi⟩
    exact ⟨j, k, i, hi⟩

/-- A disjoint canonical partition into 64-wire packets has exactly one
packet per 64 wires. This converts the receiver's existential family size
into the scheduler's concrete packet count. -/
theorem canonicalPacketFamily_count_mul_64 {N : Nat}
    (P : CanonicalPacketFamily N) (support : Finset (Fin N))
    {α : Type} [LinearOrder α] (v : Fin N → α)
    (h : CanonicalPacketPortContract P support v) :
    P.count * 64 = support.card := by
  have hdis : ∀ i ∈ Finset.univ, ∀ j ∈ Finset.univ, i ≠ j →
      Disjoint (P.packet i) (P.packet j) := by
    intro i hi j hj hij
    exact h.2.2.1 i j hij
  rw [← h.2.1, Finset.card_biUnion hdis]
  simp [h.2.2.2]

/-- The physical support of a logical 64-wire packet embedding. -/
def packetEmbeddingSupport {N : Nat} (p : Fin 64 ↪ Fin N) : Finset (Fin N) :=
  Finset.univ.image p

theorem packetEmbeddingSupport_mem_iff {N : Nat} (p : Fin 64 ↪ Fin N)
    (w : Fin N) :
    w ∈ packetEmbeddingSupport p ↔ w ∈ Set.range p := by
  simp [packetEmbeddingSupport, Set.mem_range]

theorem packetEmbeddingSupport_card {N : Nat} (p : Fin 64 ↪ Fin N) :
    (packetEmbeddingSupport p).card = 64 := by
  rw [packetEmbeddingSupport, Finset.card_image_of_injective _ p.injective]
  simp

/-- Provenance retained from canonical packet grouping: each full block is
built from a specific consecutive group of 64 source packets. -/
structure CanonicalPacketFullBlockProvenance {N : Nat}
    (P : CanonicalPacketFamily N) (q r : Nat)
    (blocks : List (Fin 4096 ↪ Fin N)) where
  sourcePackets : Fin (q * 64) → Fin 64 ↪ Fin N
  sourceIndex : Fin (q * 64) → Fin P.count
  sourceIndex_val : ∀ a, (sourceIndex a).val = a.val
  sourceDisjoint : ∀ a b, a ≠ b → ∀ x y, sourcePackets a x ≠ sourcePackets b y
  sourceSupport : ∀ a,
    packetEmbeddingSupport (sourcePackets a) = P.packet (sourceIndex a)
  groupBlocks : Fin q → Fin 4096 ↪ Fin N
  groupBlock_eq : ∀ g,
    groupBlocks g = packetFamily64BlockEmbedding sourcePackets sourceDisjoint g
  blockList_eq : blocks = List.ofFn groupBlocks

/-- Grouping 64 consecutive 64-rank cells produces exactly one 4096-rank
interval in the same support. This is the rank-alignment adapter needed to
feed regular full blocks into port-local overlap estimates. -/
theorem packetFamily64BlockEmbedding_rankInterval_support {q N : Nat}
    (s : Finset (Fin N)) (lo : Nat)
    (packets : Fin (q * 64) → Fin 64 ↪ Fin N)
    (hdis : ∀ a b, a ≠ b → ∀ x y, packets a x ≠ packets b y)
    (hcell : ∀ a, Set.range (packets a) =
      (rankPacketCell s lo ⟨a.val, by have ha := a.isLt; omega⟩ : Set (Fin N)))
    (g : Fin q) (hfinish : lo + 4096 * (g.val + 1) ≤ s.card) :
    Set.range (packetFamily64BlockEmbedding packets hdis g) =
      (Chvatal.blockOf s (lo + 4096 * g.val)
        (lo + 4096 * (g.val + 1)) : Set (Fin N)) := by
  classical
  let groupedPackets : Fin 64 → Fin 64 ↪ Fin N := fun i =>
    packets (packetFamily64BlockIndex g i)
  have hlocalDis : ∀ i j, i ≠ j → ∀ x y, groupedPackets i x ≠ groupedPackets j y := by
    intro i j hij x y heq
    apply hdis (packetFamily64BlockIndex g i) (packetFamily64BlockIndex g j)
    · intro h
      exact hij (packetFamily64BlockIndex_injective g h)
    · exact heq
  have hmem (w : Fin N) :
      w ∈ Set.range (packetFamily64BlockEmbedding packets hdis g) ↔
        ∃ i : Fin 64, w ∈ Set.range (groupedPackets i) := by
    rw [Set.mem_range]
    constructor
    · rintro ⟨x, rfl⟩
      obtain ⟨i, j, hx⟩ := genPacketGroup64Embedding_mem_packets groupedPackets
        (by intro i j hij x y; exact hlocalDis i j hij x y) x
      exact ⟨i, ⟨j, hx.symm⟩⟩
    · rintro ⟨i, hi⟩
      obtain ⟨j, hx⟩ := hi
      obtain ⟨x, hxGroup⟩ := genPacketGroup64Embedding_covers_packets groupedPackets
        (by intro i j hij x y; exact hlocalDis i j hij x y) i j
      exact ⟨x, by
        simpa [packetFamily64BlockEmbedding, groupedPackets] using hxGroup.trans hx⟩
  apply Set.ext
  intro w
  rw [hmem]
  change (∃ i : Fin 64, w ∈ Set.range (groupedPackets i)) ↔
    w ∈ Chvatal.blockOf s (lo + 4096 * g.val) (lo + 4096 * (g.val + 1))
  rw [Chvatal.mem_blockOf]
  constructor
  · rintro ⟨i, hi⟩
    rw [hcell (packetFamily64BlockIndex g i)] at hi
    have hi' : w ∈ rankPacketCell s lo
        ⟨(packetFamily64BlockIndex g i).val, by
          have hk := (packetFamily64BlockIndex g i).isLt
          omega⟩ := by simpa using hi
    have hb := rankPacketCell_bounds s lo
      ⟨(packetFamily64BlockIndex g i).val, by
        have hk := (packetFamily64BlockIndex g i).isLt
        omega⟩ hi'
    have hparts := Chvatal.mem_blockOf.mp hi'
    refine ⟨hparts.1, ?_, ?_⟩
    · have hidx : (packetFamily64BlockIndex g i).val = 64 * g.val + i.val := by
        simp [packetFamily64BlockIndex]
        ring
      have hi64 := i.isLt
      have hb' := hb
      rw [hidx] at hb'
      omega
    · have hidx : (packetFamily64BlockIndex g i).val = 64 * g.val + i.val := by
        simp [packetFamily64BlockIndex]
        ring
      have hi64 := i.isLt
      have hb' := hb
      rw [hidx] at hb'
      omega
  · rintro ⟨hw, hlo, hhi⟩
    let k : Fin 64 := ⟨(Chvatal.rankIn s w - (lo + 4096 * g.val)) / 64, by
      apply (Nat.div_lt_iff_lt_mul (by norm_num : 0 < 64)).2
      omega⟩
    have hcellw : w ∈ rankPacketCell s (lo + 4096 * g.val) k := by
      apply Chvatal.mem_blockOf.mpr
      refine ⟨hw, ?_, ?_⟩ <;> simp [rankPacketCell, k] <;>
        have hdecomp := Nat.mod_add_div
          (Chvatal.rankIn s w - (lo + 4096 * g.val)) 64 <;> omega
    have hcell' : rankPacketCell s (lo + 4096 * g.val) k =
        rankPacketCell s lo ⟨(packetFamily64BlockIndex g k).val, by
          have hk := (packetFamily64BlockIndex g k).isLt
          omega⟩ := by
      ext z
      simp only [rankPacketCell, Chvatal.mem_blockOf]
      have hstart : lo + 64 * (packetFamily64BlockIndex g k).val =
          lo + 4096 * g.val + 64 * k.val := by
        simp [packetFamily64BlockIndex]
        ring
      have hend : lo + 64 * ((packetFamily64BlockIndex g k).val + 1) =
          lo + 4096 * g.val + 64 * (k.val + 1) := by
        simp [packetFamily64BlockIndex]
        ring
      rw [hstart, hend]
    refine ⟨k, ?_⟩
    rw [hcell'] at hcellw
    have hsource : w ∈ Set.range (groupedPackets k) := by
      have hcellSet : w ∈ (rankPacketCell s lo
          ⟨(packetFamily64BlockIndex g k).val, by
            have hk := (packetFamily64BlockIndex g k).isLt
            omega⟩ : Set (Fin N)) := hcellw
      rw [← hcell (packetFamily64BlockIndex g k)] at hcellSet
      simpa [groupedPackets] using hcellSet
    exact hsource

/-- Every entry of the 64-packet block list has an explicit consecutive
4096-rank interval as support when its source packets are consecutive
64-rank cells. The existential group index is retained for overlap counting. -/
theorem packetFamily64BlockList_rankIntervals {q N : Nat}
    (s : Finset (Fin N)) (lo : Nat)
    (packets : Fin (q * 64) → Fin 64 ↪ Fin N)
    (hdis : ∀ a b, a ≠ b → ∀ x y, packets a x ≠ packets b y)
    (hcell : ∀ a, Set.range (packets a) =
      (rankPacketCell s lo ⟨a.val, by have ha := a.isLt; omega⟩ : Set (Fin N)))
    (hcomplete : lo + 4096 * q ≤ s.card)
    (e : Fin 4096 ↪ Fin N) (he : e ∈ packetFamily64BlockList packets hdis) :
    ∃ g : Fin q, Set.range e =
      (Chvatal.blockOf s (lo + 4096 * g.val)
        (lo + 4096 * (g.val + 1)) : Set (Fin N)) := by
  classical
  simp only [packetFamily64BlockList, List.mem_ofFn] at he
  obtain ⟨g, rfl⟩ := he
  refine ⟨g, packetFamily64BlockEmbedding_rankInterval_support s lo packets hdis
    hcell g ?_⟩
  have hg := g.isLt
  omega

/-- The block provenance converts rank-cell structure on a canonical source
family into rank intervals for every stored full block. -/
theorem CanonicalPacketFullBlockProvenance.block_rankIntervals
    {N : Nat} {P : CanonicalPacketFamily N} {q r : Nat}
    {blocks : List (Fin 4096 ↪ Fin N)}
    (D : CanonicalPacketFullBlockProvenance P q r blocks)
    (s : Finset (Fin N)) (lo : Nat)
    (hcell : ∀ k : Fin P.count, P.packet k = rankPacketCell s lo k)
    (hcomplete : lo + 4096 * q ≤ s.card)
    (e : Fin 4096 ↪ Fin N) (he : e ∈ blocks) :
    ∃ g : Fin q, Set.range e =
      (Chvatal.blockOf s (lo + 4096 * g.val)
        (lo + 4096 * (g.val + 1)) : Set (Fin N)) := by
  have hsourceCell : ∀ a, Set.range (D.sourcePackets a) =
      (rankPacketCell s lo (D.sourceIndex a) : Set (Fin N)) := by
    intro a
    calc
      Set.range (D.sourcePackets a) =
          (packetEmbeddingSupport (D.sourcePackets a) : Set (Fin N)) := by
            ext w
            exact (packetEmbeddingSupport_mem_iff (D.sourcePackets a) w).symm
      _ = (P.packet (D.sourceIndex a) : Set (Fin N)) :=
        congrArg (fun x : Finset (Fin N) => (x : Set (Fin N))) (D.sourceSupport a)
      _ = (rankPacketCell s lo (D.sourceIndex a) : Set (Fin N)) := by
        rw [hcell]
  have hlocalCell : ∀ a, Set.range (D.sourcePackets a) =
      (rankPacketCell s lo ⟨a.val, by have ha := a.isLt; omega⟩ : Set (Fin N)) := by
    intro a
    rw [hsourceCell a]
    congr 1
    ext w
    simp [rankPacketCell, Chvatal.mem_blockOf, D.sourceIndex_val]
  have hlist : e ∈ List.ofFn D.groupBlocks := by
    rw [← D.blockList_eq]
    exact he
  simp only [List.mem_ofFn] at hlist
  obtain ⟨g, rfl⟩ := hlist
  have hgroupMem : D.groupBlocks g ∈
      packetFamily64BlockList D.sourcePackets D.sourceDisjoint := by
    rw [D.groupBlock_eq]
    simp [packetFamily64BlockList]
  obtain ⟨g', hg'⟩ := packetFamily64BlockList_rankIntervals s lo
    D.sourcePackets D.sourceDisjoint hlocalCell hcomplete
    (D.groupBlocks g) hgroupMem
  exact ⟨g', hg'⟩

/-- Rank interval of the block at its own provenance index. -/
theorem CanonicalPacketFullBlockProvenance.groupBlock_rankInterval
    {N : Nat} {P : CanonicalPacketFamily N} {q r : Nat}
    {blocks : List (Fin 4096 ↪ Fin N)}
    (D : CanonicalPacketFullBlockProvenance P q r blocks)
    (s : Finset (Fin N)) (lo : Nat)
    (hcell : ∀ k : Fin P.count, P.packet k = rankPacketCell s lo k)
    (hcomplete : lo + 4096 * q ≤ s.card) (g : Fin q) :
    Set.range (D.groupBlocks g) =
      (Chvatal.blockOf s (lo + 4096 * g.val)
        (lo + 4096 * (g.val + 1)) : Set (Fin N)) := by
  have hsourceCell : ∀ a, Set.range (D.sourcePackets a) =
      (rankPacketCell s lo (D.sourceIndex a) : Set (Fin N)) := by
    intro a
    calc
      Set.range (D.sourcePackets a) =
          (packetEmbeddingSupport (D.sourcePackets a) : Set (Fin N)) := by
            ext w
            exact (packetEmbeddingSupport_mem_iff (D.sourcePackets a) w).symm
      _ = (P.packet (D.sourceIndex a) : Set (Fin N)) :=
        congrArg (fun x : Finset (Fin N) => (x : Set (Fin N))) (D.sourceSupport a)
      _ = (rankPacketCell s lo (D.sourceIndex a) : Set (Fin N)) := by rw [hcell]
  have hlocalCell : ∀ a, Set.range (D.sourcePackets a) =
      (rankPacketCell s lo ⟨a.val, by have ha := a.isLt; omega⟩ : Set (Fin N)) := by
    intro a
    rw [hsourceCell a]
    congr 1
    ext w
    simp [rankPacketCell, Chvatal.mem_blockOf, D.sourceIndex_val]
  rw [D.groupBlock_eq]
  exact packetFamily64BlockEmbedding_rankInterval_support s lo D.sourcePackets
    D.sourceDisjoint hlocalCell g (by have hg := g.isLt; omega)


/-- An increasing packet embedding is exactly the canonical rank enumeration
of its physical support. -/
theorem packetEmbedding_eq_supportOrderEmbedding {N : Nat}
    (p : Fin 64 ↪ Fin N) (hmono : StrictMono p) :
    ((packetEmbeddingSupport p).orderEmbOfFin (packetEmbeddingSupport_card p)).toEmbedding
      = p := by
  have hEq := Finset.orderEmbOfFin_unique (packetEmbeddingSupport_card p)
    (fun i => by
      simp [packetEmbeddingSupport]) hmono
  ext i
  exact congrArg Fin.val (congrFun hEq i).symm

/-- The increasing physical-wire embedding of every packet in a canonical
rank-sorted family. -/
noncomputable def canonicalPacketEmbedding {N : Nat}
    (P : CanonicalPacketFamily N)
    (hcard : ∀ i, (P.packet i).card = 64) :
    Fin P.count → Fin 64 ↪ Fin N :=
  fun i => ((P.packet i).orderEmbOfFin (hcard i)).toEmbedding

theorem canonicalPacketEmbedding_support {N : Nat}
    (P : CanonicalPacketFamily N)
    (hcard : ∀ i, (P.packet i).card = 64) (i : Fin P.count) :
    packetEmbeddingSupport (canonicalPacketEmbedding P hcard i) = P.packet i := by
  ext w
  change w ∈ packetEmbeddingSupport
      (((P.packet i).orderEmbOfFin (hcard i)).toEmbedding) ↔ w ∈ P.packet i
  rw [packetEmbeddingSupport_mem_iff]
  change w ∈ Set.range ((P.packet i).orderEmbOfFin (hcard i)) ↔
    w ∈ P.packet i
  rw [Finset.range_orderEmbOfFin]
  simp

/-- The two 32-wire rank lanes inside an increasing 64-wire packet embedding. -/
def packetEvenRankEmbedding {N : Nat} (p : Fin 64 ↪ Fin N) :
    Fin 32 ↪ Fin N where
  toFun i := p (evenWire 32 i)
  inj' := by
    intro i j hij
    apply Fin.ext
    have h := p.injective hij
    simp [evenWire] at h
    omega

def packetOddRankEmbedding {N : Nat} (p : Fin 64 ↪ Fin N) :
    Fin 32 ↪ Fin N where
  toFun i := p (oddWire 32 i)
  inj' := by
    intro i j hij
    apply Fin.ext
    have h := p.injective hij
    simp [oddWire] at h
    omega

def packetRankLaneSupport {N m : Nat} (p : Fin m ↪ Fin N) : Finset (Fin N) :=
  Finset.univ.image p

theorem packetEvenRankEmbedding_strictMono {N : Nat} (p : Fin 64 ↪ Fin N)
    (hp : StrictMono p) : StrictMono (packetEvenRankEmbedding p) := by
  intro i j hij
  apply hp
  apply Fin.mk_lt_mk.mpr
  simp [packetEvenRankEmbedding, evenWire]
  omega

theorem packetOddRankEmbedding_strictMono {N : Nat} (p : Fin 64 ↪ Fin N)
    (hp : StrictMono p) : StrictMono (packetOddRankEmbedding p) := by
  intro i j hij
  apply hp
  apply Fin.mk_lt_mk.mpr
  simp [packetOddRankEmbedding, oddWire]
  have h := Fin.mk_lt_mk.mp hij
  omega

/-- Even and odd rank supports partition the support of a 64-wire packet. -/
theorem packetParityRankSupports_partition {N : Nat} (p : Fin 64 ↪ Fin N) :
    Set.range (packetEvenRankEmbedding p) ∪ Set.range (packetOddRankEmbedding p) =
      Set.range p := by
  ext w
  constructor
  · intro hw
    rcases hw with ⟨⟨i, rfl⟩⟩ | ⟨⟨i, rfl⟩⟩
    · exact ⟨evenWire 32 i, rfl⟩
    · exact ⟨oddWire 32 i, rfl⟩
  · rintro ⟨i, rfl⟩
    by_cases heven : i.val % 2 = 0
    · let j : Fin 32 := ⟨i.val / 2, by have := i.isLt; omega⟩
      have hi : evenWire 32 j = i := by
        apply Fin.ext
        simp [evenWire, j]
        omega
      left
      exact ⟨j, by simp [packetEvenRankEmbedding, hi]⟩
    · let j : Fin 32 := ⟨i.val / 2, by have := i.isLt; omega⟩
      have hi : oddWire 32 j = i := by
        apply Fin.ext
        simp [oddWire, j]
        omega
      right
      exact ⟨j, by simp [packetOddRankEmbedding, hi]⟩

theorem packetEmbeddingSupport_parity_partition {N : Nat} (p : Fin 64 ↪ Fin N) :
    packetRankLaneSupport (packetEvenRankEmbedding p) ∪
      packetRankLaneSupport (packetOddRankEmbedding p) =
    packetEmbeddingSupport p := by
  ext w
  simp only [Finset.mem_union, packetRankLaneSupport, Finset.mem_image,
    Finset.mem_univ, true_and, packetEmbeddingSupport_mem_iff]
  have h := congrArg (fun s : Set (Fin N) => w ∈ s)
    (packetParityRankSupports_partition p)
  simpa [Set.mem_union] using h

/-- On a real canonical receiver family, all even/odd rank supports together
partition exactly the receiver register. -/
theorem canonicalPacketParitySupports_partition {N : Nat}
    (P : CanonicalPacketFamily N) (support : Finset (Fin N))
    {α : Type} [LinearOrder α] (v : Fin N → α)
    (hcontract : CanonicalPacketPortContract P support v) :
    Finset.univ.biUnion (fun i =>
      packetRankLaneSupport
          (packetEvenRankEmbedding
            (canonicalPacketEmbedding P hcontract.2.2.2 i)) ∪
        packetRankLaneSupport
          (packetOddRankEmbedding
            (canonicalPacketEmbedding P hcontract.2.2.2 i))) = support := by
  have hUnion : Finset.univ.biUnion P.packet = support := hcontract.2.1
  ext w
  simp only [Finset.mem_biUnion, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨i, hw⟩
    have hlocal := packetEmbeddingSupport_parity_partition
      (canonicalPacketEmbedding P hcontract.2.2.2 i)
    have hpacket := canonicalPacketEmbedding_support P hcontract.2.2.2 i
    rw [hlocal, hpacket] at hw
    rw [← hUnion]
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and]
    exact ⟨i, hw⟩
  · intro hw
    have hexists : ∃ i, w ∈ P.packet i := by
      rw [← hUnion] at hw
      simpa using hw
    rcases hexists with ⟨i, hw⟩
    refine ⟨i, ?_⟩
    have hlocal := packetEmbeddingSupport_parity_partition
      (canonicalPacketEmbedding P hcontract.2.2.2 i)
    have hpacket := canonicalPacketEmbedding_support P hcontract.2.2.2 i
    rw [hlocal, hpacket]
    exact hw

theorem canonicalPacketParityEmbeddings_strictMono {N : Nat}
    (P : CanonicalPacketFamily N) (support : Finset (Fin N))
    {α : Type} [LinearOrder α] (v : Fin N → α)
    (hcontract : CanonicalPacketPortContract P support v) (i : Fin P.count) :
    StrictMono (packetEvenRankEmbedding
      (canonicalPacketEmbedding P hcontract.2.2.2 i)) ∧
    StrictMono (packetOddRankEmbedding
      (canonicalPacketEmbedding P hcontract.2.2.2 i)) := by
  have hp : StrictMono (canonicalPacketEmbedding P hcontract.2.2.2 i) := by
    intro j k hjk
    exact ((P.packet i).orderEmbOfFin (hcontract.2.2.2 i)).strictMono hjk
  exact ⟨packetEvenRankEmbedding_strictMono _ hp,
    packetOddRankEmbedding_strictMono _ hp⟩

/-- Reindex the even and odd rank lanes of every canonical 64-wire packet as
one scattered family of 32-wire embeddings. -/
noncomputable def canonicalPacketParityEmbedding {N : Nat} (P : CanonicalPacketFamily N)
    (hcard : ∀ i, (P.packet i).card = 64) :
    Fin P.count × Bool → Fin 32 ↪ Fin N := fun z =>
  if z.2 then packetOddRankEmbedding (canonicalPacketEmbedding P hcard z.1)
  else packetEvenRankEmbedding (canonicalPacketEmbedding P hcard z.1)

theorem canonicalPacketParityEmbedding_mem {N : Nat}
    (P : CanonicalPacketFamily N) (hcard : ∀ i, (P.packet i).card = 64)
    (z : Fin P.count × Bool) (i : Fin 32) :
    canonicalPacketParityEmbedding P hcard z i ∈ P.packet z.1 := by
  by_cases hb : z.2
  · simp only [canonicalPacketParityEmbedding, if_pos hb, packetOddRankEmbedding,
      canonicalPacketEmbedding]
    exact Finset.orderEmbOfFin_mem (P.packet z.1) (hcard z.1) (oddWire 32 i)
  · simp only [canonicalPacketParityEmbedding, if_neg hb, packetEvenRankEmbedding,
      canonicalPacketEmbedding]
    exact Finset.orderEmbOfFin_mem (P.packet z.1) (hcard z.1) (evenWire 32 i)

/-- Distinct parity lanes from a canonical receiver family have disjoint
physical supports. -/
theorem canonicalPacketParityEmbeddings_disjoint {N : Nat}
    (P : CanonicalPacketFamily N) (support : Finset (Fin N))
    {A : Type} [LinearOrder A] (v : Fin N → A)
    (hcontract : CanonicalPacketPortContract P support v) :
    ∀ z z' : Fin P.count × Bool, z ≠ z' →
      ∀ i j : Fin 32,
        canonicalPacketParityEmbedding P hcontract.2.2.2 z i ≠
          canonicalPacketParityEmbedding P hcontract.2.2.2 z' j := by
  intro z z' hzz i j heq
  by_cases hp : z.1 = z'.1
  · have hfirst : z'.1 = z.1 := hp.symm
    have hb : z.2 ≠ z'.2 := by
      intro h
      exact hzz (Prod.ext hp h)
    simp only [canonicalPacketParityEmbedding, packetEvenRankEmbedding,
      packetOddRankEmbedding] at heq
    rw [hfirst] at heq
    cases hz : z.2 <;> cases hz' : z'.2
    · exact (hb (hz.trans hz'.symm)).elim
    · have hpoint : (canonicalPacketEmbedding P hcontract.2.2.2 z.1) (evenWire 32 i) =
          (canonicalPacketEmbedding P hcontract.2.2.2 z.1) (oddWire 32 j) := by
        simpa [canonicalPacketParityEmbedding, packetEvenRankEmbedding,
          packetOddRankEmbedding, hz, hz'] using heq
      have hidx := (canonicalPacketEmbedding P hcontract.2.2.2 z.1).injective hpoint
      have hv := congrArg Fin.val hidx
      simp [evenWire, oddWire] at hv
      omega
    · have hpoint : (canonicalPacketEmbedding P hcontract.2.2.2 z.1) (oddWire 32 i) =
          (canonicalPacketEmbedding P hcontract.2.2.2 z.1) (evenWire 32 j) := by
        simpa [canonicalPacketParityEmbedding, packetEvenRankEmbedding,
          packetOddRankEmbedding, hz, hz'] using heq
      have hidx := (canonicalPacketEmbedding P hcontract.2.2.2 z.1).injective hpoint
      have hv := congrArg Fin.val hidx
      simp [evenWire, oddWire] at hv
      omega
    · exact (hb (hz.trans hz'.symm)).elim
  · have hmem (p : Fin P.count) (b : Bool) (k : Fin 32) :
        (if b then packetOddRankEmbedding (canonicalPacketEmbedding P hcontract.2.2.2 p)
          else packetEvenRankEmbedding (canonicalPacketEmbedding P hcontract.2.2.2 p)) k
          ∈ P.packet p := by
      by_cases hb : b
      · simp only [if_pos hb, packetOddRankEmbedding, canonicalPacketEmbedding]
        exact Finset.orderEmbOfFin_mem (P.packet p) (hcontract.2.2.2 p) (oddWire 32 k)
      · simp only [if_neg hb, packetEvenRankEmbedding, canonicalPacketEmbedding]
        exact Finset.orderEmbOfFin_mem (P.packet p) (hcontract.2.2.2 p) (evenWire 32 k)
    have hmem' : canonicalPacketParityEmbedding P hcontract.2.2.2 z i ∈ P.packet z.1 := by
      exact hmem z.1 z.2 i
    have hmem'' : canonicalPacketParityEmbedding P hcontract.2.2.2 z' j ∈ P.packet z'.1 := by
      exact hmem z'.1 z'.2 j
    have hdis := Finset.disjoint_left.mp (hcontract.2.2.1 z.1 z'.1 hp) hmem'
    apply hdis
    rw [heq]
    exact hmem''

/-- The even/odd lane embeddings together cover exactly the canonical
receiver support. Combined with `canonicalPacketParityEmbeddings_disjoint`,
this is a partition indexed by `(packet, parity)`. -/
theorem canonicalPacketParityEmbeddings_cover {N : Nat}
    (P : CanonicalPacketFamily N) (support : Finset (Fin N))
    {A : Type} [LinearOrder A] (v : Fin N → A)
    (hcontract : CanonicalPacketPortContract P support v) :
    ∀ w ∈ support, ∃ z : Fin P.count × Bool, ∃ i : Fin 32,
      canonicalPacketParityEmbedding P hcontract.2.2.2 z i = w := by
  intro w hw
  have hpacket : w ∈ Finset.univ.biUnion P.packet := by
    rw [hcontract.2.1]
    exact hw
  simp only [Finset.mem_biUnion, Finset.mem_univ, true_and] at hpacket
  obtain ⟨p, hp⟩ := hpacket
  have hsupport : w ∈ packetEmbeddingSupport (canonicalPacketEmbedding P
      hcontract.2.2.2 p) := by
    rw [canonicalPacketEmbedding_support P hcontract.2.2.2 p]
    exact hp
  have hrange : w ∈ Set.range (canonicalPacketEmbedding P hcontract.2.2.2 p) :=
    (packetEmbeddingSupport_mem_iff _ _).1 hsupport
  have hpartition := packetParityRankSupports_partition
    (canonicalPacketEmbedding P hcontract.2.2.2 p)
  have hlanes : w ∈ Set.range (packetEvenRankEmbedding
      (canonicalPacketEmbedding P hcontract.2.2.2 p)) ∪
      Set.range (packetOddRankEmbedding
        (canonicalPacketEmbedding P hcontract.2.2.2 p)) := by
    rw [hpartition]
    exact hrange
  rcases hlanes with heven | hodd
  · obtain ⟨i, hi⟩ := heven
    refine ⟨(p, false), i, ?_⟩
    simpa [canonicalPacketParityEmbedding, packetEvenRankEmbedding] using hi
  · obtain ⟨i, hi⟩ := hodd
    refine ⟨(p, true), i, ?_⟩
    simpa [canonicalPacketParityEmbedding, packetOddRankEmbedding] using hi

/-- Convert a rank-sorted canonical partition into logical packet embeddings.
The increasing physical-wire enumeration ensures each input embedding is
sorted, and the embeddings retain the partition's exact support and
disjointness. -/
theorem canonicalPacketFamily_toEmbeddings {N : Nat} {α : Type}
    [LinearOrder α] (P : CanonicalPacketFamily N)
    (support : Finset (Fin N)) (v : Fin N → α)
    (hcontract : CanonicalPacketPortContract P support v) :
    let packets := canonicalPacketEmbedding P hcontract.2.2.2
    (∀ i, Monotone (fun k => v (packets i k))) ∧
    (∀ i i', i ≠ i' → ∀ x y, packets i x ≠ packets i' y) ∧
    Finset.univ.biUnion (fun i => packetEmbeddingSupport (packets i)) = support := by
  let packets := canonicalPacketEmbedding P hcontract.2.2.2
  have hsorted : ∀ i, Monotone (fun k => v (packets i k)) := by
    intro i a b hab
    have hmemA : packets i a ∈ P.packet i := by
      simpa [packets, canonicalPacketEmbedding] using
        Finset.orderEmbOfFin_mem (P.packet i) (hcontract.2.2.2 i) a
    have hmemB : packets i b ∈ P.packet i := by
      simpa [packets, canonicalPacketEmbedding] using
        Finset.orderEmbOfFin_mem (P.packet i) (hcontract.2.2.2 i) b
    have hwire : (packets i a).val ≤ (packets i b).val := by
      exact Fin.le_def.mp
        (((P.packet i).orderEmbOfFin (hcontract.2.2.2 i)).monotone hab)
    exact hcontract.1 i hmemA hmemB hwire
  have hdisjoint : ∀ i i', i ≠ i' → ∀ x y, packets i x ≠ packets i' y := by
    intro i i' hne x y heq
    have hmemA : packets i x ∈ P.packet i :=
      by simpa [packets, canonicalPacketEmbedding] using
        Finset.orderEmbOfFin_mem (P.packet i) (hcontract.2.2.2 i) x
    have hmemB : packets i' y ∈ P.packet i' :=
      by simpa [packets, canonicalPacketEmbedding] using
        Finset.orderEmbOfFin_mem (P.packet i') (hcontract.2.2.2 i') y
    have hnot := (Finset.disjoint_left.mp (hcontract.2.2.1 i i' hne)) hmemA
    exact hnot (heq ▸ hmemB)
  have hsupport : Finset.univ.biUnion
      (fun i => packetEmbeddingSupport (packets i)) = support := by
    simp_rw [packets, canonicalPacketEmbedding_support]
    exact hcontract.2.1
  exact ⟨hsorted, hdisjoint, hsupport⟩

/-- Group every complete run of 64 packets in a canonical family into a
4096-wire merge block. The fewer than 64 remaining packets stay as sorted
tail packets, and together the two parts cover the original support exactly.
This handles the parent port's arbitrary packet-count residue. -/
theorem canonicalPacketFamily_fullBlocks_with_tail {N : Nat} {α : Type}
    [LinearOrder α] (P : CanonicalPacketFamily N) (support : Finset (Fin N))
    (v : Fin N → α) (hcontract : CanonicalPacketPortContract P support v) :
    ∃ q r, q * 64 + r = P.count ∧ r < 64 ∧
    ∃ tail : Fin r → Fin 64 ↪ Fin N,
    ∃ blocks : List (Fin 4096 ↪ Fin N),
      blocks.Nodup ∧
      (∀ e ∈ blocks, ∀ f ∈ blocks, e ≠ f → ∀ x y, e x ≠ f y) ∧
      (genScatterMergeTreeBatch (packetPowerTree6 (α := α)) blocks).depth ≤ 57 ∧
      (∀ e ∈ blocks, Monotone (fun i =>
        (genScatterMergeTreeBatch (packetPowerTree6 (α := α)) blocks).exec v (e i))) ∧
      (∀ e ∈ blocks, ∀ j : Fin (packetPowerTree6 (α := α)).leafCount,
        Monotone (fun i =>
          (genScatterMergeTreeBatch (packetPowerTree6 (α := α)) blocks).exec v
            (genScatterMergeTreeOutputEmbedding (packetPowerTree6 (α := α)) e j i))) ∧
      (∀ j, Monotone (fun i => v (tail j i))) ∧
      (∀ j, StrictMono (tail j)) ∧
      (∀ e ∈ blocks, ∀ i j k, e i ≠ tail j k) ∧
      (∀ j j', j ≠ j' → ∀ x y, tail j x ≠ tail j' y) ∧
      (∀ w, ((∃ e ∈ blocks, w ∈ Set.range e) ∨
          ∃ j, w ∈ Set.range (tail j)) ↔ w ∈ support) ∧
      Nonempty (CanonicalPacketFullBlockProvenance P q r blocks) := by
  let q := P.count / 64
  let r := P.count % 64
  have hqr : q * 64 + r = P.count := by
    dsimp [q, r]
    have h := Nat.mod_add_div P.count 64
    omega
  have hr : r < 64 := by dsimp [r]; exact Nat.mod_lt _ (by omega)
  let emb := canonicalPacketEmbedding P hcontract.2.2.2
  let prefixIndex : Fin (q * 64) → Fin P.count :=
    fun i => Fin.cast hqr (Fin.castAdd r i)
  let tailIndex : Fin r → Fin P.count :=
    fun i => Fin.cast hqr (Fin.natAdd (q * 64) i)
  let prefixPackets : Fin (q * 64) → Fin 64 ↪ Fin N := fun i => emb (prefixIndex i)
  let tail : Fin r → Fin 64 ↪ Fin N := fun i => emb (tailIndex i)
  have hcanon := canonicalPacketFamily_toEmbeddings P support v hcontract
  have hprefixDis : ∀ a b, a ≠ b → ∀ x y, prefixPackets a x ≠ prefixPackets b y := by
    intro a b hab x y heq
    have hne : prefixIndex a ≠ prefixIndex b := by
      intro h
      apply hab
      apply Fin.ext
      have hv := congrArg Fin.val h
      simpa [prefixIndex] using hv
    exact hcanon.2.1 (prefixIndex a) (prefixIndex b) hne x y heq
  let blocks := packetFamily64BlockList prefixPackets hprefixDis
  have hsplit : ∀ i : Fin P.count,
      (∃ a, prefixIndex a = i) ∨ (∃ j, tailIndex j = i) := by
    intro i
    by_cases hi : i.val < q * 64
    · left
      let a : Fin (q * 64) := ⟨i.val, hi⟩
      refine ⟨a, ?_⟩
      apply Fin.ext
      simp [prefixIndex, a]
    · right
      let j : Fin r := ⟨i.val - q * 64, by have hii := i.isLt; omega⟩
      refine ⟨j, ?_⟩
      apply Fin.ext
      simp [tailIndex, j]
      omega
  have hpacketRange (i : Fin P.count) (w : Fin N) :
      w ∈ P.packet i ↔ w ∈ Set.range (emb i) := by
    rw [← canonicalPacketEmbedding_support P hcontract.2.2.2 i]
    exact packetEmbeddingSupport_mem_iff (emb i) w
  have hcover : ∀ w, ((∃ e ∈ blocks, w ∈ Set.range e) ∨
      ∃ j, w ∈ Set.range (tail j)) ↔ w ∈ support := by
    intro w
    have hblocks : (∃ e ∈ blocks, w ∈ Set.range e) ↔
        ∃ a x, prefixPackets a x = w := by
      simpa [blocks] using packetFamily64BlockList_support prefixPackets hprefixDis w
    constructor
    · intro h
      have hsource : ∃ i, w ∈ P.packet i := by
        rcases h with hfull | htail
        · obtain ⟨a, x, hax⟩ := hblocks.mp hfull
          exact ⟨prefixIndex a, (hpacketRange (prefixIndex a) w).2 ⟨x, hax⟩⟩
        · obtain ⟨j, x, hx⟩ := htail
          exact ⟨tailIndex j, (hpacketRange (tailIndex j) w).2 ⟨x, hx⟩⟩
      rw [← hcontract.2.1]
      simpa only [Finset.mem_biUnion, Finset.mem_univ, true_and] using hsource
    · intro hw
      rw [← hcontract.2.1] at hw
      simp only [Finset.mem_biUnion, Finset.mem_univ, true_and] at hw
      obtain ⟨i, hi⟩ := hw
      rcases hsplit i with ⟨a, rfl⟩ | ⟨j, rfl⟩
      · left
        apply hblocks.mpr
        obtain ⟨x, hx⟩ := (hpacketRange (prefixIndex a) w).mp hi
        exact ⟨a, x, by simpa [prefixPackets] using hx⟩
      · right
        exact ⟨j, (hpacketRange (tailIndex j) w).mp hi⟩
  have htailSorted : ∀ j, Monotone (fun i => v (tail j i)) := by
    intro j
    exact hcanon.1 (tailIndex j)
  have htailStrict : ∀ j, StrictMono (tail j) := by
    intro j
    simpa [tail, emb, canonicalPacketEmbedding] using
      ((P.packet (tailIndex j)).orderEmbOfFin
        (hcontract.2.2.2 (tailIndex j))).strictMono
  have htailDis : ∀ e ∈ blocks, ∀ i j k, e i ≠ tail j k := by
    intro e he i j k heq
    have hsource := (packetFamily64BlockList_support prefixPackets hprefixDis
        (tail j k)).1 ⟨e, he, i, heq⟩
    obtain ⟨a, x, hax⟩ := hsource
    have hne : prefixIndex a ≠ tailIndex j := by
      intro h
      have hv := congrArg Fin.val h
      simp [prefixIndex, tailIndex] at hv
      omega
    exact hcanon.2.1 (prefixIndex a) (tailIndex j) hne x k hax
  have htailPairwise : ∀ j j', j ≠ j' → ∀ x y, tail j x ≠ tail j' y := by
    intro j j' hj x y heq
    have hne : tailIndex j ≠ tailIndex j' := by
      intro h
      apply hj
      apply Fin.ext
      have hv := congrArg Fin.val h
      simp [tailIndex] at hv
      omega
    exact hcanon.2.1 (tailIndex j) (tailIndex j') hne x y heq
  refine ⟨q, r, hqr, hr, tail, blocks,
    packetFamily64BlockList_nodup prefixPackets hprefixDis,
    packetFamily64BlockList_disjoint prefixPackets hprefixDis,
    packetFamily64BlockList_merge_depth_le prefixPackets hprefixDis,
    packetFamily64BlockList_merge_output_blockSorted prefixPackets hprefixDis v
      (fun a => hcanon.1 (prefixIndex a)),
    packetFamily64BlockList_merge_output_sorted prefixPackets hprefixDis v
      (fun a => hcanon.1 (prefixIndex a)),
    htailSorted, htailStrict, htailDis, htailPairwise, hcover, ?_⟩
  refine ⟨⟨prefixPackets, prefixIndex, ?_, hprefixDis, ?_,
    (fun g => packetFamily64BlockEmbedding prefixPackets hprefixDis g), ?_, rfl⟩⟩
  · intro a
    simp [prefixIndex]
  · intro a
    simpa [prefixPackets, emb] using
      (canonicalPacketEmbedding_support P hcontract.2.2.2 (prefixIndex a))
  · intro g
    rfl

/-- Group each member of a disjoint family of canonical streams independently.
The resulting 4096-wire blocks remain disjoint across streams, so all those
per-stream block batches can later be scheduled in parallel. -/
theorem canonicalStreamFamilies_fullBlocks_disjoint {N : Nat} {α I : Type}
    [LinearOrder α] [Fintype I]
    (P : I → CanonicalPacketFamily N)
    (support : I → Finset (Fin N)) (v : Fin N → α)
    (hcontract : ∀ i, CanonicalPacketPortContract (P i) (support i) v)
    (hsupport : ∀ i j, i ≠ j → Disjoint (support i) (support j)) :
    ∃ blocks : I → List (Fin 4096 ↪ Fin N),
    ∃ remainder : I → Nat,
    ∃ tail : ∀ i, Fin (remainder i) → Fin 64 ↪ Fin N,
    ∃ fullGroups : I → Nat,
      (∀ i, fullGroups i * 64 + remainder i = (P i).count ∧
        remainder i < 64 ∧ (blocks i).Nodup ∧
        (∀ e ∈ blocks i, ∀ f ∈ blocks i, e ≠ f → ∀ x y, e x ≠ f y) ∧
        (genScatterMergeTreeBatch (packetPowerTree6 (α := α)) (blocks i)).depth ≤ 57 ∧
        (∀ e ∈ blocks i, Monotone (fun k =>
          (genScatterMergeTreeBatch (packetPowerTree6 (α := α)) (blocks i)).exec
            v (e k))) ∧
        (∀ e ∈ blocks i, ∀ j : Fin (packetPowerTree6 (α := α)).leafCount,
          Monotone (fun k =>
            (genScatterMergeTreeBatch (packetPowerTree6 (α := α)) (blocks i)).exec
              v (genScatterMergeTreeOutputEmbedding
                (packetPowerTree6 (α := α)) e j k))) ∧
        (∀ j, Monotone (fun k => v (tail i j k))) ∧
        (∀ j, StrictMono (tail i j)) ∧
        (∀ e ∈ blocks i, ∀ a j k, e a ≠ tail i j k) ∧
        (∀ j j', j ≠ j' → ∀ x y, tail i j x ≠ tail i j' y) ∧
        (∀ w, ((∃ e ∈ blocks i, w ∈ Set.range e) ∨
            ∃ j, w ∈ Set.range (tail i j)) ↔ w ∈ support i)) ∧
      (∀ i j, i ≠ j → ∀ e ∈ blocks i, ∀ f ∈ blocks j,
        ∀ x y, e x ≠ f y) ∧
      (∀ i, Nonempty (CanonicalPacketFullBlockProvenance
        (P i) (fullGroups i) (remainder i) (blocks i))) := by
  classical
  have hfull : ∀ i, ∃ q r, q * 64 + r = (P i).count ∧ r < 64 ∧
      ∃ tail : Fin r → Fin 64 ↪ Fin N,
      ∃ blocks : List (Fin 4096 ↪ Fin N),
        blocks.Nodup ∧
        (∀ e ∈ blocks, ∀ f ∈ blocks, e ≠ f → ∀ x y, e x ≠ f y) ∧
        (genScatterMergeTreeBatch (packetPowerTree6 (α := α)) blocks).depth ≤ 57 ∧
        (∀ e ∈ blocks, Monotone (fun k =>
          (genScatterMergeTreeBatch (packetPowerTree6 (α := α)) blocks).exec v (e k))) ∧
        (∀ e ∈ blocks, ∀ j : Fin (packetPowerTree6 (α := α)).leafCount,
          Monotone (fun k =>
            (genScatterMergeTreeBatch (packetPowerTree6 (α := α)) blocks).exec v
              (genScatterMergeTreeOutputEmbedding
                (packetPowerTree6 (α := α)) e j k))) ∧
        (∀ j, Monotone (fun k => v (tail j k))) ∧
        (∀ j, StrictMono (tail j)) ∧
        (∀ e ∈ blocks, ∀ a j k, e a ≠ tail j k) ∧
        (∀ j j', j ≠ j' → ∀ x y, tail j x ≠ tail j' y) ∧
        (∀ w, ((∃ e ∈ blocks, w ∈ Set.range e) ∨
            ∃ j, w ∈ Set.range (tail j)) ↔ w ∈ support i) ∧
        Nonempty (CanonicalPacketFullBlockProvenance (P i) q r blocks) := by
    intro i
    exact canonicalPacketFamily_fullBlocks_with_tail (P i) (support i) v
      (hcontract i)
  choose q r hqr hr tail blocks hnd hdis hdepth hblockSorted houtputSorted
    htailSorted htailStrict hblockTail htailPairwise hcover hprovenance using hfull
  refine ⟨blocks, r, tail, q, ?_, ?_, ?_⟩
  · intro i
    exact ⟨hqr i, hr i, hnd i, hdis i, hdepth i, hblockSorted i,
      houtputSorted i, htailSorted i, htailStrict i, hblockTail i, htailPairwise i,
      hcover i⟩
  · intro i j hij e he f hf x y heq
    have hix : e x ∈ support i := by
      apply (hcover i (e x)).mp
      exact Or.inl ⟨e, he, ⟨x, rfl⟩⟩
    have hjy : f y ∈ support j := by
      apply (hcover j (f y)).mp
      exact Or.inl ⟨f, hf, ⟨y, rfl⟩⟩
    have hnot := (Finset.disjoint_left.mp (hsupport i j hij) hix)
    exact hnot (heq ▸ hjy)
  · exact hprovenance

/-- Data form of the per-stream full-block decomposition, for composition with
other receiver-stage data. -/
structure CanonicalStreamFullBlockData {N : Nat} {α I : Type}
    [LinearOrder α] [Fintype I]
    (P : I → CanonicalPacketFamily N) (support : I → Finset (Fin N))
    (v : Fin N → α) where
  blocks : I → List (Fin 4096 ↪ Fin N)
  remainder : I → Nat
  tail : ∀ i, Fin (remainder i) → Fin 64 ↪ Fin N
  fullGroups : I → Nat
  perStream : ∀ i,
    fullGroups i * 64 + remainder i = (P i).count ∧
    remainder i < 64 ∧
    (blocks i).Nodup ∧
    (∀ e ∈ blocks i, ∀ f ∈ blocks i, e ≠ f → ∀ x y, e x ≠ f y) ∧
    (genScatterMergeTreeBatch (packetPowerTree6 (α := α)) (blocks i)).depth ≤ 57 ∧
    (∀ e ∈ blocks i, Monotone (fun k =>
      (genScatterMergeTreeBatch (packetPowerTree6 (α := α)) (blocks i)).exec
        v (e k))) ∧
    (∀ e ∈ blocks i, ∀ j : Fin (packetPowerTree6 (α := α)).leafCount,
      Monotone (fun k =>
        (genScatterMergeTreeBatch (packetPowerTree6 (α := α)) (blocks i)).exec
          v (genScatterMergeTreeOutputEmbedding
            (packetPowerTree6 (α := α)) e j k))) ∧
    (∀ j, Monotone (fun k => v (tail i j k))) ∧
    (∀ j, StrictMono (tail i j)) ∧
    (∀ e ∈ blocks i, ∀ a j k, e a ≠ tail i j k) ∧
    (∀ j j', j ≠ j' → ∀ x y, tail i j x ≠ tail i j' y) ∧
    (∀ w, ((∃ e ∈ blocks i, w ∈ Set.range e) ∨
        ∃ j, w ∈ Set.range (tail i j)) ↔ w ∈ support i)
  crossStreamDisjoint : ∀ i j, i ≠ j → ∀ e ∈ blocks i, ∀ f ∈ blocks j,
    ∀ x y, e x ≠ f y
  provenance : ∀ i, Nonempty (CanonicalPacketFullBlockProvenance
    (P i) (fullGroups i) (remainder i) (blocks i))

/-- Package the checked existential decomposition as reusable data. -/
theorem canonicalStreamFamilies_fullBlocks_data {N : Nat} {α I : Type}
    [LinearOrder α] [Fintype I]
    (P : I → CanonicalPacketFamily N)
    (support : I → Finset (Fin N)) (v : Fin N → α)
    (hcontract : ∀ i, CanonicalPacketPortContract (P i) (support i) v)
    (hsupport : ∀ i j, i ≠ j → Disjoint (support i) (support j)) :
    Nonempty (CanonicalStreamFullBlockData P support v) := by
  obtain ⟨blocks, remainder, tail, fullGroups, hperStream, hcross, hprovenance⟩ :=
    canonicalStreamFamilies_fullBlocks_disjoint P support v hcontract hsupport
  exact ⟨⟨blocks, remainder, tail, fullGroups, hperStream, hcross, hprovenance⟩⟩

namespace CanonicalStreamFullBlockData

/-- A 64-wire rank cell cannot run past the end of its source register: its
64 distinct wires occupy 64 distinct ranks in an interval of width 64. -/
theorem rankPacketCell_end_le_card {N : Nat} (s : Finset (Fin N)) (lo k : Nat)
    (hcellCard : (rankPacketCell s lo ⟨k, Nat.lt_succ_self k⟩).card = 64) :
    lo + 64 * (k + 1) ≤ s.card := by
  let cell := rankPacketCell s lo ⟨k, Nat.lt_succ_self k⟩
  let start := lo + 64 * k
  let R := cell.image (Chvatal.rankIn s)
  have hcardR : R.card = 64 := by
    dsimp [R]
    rw [Finset.card_image_of_injOn (f := Chvatal.rankIn s)]
    · exact hcellCard
    · intro w hw w' hw' heq
      exact Chvatal.rankIn_injOn
        (Chvatal.mem_blockOf.mp hw).1 (Chvatal.mem_blockOf.mp hw').1 heq
  have hsubset : R ⊆ Finset.Ico start s.card := by
    intro r hr
    rcases Finset.mem_image.mp hr with ⟨w, hw, rfl⟩
    have hb := rankPacketCell_bounds s lo ⟨k, Nat.lt_succ_self k⟩ hw
    have hs := Chvatal.mem_blockOf.mp hw
    have hlt := Chvatal.rankIn_lt_card hs.1
    simp only [Finset.mem_Ico]
    exact ⟨by simpa [start] using hb.1, hlt⟩
  have hle := Finset.card_le_card hsubset
  rw [Nat.card_Ico] at hle
  dsimp [start] at hle
  omega

/-- Recover the exact port-local rank interval for every retained regular
full block whenever the canonical source packets are consecutive rank cells. -/
theorem block_rankIntervals {N : Nat} {α I : Type}
    [LinearOrder α] [Fintype I]
    {P : I → CanonicalPacketFamily N} {support : I → Finset (Fin N)}
    {v : Fin N → α} (D : CanonicalStreamFullBlockData P support v)
    (i : I) (s : Finset (Fin N)) (lo : Nat)
    (hcontract : CanonicalPacketPortContract (P i) (support i) v)
    (hcell : ∀ k : Fin (P i).count,
      (P i).packet k = rankPacketCell s lo k)
    (e : Fin 4096 ↪ Fin N) (he : e ∈ D.blocks i) :
    ∃ g : Fin (D.fullGroups i), Set.range e =
      (Chvatal.blockOf s (lo + 4096 * g.val)
        (lo + 4096 * (g.val + 1)) : Set (Fin N)) := by
  classical
  have hcount := (D.perStream i).1
  have hgroups : D.fullGroups i * 64 ≤ (P i).count := by omega
  by_cases hzero : D.fullGroups i = 0
  · have hblocks : D.blocks i = [] := by
      rcases D.provenance i with ⟨prov⟩
      rw [prov.blockList_eq]
      simp [hzero]
    rw [hblocks] at he
    simp at he
  · have hcomplete : lo + 4096 * D.fullGroups i ≤ s.card := by
      let n := D.fullGroups i * 64 - 1
      have hn : n < (P i).count := by dsimp [n]; omega
      let k : Fin (P i).count := ⟨n, hn⟩
      have hcard := hcontract.2.2.2 k
      rw [hcell k] at hcard
      have hend := rankPacketCell_end_le_card s lo n (by simpa [k, n] using hcard)
      dsimp [n] at hend
      omega
    exact (Classical.choice (D.provenance i)).block_rankIntervals
      s lo hcell hcomplete e he

/-- A nonempty full-block prefix of rank cells is complete in its source
register; this is the endpoint inequality needed by the shifted overlap lemma. -/
theorem rankCellStream_complete {N : Nat} {α I : Type}
    [LinearOrder α] [Fintype I]
    {P : I → CanonicalPacketFamily N} {support : I → Finset (Fin N)}
    {v : Fin N → α} (D : CanonicalStreamFullBlockData P support v)
    (i : I) (s : Finset (Fin N)) (lo : Nat)
    (hcontract : CanonicalPacketPortContract (P i) (support i) v)
    (hcell : ∀ k : Fin (P i).count,
      (P i).packet k = rankPacketCell s lo k)
    (hpositive : 0 < D.fullGroups i) :
    lo + 4096 * D.fullGroups i ≤ s.card := by
  have hcount := (D.perStream i).1
  have hgroups : D.fullGroups i * 64 ≤ (P i).count := by omega
  let n := D.fullGroups i * 64 - 1
  have hn : n < (P i).count := by dsimp [n]; omega
  let k : Fin (P i).count := ⟨n, hn⟩
  have hcard := hcontract.2.2.2 k
  rw [hcell k] at hcard
  have hend := rankPacketCell_end_le_card s lo n (by simpa [k, n] using hcard)
  dsimp [n] at hend
  omega

/-- Exact rank support of a regular block at its own stream-group index. -/
theorem groupBlock_rankInterval {N : Nat} {α I : Type}
    [LinearOrder α] [Fintype I]
    {P : I → CanonicalPacketFamily N} {support : I → Finset (Fin N)}
    {v : Fin N → α} (D : CanonicalStreamFullBlockData P support v)
    (i : I) (s : Finset (Fin N)) (lo : Nat)
    (hcontract : CanonicalPacketPortContract (P i) (support i) v)
    (hcell : ∀ k : Fin (P i).count,
      (P i).packet k = rankPacketCell s lo k)
    (g : Fin (D.fullGroups i)) :
    Set.range ((Classical.choice (D.provenance i)).groupBlocks g) =
      (Chvatal.blockOf s (lo + 4096 * g.val)
        (lo + 4096 * (g.val + 1)) : Set (Fin N)) := by
  classical
  have hcount := (D.perStream i).1
  have hgroups : D.fullGroups i * 64 ≤ (P i).count := by omega
  have hpos : 0 < D.fullGroups i := by have hg := g.isLt; omega
  let n := D.fullGroups i * 64 - 1
  have hn : n < (P i).count := by dsimp [n]; omega
  let k : Fin (P i).count := ⟨n, hn⟩
  have hcard := hcontract.2.2.2 k
  rw [hcell k] at hcard
  have hend := rankPacketCell_end_le_card s lo n (by simpa [k, n] using hcard)
  dsimp [n] at hend
  have hcomplete : lo + 4096 * D.fullGroups i ≤ s.card := by omega
  exact (Classical.choice (D.provenance i)).groupBlock_rankInterval
    s lo hcell hcomplete g

/-- Combine per-stream rank-cell offsets with the retained full-block
provenance. Completeness of every full rank interval is derived from the
64-wire packet cardinality, rather than supplied as an extra assumption. -/
theorem rankIntervals_of_rankCellStreams {N : Nat} {α I : Type}
    [LinearOrder α] [Fintype I]
    {P : I → CanonicalPacketFamily N} {support : I → Finset (Fin N)}
    {v : Fin N → α} (D : CanonicalStreamFullBlockData P support v)
    (hcontract : ∀ i, CanonicalPacketPortContract (P i) (support i) v)
    (sourceSupport : I → Finset (Fin N))
    (hcell : ∀ i, ∃ lo, ∀ k : Fin (P i).count,
      (P i).packet k = rankPacketCell (sourceSupport i) lo k) :
    ∀ i e, e ∈ D.blocks i → ∃ lo g : Nat,
      ∃ gi : Fin (D.fullGroups i), gi.val = g ∧
        Set.range e =
          (Chvatal.blockOf (sourceSupport i) (lo + 4096 * g)
            (lo + 4096 * (g + 1)) : Set (Fin N)) := by
  intro i e he
  obtain ⟨lo, hlo⟩ := hcell i
  obtain ⟨g, hinterval⟩ := D.block_rankIntervals i (sourceSupport i) lo
    (hcontract i) hlo e he
  exact ⟨lo, g.val, g, rfl, hinterval⟩

/-- Every retained residue-wire belongs to the original stream support. -/
theorem tail_subset_support {N : Nat} {α I : Type} [LinearOrder α] [Fintype I]
    {P : I → CanonicalPacketFamily N} {support : I → Finset (Fin N)}
    {v : Fin N → α} (D : CanonicalStreamFullBlockData P support v)
    (i : I) (j : Fin (D.remainder i)) :
    packetEmbeddingSupport (D.tail i j) ⊆ support i := by
  rcases D.perStream i with
    ⟨_, _, _, _, _, _, _, _, _, _, _, hcover⟩
  intro w hw
  apply (hcover w).mp
  right
  exact ⟨j, (packetEmbeddingSupport_mem_iff (D.tail i j) w).mp hw⟩

/-- Every regular full-block wire belongs to its original stream support. -/
theorem block_subset_support {N : Nat} {α I : Type} [LinearOrder α] [Fintype I]
    {P : I → CanonicalPacketFamily N} {support : I → Finset (Fin N)}
    {v : Fin N → α} (D : CanonicalStreamFullBlockData P support v)
    (i : I) (e : Fin 4096 ↪ Fin N) (he : e ∈ D.blocks i) :
    Set.range e ⊆ support i := by
  rcases D.perStream i with
    ⟨_, _, _, _, _, _, _, _, _, _, _, hcover⟩
  intro w hw
  apply (hcover w).mp
  left
  exact ⟨e, he, hw⟩

end CanonicalStreamFullBlockData

/-- Packet supports indexed by the exact tails of a full-block decomposition
and by a supplied family of endpoint packets. -/
def canonicalStreamFullBlockExceptionPacket {N : Nat} {α I E : Type}
    [LinearOrder α] [Fintype I]
    {P : I → CanonicalPacketFamily N} {support : I → Finset (Fin N)}
    {v : Fin N → α} (D : CanonicalStreamFullBlockData P support v)
    (endpoint : E → Finset (Fin N))
    (j : (Σ i : I, Fin (D.remainder i)) ⊕ E) : Finset (Fin N) :=
  match j with
  | Sum.inl ⟨i, k⟩ => packetEmbeddingSupport (D.tail i k)
  | Sum.inr e => endpoint e

/-- The regular cells of any aligned rank interval form a canonical sorted
packet stream. This is the interface for splitting each concrete port stream
into 4096-wire blocks and fewer than 64 residue cells. -/
theorem rankPacketCell_stream_contract {N : Nat} {α : Type} [LinearOrder α]
    (s : Finset (Fin N)) (v : Fin N → α) (lo m : Nat)
    (hcell : ∀ k : Fin m, RankSortedOn (rankPacketCell s lo k) v)
    (hfinish : lo + 64 * m ≤ s.card) :
    CanonicalPacketPortContract
      ⟨m, fun k : Fin m => rankPacketCell s lo k⟩
      (Chvatal.blockOf s lo (lo + 64 * m)) v := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro k
    exact hcell k
  · simpa [rankPacketCell] using
      (blockOf_packetCell_partition s lo m).symm
  · intro k l hne
    have hkl : k.val ≠ l.val := fun h => hne (Fin.ext h)
    apply Finset.disjoint_left.mpr
    intro w hwk hwl
    have hk := rankPacketCell_bounds s lo k hwk
    have hl := rankPacketCell_bounds s lo l hwl
    rcases lt_or_gt_of_ne hkl with hkl | hlk
    · omega
    · omega
  · intro k
    have hklt : k.val < m := by simpa using k.isLt
    have hk : k.val + 1 ≤ m := by omega
    have hmul : 64 * (k.val + 1) ≤ 64 * m := Nat.mul_le_mul_left 64 hk
    have hsum : lo + 64 * (k.val + 1) ≤ lo + 64 * m :=
      Nat.add_le_add_left hmul lo
    have hcellHi : lo + 64 * (k.val + 1) ≤ s.card := hsum.trans hfinish
    simp only [rankPacketCell]
    rw [Chvatal.blockOf_card hcellHi]
    omega

/-- Conditional arithmetic budget for pooling the residues of the 129
regular streams and at most 65 endpoint packets.  This counts packets only;
it does not assert their supports are disjoint or form a canonical family. -/
theorem shiftedSelector_exceptionPool_budget
    (residue : Fin 129 → Nat) (hresidue : ∀ i, residue i < 64) :
    (∑ i : Fin 129, residue i) + 65 ≤ 8192 ∧
      ((∑ i : Fin 129, residue i) + 65) / 64 ≤ 128 := by
  have hsum : (∑ i : Fin 129, residue i) ≤ ∑ _i : Fin 129, 63 :=
    Finset.sum_le_sum (fun i _ => by have hi := hresidue i; omega)
  have hconst : (∑ _i : Fin 129, 63) = 8127 := by norm_num
  have hbudget : (∑ i : Fin 129, residue i) + 65 ≤ 8192 := by omega
  constructor
  · exact hbudget
  · omega

/-- Flatten the stream residues and endpoint slots into one finite index
type. This is only an index-card bound; packet supports and their disjointness
must still be supplied by the concrete selector decomposition. -/
theorem shiftedSelector_exceptionPool_index_card
    (residue : Fin 129 → Nat) (hresidue : ∀ i, residue i < 64) :
    Fintype.card ((Σ i : Fin 129, Fin (residue i)) ⊕ Fin 65) ≤ 8192 := by
  classical
  have hbudget := shiftedSelector_exceptionPool_budget residue hresidue
  simp only [Fintype.card_sum, Fintype.card_sigma, Fintype.card_fin]
  omega

set_option maxRecDepth 10000
/-- Assemble actual sorted, disjoint 64-wire stream residues and existing
endpoint packets into one canonical family.  This is the pool-construction
interface: callers must provide the concrete packet function and prove its
support properties; the 8,192 capacity then follows from the stream bounds. -/
theorem canonicalExceptionPool_family {N : Nat} {α I E : Type}
    [LinearOrder α] [Fintype I] [Fintype E]
    (v : Fin N → α) (residue : I → Nat)
    (hstreamCount : Fintype.card I ≤ 129)
    (hresidue : ∀ i, residue i < 64)
    (packet : ((Σ i : I, Fin (residue i)) ⊕ E) → Finset (Fin N))
    (hendpointCount : Fintype.card E ≤ 65)
    (hsorted : ∀ i, RankSortedOn (packet i) v)
    (hdisjoint : ∀ i j, i ≠ j → Disjoint (packet i) (packet j))
    (hcard : ∀ i, (packet i).card = 64) :
    ∃ P : CanonicalPacketFamily N,
      P.count ≤ 8192 ∧
      CanonicalPacketPortContract P (Finset.univ.biUnion packet) v := by
  classical
  let J := (Σ i : I, Fin (residue i)) ⊕ E
  let P := canonicalPacketFamily packet
  have hsum : ∑ i : I, residue i ≤ ∑ _i : I, 63 :=
    Finset.sum_le_sum fun i hi => Nat.le_pred_of_lt (hresidue i)
  have hconst : (∑ _i : I, 63) = Fintype.card I * 63 := by simp
  have hbudget : (∑ i : I, residue i) + Fintype.card E ≤ 8192 := by
    rw [hconst] at hsum
    have hE := hendpointCount
    omega
  have hcardJ : Fintype.card J ≤ 8192 := by
    simp only [J, Fintype.card_sum, Fintype.card_sigma, Fintype.card_fin]
    exact hbudget
  have hcontract : CanonicalPacketPortContract P
      (Finset.univ.biUnion packet) v :=
    canonicalPacketFamily_contract packet (Finset.univ.biUnion packet) v
      ⟨hsorted, rfl, hdisjoint, hcard⟩
  have hPcount : P.count = Fintype.card J := rfl
  refine ⟨P, ?_, hcontract⟩
  rw [hPcount]
  exact hcardJ
set_option maxRecDepth 1000

/-- Pool the exact tails chosen by a full-block decomposition together with a
pairwise-disjoint family of endpoint packets. The resulting canonical family
is supported precisely on those tails and endpoints. -/
theorem canonicalStreamFullBlock_exceptionPool {N : Nat} {α I E : Type}
    [LinearOrder α] [Fintype I] [Fintype E]
    {P : I → CanonicalPacketFamily N} {support : I → Finset (Fin N)}
    {v : Fin N → α} (D : CanonicalStreamFullBlockData P support v)
    (hStreamCount : Fintype.card I ≤ 129)
    (hSupportDisjoint : ∀ i i', i ≠ i' → Disjoint (support i) (support i'))
    (endpoint : E → Finset (Fin N))
    (hEndpointCount : Fintype.card E ≤ 65)
    (hEndpointSorted : ∀ e, RankSortedOn (endpoint e) v)
    (hEndpointCard : ∀ e, (endpoint e).card = 64)
    (hEndpointDisjoint : ∀ e e', e ≠ e' → Disjoint (endpoint e) (endpoint e'))
    (hStreamEndpoint : ∀ i e, Disjoint (support i) (endpoint e)) :
    ∃ Q : CanonicalPacketFamily N,
      Q.count ≤ 8192 ∧
      CanonicalPacketPortContract Q (Finset.univ.biUnion Q.packet) v ∧
      Finset.univ.biUnion Q.packet =
        Finset.univ.biUnion (canonicalStreamFullBlockExceptionPacket D endpoint) := by
  classical
  let residue : I → Nat := D.remainder
  let packet : ((Σ i : I, Fin (residue i)) ⊕ E) → Finset (Fin N) := fun j =>
    canonicalStreamFullBlockExceptionPacket D endpoint j
  have hresidue : ∀ i, residue i < 64 := by
    intro i
    rcases D.perStream i with ⟨_, hlt, _, _, _, _, _, _, _, _, _, _⟩
    exact hlt
  have hsorted : ∀ j, RankSortedOn (packet j) v := by
    intro j
    cases j with
    | inl ij =>
        rcases ij with ⟨i, k⟩
        rcases D.perStream i with
          ⟨_, _, _, _, _, _, _, htailSorted, htailStrict, _, _, _⟩
        simpa [packet, packetEmbeddingSupport] using
          rankSortedOn_packetEmbedding_range (D.tail i k) (htailStrict k) v
            (htailSorted k)
    | inr e =>
        simpa [packet] using hEndpointSorted e
  have hdisjoint : ∀ j j', j ≠ j' → Disjoint (packet j) (packet j') := by
    intro j j' hj
    cases j with
    | inl ij =>
        rcases ij with ⟨i, k⟩
        cases j' with
        | inl i'k' =>
            rcases i'k' with ⟨i', k'⟩
            by_cases hii' : i = i'
            · subst i'
              have hkk' : k ≠ k' := by
                intro h
                apply hj
                subst k'
                rfl
              rcases D.perStream i with
                ⟨_, _, _, _, _, _, _, _, _, _, htailPairwise, _⟩
              apply Finset.disjoint_left.mpr
              intro w hw hw'
              obtain ⟨x, hx⟩ :=
                (packetEmbeddingSupport_mem_iff (D.tail i k) w).mp (by simpa [packet] using hw)
              obtain ⟨y, hy⟩ :=
                (packetEmbeddingSupport_mem_iff (D.tail i k') w).mp (by simpa [packet] using hw')
              exact htailPairwise k k' hkk' x y (hx.trans hy.symm)
            · apply Finset.disjoint_left.mpr
              intro w hw hw'
              have hiw : w ∈ support i :=
                D.tail_subset_support i k (by simpa [packet] using hw)
              have hi'w : w ∈ support i' :=
                D.tail_subset_support i' k' (by simpa [packet] using hw')
              exact (Finset.disjoint_left.mp (hSupportDisjoint i i' hii') hiw) hi'w
        | inr e =>
            apply Finset.disjoint_left.mpr
            intro w hw hw'
            have hiw : w ∈ support i :=
              D.tail_subset_support i k (by simpa [packet] using hw)
            exact (Finset.disjoint_left.mp (hStreamEndpoint i e) hiw) (by simpa [packet] using hw')
    | inr e =>
        cases j' with
        | inl ik =>
            rcases ik with ⟨i, k⟩
            apply Finset.disjoint_left.mpr
            intro w hw hw'
            have hiw : w ∈ support i :=
              D.tail_subset_support i k (by simpa [packet] using hw')
            exact (Finset.disjoint_left.mp (hStreamEndpoint i e) hiw)
              (by simpa [packet] using hw)
        | inr e' =>
            have hee' : e ≠ e' := by
              intro h
              apply hj
              subst e'
              rfl
            simpa [packet] using hEndpointDisjoint e e' hee'
  have hcard : ∀ j, (packet j).card = 64 := by
    intro j
    cases j with
    | inl ij =>
        rcases ij with ⟨i, k⟩
        exact packetEmbeddingSupport_card (D.tail i k)
    | inr e => exact hEndpointCard e
  obtain ⟨Q, hcount, hcontract⟩ :=
    canonicalExceptionPool_family v residue hStreamCount hresidue packet
      hEndpointCount hsorted hdisjoint hcard
  exact ⟨Q, hcount, ⟨hcontract.1, rfl, hcontract.2.2.1, hcontract.2.2.2⟩,
    by simpa [packet, residue, canonicalStreamFullBlockExceptionPacket] using hcontract.2.1⟩

/-- The regular full blocks and the exact-tail exception pool form one exact
support partition of the receiver. -/
theorem canonicalStreamFullBlock_exceptionPool_partition
    {N : Nat} {α I E : Type} [LinearOrder α] [Fintype I] [Fintype E]
    {P : I → CanonicalPacketFamily N} {support : I → Finset (Fin N)}
    {v : Fin N → α} (D : CanonicalStreamFullBlockData P support v)
    (hStreamCount : Fintype.card I ≤ 129)
    (hSupportDisjoint : ∀ i i', i ≠ i' → Disjoint (support i) (support i'))
    (endpoint : E → Finset (Fin N)) (hEndpointCount : Fintype.card E ≤ 65)
    (hEndpointSorted : ∀ e, RankSortedOn (endpoint e) v)
    (hEndpointCard : ∀ e, (endpoint e).card = 64)
    (hEndpointDisjoint : ∀ e e', e ≠ e' → Disjoint (endpoint e) (endpoint e'))
    (hStreamEndpoint : ∀ i e, Disjoint (support i) (endpoint e))
    (receiver : Finset (Fin N))
    (hReceiverCover : Finset.univ.biUnion support ∪
      Finset.univ.biUnion endpoint = receiver) :
    ∃ Q : CanonicalPacketFamily N,
      Q.count ≤ 8192 ∧
      CanonicalPacketPortContract Q (Finset.univ.biUnion Q.packet) v ∧
      Finset.univ.biUnion Q.packet =
        Finset.univ.biUnion (canonicalStreamFullBlockExceptionPacket D endpoint) ∧
      ∀ w, w ∈ receiver ↔
        (∃ i, ∃ e ∈ D.blocks i, w ∈ Set.range e) ∨
          w ∈ Finset.univ.biUnion Q.packet := by
  obtain ⟨Q, hcount, hcontract, hQsupport⟩ :=
    canonicalStreamFullBlock_exceptionPool D hStreamCount hSupportDisjoint
      endpoint hEndpointCount hEndpointSorted hEndpointCard hEndpointDisjoint
      hStreamEndpoint
  refine ⟨Q, hcount, hcontract, hQsupport, ?_⟩
  intro w
  rw [← hReceiverCover]
  constructor
  · intro hw
    rcases Finset.mem_union.mp hw with hs | he
    · obtain ⟨i, -, hi⟩ := Finset.mem_biUnion.mp hs
      rcases D.perStream i with
        ⟨_, _, _, _, _, _, _, _, _, _, _, hlocalCover⟩
      rcases (hlocalCover w).mpr hi with hblock | htail
      · left
        obtain ⟨e, he, hrange⟩ := hblock
        exact ⟨i, e, he, hrange⟩
      · right
        obtain ⟨j, hrange⟩ := htail
        rw [hQsupport]
        apply Finset.mem_biUnion.mpr
        refine ⟨Sum.inl ⟨i, j⟩, Finset.mem_univ _, ?_⟩
        exact (packetEmbeddingSupport_mem_iff (D.tail i j) w).2 hrange
    · obtain ⟨e, -, he⟩ := Finset.mem_biUnion.mp he
      right
      rw [hQsupport]
      apply Finset.mem_biUnion.mpr
      exact ⟨Sum.inr e, Finset.mem_univ _, he⟩
  · rintro (hblock | hpool)
    · rcases hblock with ⟨i, e, he, hrange⟩
      apply Finset.mem_union.mpr
      left
      apply Finset.mem_biUnion.mpr
      exact ⟨i, Finset.mem_univ _, D.block_subset_support i e he hrange⟩
    · rw [hQsupport] at hpool
      obtain ⟨j, -, hj⟩ := Finset.mem_biUnion.mp hpool
      cases j with
      | inl ij =>
          rcases ij with ⟨i, k⟩
          apply Finset.mem_union.mpr
          left
          apply Finset.mem_biUnion.mpr
          exact ⟨i, Finset.mem_univ _, D.tail_subset_support i k hj⟩
      | inr e =>
          apply Finset.mem_union.mpr
          right
          apply Finset.mem_biUnion.mpr
          exact ⟨e, Finset.mem_univ _, hj⟩

/-- Data form of the standard full-block decomposition for one canonical
packet family. -/
structure CanonicalPacketFullBlockData {N : Nat} {α : Type} [LinearOrder α]
    (P : CanonicalPacketFamily N) (support : Finset (Fin N)) (v : Fin N → α) where
  fullGroups : Nat
  remainder : Nat
  tail : Fin remainder → Fin 64 ↪ Fin N
  blocks : List (Fin 4096 ↪ Fin N)
  count_eq : fullGroups * 64 + remainder = P.count
  remainder_lt : remainder < 64
  blocks_nodup : blocks.Nodup
  blocks_disjoint : ∀ e ∈ blocks, ∀ f ∈ blocks, e ≠ f → ∀ x y, e x ≠ f y
  depth_le : (genScatterMergeTreeBatch (packetPowerTree6 (α := α)) blocks).depth ≤ 57
  block_sorted : ∀ e ∈ blocks, Monotone (fun i =>
    (genScatterMergeTreeBatch (packetPowerTree6 (α := α)) blocks).exec v (e i))
  output_sorted : ∀ e ∈ blocks, ∀ j : Fin (packetPowerTree6 (α := α)).leafCount,
    Monotone (fun i =>
      (genScatterMergeTreeBatch (packetPowerTree6 (α := α)) blocks).exec v
        (genScatterMergeTreeOutputEmbedding (packetPowerTree6 (α := α)) e j i))
  tail_sorted : ∀ j, Monotone (fun i => v (tail j i))
  tail_strictMono : ∀ j, StrictMono (tail j)
  block_tail_disjoint : ∀ e ∈ blocks, ∀ i j k, e i ≠ tail j k
  tail_pairwise : ∀ j j', j ≠ j' → ∀ x y, tail j x ≠ tail j' y
  support_cover : ∀ w,
    ((∃ e ∈ blocks, w ∈ Set.range e) ∨ ∃ j, w ∈ Set.range (tail j)) ↔
      w ∈ support
  provenance : CanonicalPacketFullBlockProvenance P fullGroups remainder blocks

/-- Union of the physical supports of a finite list of 4096-wire embeddings. -/
noncomputable def packetBlockListSupport {N : Nat}
    (blocks : List (Fin 4096 ↪ Fin N)) : Finset (Fin N) := by
  classical
  exact blocks.toFinset.biUnion (fun e => Finset.univ.image e)

theorem packetBlockListSupport_mem_iff {N : Nat}
    (blocks : List (Fin 4096 ↪ Fin N)) (w : Fin N) :
    w ∈ packetBlockListSupport blocks ↔
      ∃ e ∈ blocks, w ∈ Set.range e := by
  classical
  simp [packetBlockListSupport, Set.mem_range]

/-- Replacing every full block by its merge-tree output chunks preserves the
physical support exactly. -/
theorem packetBlockListSupport_eq_outputChunks {N : Nat} {α : Type}
    [LinearOrder α] (tree : PacketMergeTree α 4096)
    (blocks : List (Fin 4096 ↪ Fin N)) (w : Fin N) :
    w ∈ packetBlockListSupport blocks ↔
      ∃ e ∈ blocks, ∃ j : Fin tree.leafCount,
        w ∈ Set.range (genScatterMergeTreeOutputEmbedding tree e j) := by
  rw [packetBlockListSupport_mem_iff]
  constructor
  · rintro ⟨e, he, hw⟩
    exact ⟨e, he, (genScatterMergeTreeOutputEmbedding_support_iff tree e w).2 hw⟩
  · rintro ⟨e, he, j, hw⟩
    exact ⟨e, he, (genScatterMergeTreeOutputEmbedding_support_iff tree e w).1
      ⟨j, hw⟩⟩

/-- The exact exception pool is disjoint from every regular full block:
it contains only stream residues and endpoint packets. -/
theorem canonicalStreamFullBlock_blocks_disjoint_exceptionPool
    {N : Nat} {α I E : Type} [LinearOrder α] [Fintype I]
    [Fintype E] [DecidableEq E]
    {P : I → CanonicalPacketFamily N}
    {support : I → Finset (Fin N)} {v : Fin N → α}
    (D : CanonicalStreamFullBlockData P support v)
    (endpoint : E → Finset (Fin N))
    (hsupport : ∀ i i', i ≠ i' → Disjoint (support i) (support i'))
    (hendpoint : ∀ i e, Disjoint (support i) (endpoint e))
    (i : I) :
    Disjoint (packetBlockListSupport (D.blocks i))
      (Finset.univ.biUnion
        (canonicalStreamFullBlockExceptionPacket D endpoint)) := by
  classical
  apply Finset.disjoint_left.mpr
  intro w hwBlock hwException
  obtain ⟨e, he, x, rfl⟩ := (packetBlockListSupport_mem_iff (D.blocks i) w).mp hwBlock
  obtain ⟨j, -, hj⟩ := Finset.mem_biUnion.mp hwException
  cases j with
  | inl ij =>
      rcases ij with ⟨i', k⟩
      have htail : e x ∈ packetEmbeddingSupport (D.tail i' k) := by
        simpa [canonicalStreamFullBlockExceptionPacket] using hj
      obtain ⟨y, hy⟩ := (packetEmbeddingSupport_mem_iff (D.tail i' k) (e x)).mp htail
      by_cases hii : i = i'
      · subst i'
        rcases D.perStream i with
          ⟨_, _, _, _, _, _, _, _, _, hblockTail, _, _⟩
        exact (hblockTail e he x k y) hy.symm
      · have hblockIn : e x ∈ support i := D.block_subset_support i e he (Set.mem_range_self x)
        have htailIn : e x ∈ support i' := D.tail_subset_support i' k htail
        exact (Finset.disjoint_left.mp (hsupport i i' hii)) hblockIn
          htailIn
  | inr ep =>
      have hblockIn : e x ∈ support i := D.block_subset_support i e he (Set.mem_range_self x)
      exact (Finset.disjoint_left.mp (hendpoint i ep)) hblockIn hj
/-- Package the existing full-block theorem as reusable batch data. -/
theorem canonicalPacketFamily_fullBlocks_data {N : Nat} {α : Type}
    [LinearOrder α] (P : CanonicalPacketFamily N) (support : Finset (Fin N))
    (v : Fin N → α) (hcontract : CanonicalPacketPortContract P support v) :
    Nonempty (CanonicalPacketFullBlockData P support v) := by
  obtain ⟨q, r, hqr, hr, tail, blocks, hnd, hdis, hdepth, hblockSorted,
      houtputSorted, htailSorted, htailStrict, hblockTail, htailPairwise,
      ⟨hcover, hprovenance⟩⟩ :=
    canonicalPacketFamily_fullBlocks_with_tail P support v hcontract
  exact ⟨⟨q, r, tail, blocks, hqr, hr, hnd, hdis, hdepth, hblockSorted,
    houtputSorted, htailSorted, htailStrict, hblockTail, htailPairwise, hcover,
    Classical.choice hprovenance⟩⟩

/-- The last fewer-than-64 packets of a canonical stream form a canonical
sorted, disjoint packet family in their own right. This exposes the actual
residue supports needed by the cross-stream exception pool. -/
theorem canonicalPacketFamily_residue_contract {N : Nat} {α : Type}
    [LinearOrder α] (P : CanonicalPacketFamily N)
    (support : Finset (Fin N)) (v : Fin N → α)
    (hcontract : CanonicalPacketPortContract P support v) :
    ∃ q r, q * 64 + r = P.count ∧ r < 64 ∧
      ∃ tail : CanonicalPacketFamily N,
        tail.count = r ∧
        CanonicalPacketPortContract tail (Finset.univ.biUnion tail.packet) v ∧
        (∀ (hqr : q * 64 + r = P.count) (hcount : tail.count = r)
          (j : Fin r),
          tail.packet (Fin.cast hcount.symm j) ⊆
            P.packet ⟨q * 64 + j.val, by rw [← hqr]; have hj := j.isLt; omega⟩) := by
  let q := P.count / 64
  let r := P.count % 64
  have hqr : q * 64 + r = P.count := by
    dsimp [q, r]
    have h := Nat.mod_add_div P.count 64
    omega
  have hr : r < 64 := by dsimp [r]; exact Nat.mod_lt _ (by omega)
  let tailIndex : Fin r → Fin P.count := fun j =>
    ⟨q * 64 + j.val, by rw [← hqr]; have hj := j.isLt; omega⟩
  have htailIndex_inj : Function.Injective tailIndex := by
    intro i j hij
    apply Fin.ext
    have hv := congrArg Fin.val hij
    simp only [tailIndex, Fin.mk_val] at hv
    omega
  let tail : CanonicalPacketFamily N := ⟨r, fun j => P.packet (tailIndex j)⟩
  have htail : CanonicalPacketPortContract tail
      (Finset.univ.biUnion tail.packet) v := by
    refine ⟨?_, rfl, ?_, ?_⟩
    · intro j
      exact hcontract.1 (tailIndex j)
    · intro i j hne
      exact hcontract.2.2.1 (tailIndex i) (tailIndex j)
        (fun heq => hne (htailIndex_inj heq))
    · intro j
      exact hcontract.2.2.2 (tailIndex j)
  have htailSubset : ∀ (hqr' : q * 64 + r = P.count)
      (hcount : tail.count = r) (j : Fin r),
      tail.packet (Fin.cast hcount.symm j) ⊆
        P.packet ⟨q * 64 + j.val, by rw [← hqr']; have hj := j.isLt; omega⟩ := by
    intro hqr' hcount j
    have hidx : tailIndex j =
        ⟨q * 64 + j.val, by rw [← hqr']; have hj := j.isLt; omega⟩ := by
      apply Fin.ext
      simp [tailIndex]
    simpa [tail, hcount] using (show P.packet (tailIndex j) ⊆ P.packet (tailIndex j) from
      Finset.Subset.rfl) |>.trans (by rw [hidx])
  exact ⟨q, r, hqr, hr, tail, rfl, htail, htailSubset⟩

/-- Assemble already-extracted stream residues and endpoint packets into the
bounded canonical exception pool. Cross-stream disjointness follows from
disjoint stream supports and the supplied packet-subset witness. -/
theorem canonicalStreamResidues_exceptionPool {N : Nat} {α I E : Type}
    [LinearOrder α] [Fintype I] [Fintype E]
    (v : Fin N → α)
    (stream : I → CanonicalPacketFamily N)
    (streamSupport : I → Finset (Fin N))
    (hstreamCount : Fintype.card I ≤ 129)
    (hstream : ∀ i, CanonicalPacketPortContract (stream i) (streamSupport i) v)
    (hstreamDisjoint : ∀ i j, i ≠ j → Disjoint (streamSupport i) (streamSupport j))
    (residue : I → CanonicalPacketFamily N)
    (hresidueCount : ∀ i, (residue i).count < 64)
    (hresidue : ∀ i, CanonicalPacketPortContract (residue i)
      (Finset.univ.biUnion (residue i).packet) v)
    (hresidueSubset : ∀ i j, ∃ k, (residue i).packet j ⊆ (stream i).packet k)
    (endpoint : E → Finset (Fin N))
    (hendpointSorted : ∀ e, RankSortedOn (endpoint e) v)
    (hendpointCount : Fintype.card E ≤ 65)
    (hendpointCard : ∀ e, (endpoint e).card = 64)
    (hendpointDisjoint : ∀ e e', e ≠ e' → Disjoint (endpoint e) (endpoint e'))
    (hstreamEndpointDisjoint : ∀ i e, Disjoint (streamSupport i) (endpoint e)) :
    ∃ P : CanonicalPacketFamily N,
      P.count ≤ 8192 ∧
      CanonicalPacketPortContract P
        (Finset.univ.biUnion (fun idx : (Σ i : I, Fin (residue i).count) ⊕ E =>
          match idx with
          | Sum.inl ij => (residue ij.1).packet ij.2
          | Sum.inr e => endpoint e)) v := by
  classical
  let poolPacket : ((Σ i : I, Fin (residue i).count) ⊕ E) → Finset (Fin N) :=
    fun i => match i with
      | Sum.inl ij => (residue ij.1).packet ij.2
      | Sum.inr e => endpoint e
  have hsorted : ∀ i, RankSortedOn (poolPacket i) v := by
    intro i
    cases i with
    | inl ij => exact (hresidue ij.1).1 ij.2
    | inr e => exact hendpointSorted e
  have hcard : ∀ i, (poolPacket i).card = 64 := by
    intro i
    cases i with
    | inl ij => exact (hresidue ij.1).2.2.2 ij.2
    | inr e => exact hendpointCard e
  have hstreamSupportSubset (i : I) (j : Fin (residue i).count) :
      (residue i).packet j ⊆ streamSupport i := by
    obtain ⟨k, hsub⟩ := hresidueSubset i j
    intro w hw
    have hmem : w ∈ Finset.univ.biUnion (stream i).packet := by
      simp only [Finset.mem_biUnion, Finset.mem_univ, true_and]
      exact ⟨k, hsub hw⟩
    rw [← (hstream i).2.1]
    exact hmem
  have hdisjoint : ∀ i j, i ≠ j → Disjoint (poolPacket i) (poolPacket j) := by
    intro i j hne
    cases i with
    | inl a =>
      cases j with
      | inl b =>
        by_cases hsame : a.1 = b.1
        · rcases b with ⟨bi, bj⟩
          cases hsame
          exact (hresidue a.1).2.2.1 a.2 bj (by
            intro h
            apply hne
            have hsigma : a = ⟨a.1, bj⟩ := by
              apply Sigma.ext
              · rfl
              · cases h
                exact HEq.rfl
            exact congrArg Sum.inl hsigma)
        · apply Finset.disjoint_left.mpr
          intro w hwA hwB
          have hAw := hstreamSupportSubset a.1 a.2 hwA
          have hBw := hstreamSupportSubset b.1 b.2 hwB
          exact (Finset.disjoint_left.mp (hstreamDisjoint a.1 b.1 hsame)) hAw hBw
      | inr e =>
        apply Finset.disjoint_left.mpr
        intro w hwA hwE
        exact (Finset.disjoint_left.mp (hstreamEndpointDisjoint a.1 e))
          (hstreamSupportSubset a.1 a.2 hwA) hwE
    | inr e =>
      cases j with
      | inl a =>
        apply Finset.disjoint_left.mpr
        intro w hwE hwA
        exact (Finset.disjoint_left.mp (hstreamEndpointDisjoint a.1 e).symm)
          hwE (hstreamSupportSubset a.1 a.2 hwA)
      | inr e' =>
        exact hendpointDisjoint e e' (by
          intro he
          apply hne
          simp [he])
  exact canonicalExceptionPool_family v (fun i => (residue i).count) hstreamCount
    hresidueCount poolPacket
    hendpointCount hsorted hdisjoint hcard

/-- Extract the two regular rank-cell streams from an actual shifted
source-port repair.  The repaired endpoint pair is deliberately left out of
these contracts, so its support can be counted with the other pooled
exceptions. -/
theorem flowA7_shiftedUp_regularStreams_contract {d : Nat} {α : Type}
    [LinearOrder α] (hd : 7 ≤ d) (t : Nat) (ht2 : 2 ≤ t)
    (ht : t < tf7 d) (b : KBag 64 d)
    (hdown : 0 < flowDown7 d hd b.l t)
    (hbad : HalfMisaligned (flowUp7 d hd b.l t))
    (v : Fin (64 ^ d) → α)
    (hpack : PacketSortedOn (wireSets (flowSizes7 d hd) t b) v) :
    let S := wireSets (flowSizes7 d hd) t b
    let π := flowUp7 d hd b.l t
    let q := π / 2 / 64
    let stageV := (flowA7_sourcePortRepairStage hd t ht2 ht).exec v
    CanonicalPacketPortContract ⟨q, fun k => rankPacketCell S 0 k⟩
      (Chvatal.blockOf S 0 (64 * q)) stageV ∧
    CanonicalPacketPortContract
      ⟨q, fun k => rankPacketCell S (S.card - π / 2 + 32) k⟩
      (Chvatal.blockOf S (S.card - π / 2 + 32) S.card) stageV := by
  let S := wireSets (flowSizes7 d hd) t b
  let π := flowUp7 d hd b.l t
  let τ := flowDown7 d hd b.l t
  let q := π / 2 / 64
  let stageV := (flowA7_sourcePortRepairStage hd t ht2 ht).exec v
  have hshape := node_shape_refined d hd t b.l ht2 ht
  have hres := refined_packet_residues hd ht2 ht hshape
  have hπeven : 2 ∣ π := by
    dsimp [π]
    exact (flowSizes7 d hd).hup_even b.l t ht
  have hhalf : π / 2 = 64 * q + 32 := by
    have hmod := Nat.mod_add_div (π / 2) 64
    rw [hbad.2] at hmod
    dsimp [q] at hmod ⊢
    omega
  have hπeq : π = 64 * (2 * q + 1) := by
    have htwice : π = 2 * (π / 2) :=
      (Nat.mul_div_cancel' hπeven).symm
    rw [htwice, hhalf]
    omega
  have hbag : S.card = π + 64 * τ := by
    dsimp [S, π, τ]
    rw [wireSets_card (flowSizes7 d hd) (Nat.le_of_lt ht) b]
    exact (flowSizes7 d hd).hsplit b.l t b.hl ht
  have hπle : π ≤ S.card := by rw [hbag]; omega
  have hprefixFinish : 64 * q ≤ S.card := by rw [hπeq] at hπle; omega
  have hsuffixFinish : S.card - π / 2 + 32 + 64 * q ≤ S.card := by
    rw [hhalf]
    omega
  have hfam := flowA7_sourcePortRepairStage_upSetFamily
    hd t ht2 ht b hdown hbad v hpack
  have hprefix : ∀ k : Fin q, RankSortedOn (rankPacketCell S 0 k) stageV := by
    intro k
    have hk := hfam.1 (Sum.inr (Sum.inl k))
    simpa [S, π, q, stageV, upSetRepairPacket, upSetPrefixCell] using hk
  have hsuffix : ∀ k : Fin q,
      RankSortedOn (rankPacketCell S (S.card - π / 2 + 32) k) stageV := by
    intro k
    have hk := hfam.1 (Sum.inr (Sum.inr k))
    simpa [S, π, q, stageV, upSetRepairPacket, upSetSuffixCell] using hk
  constructor
  · simpa [S, π, q, stageV] using
      rankPacketCell_stream_contract S stageV 0 q hprefix (by
        simpa using hprefixFinish)
  · have hcontract := rankPacketCell_stream_contract S stageV
      (S.card - π / 2 + 32) q hsuffix hsuffixFinish
    have hend : S.card - π / 2 + 32 + 64 * q = S.card := by
      rw [hhalf]
      omega
    simpa [S, π, q, stageV, hend] using hcontract

/-- Expose the exceptional endpoint packet of an actual shifted child
up-port, including its exact size and containment in the selected port. -/
theorem flowA7_shiftedUp_endpoint_contract {d : Nat} {α : Type}
    [LinearOrder α] (hd : 7 ≤ d) (t : Nat) (ht2 : 2 ≤ t)
    (ht : t < tf7 d) (b : KBag 64 d)
    (hdown : 0 < flowDown7 d hd b.l t)
    (hbad : HalfMisaligned (flowUp7 d hd b.l t))
    (v : Fin (64 ^ d) → α)
    (hpack : PacketSortedOn (wireSets (flowSizes7 d hd) t b) v) :
    let S := wireSets (flowSizes7 d hd) t b
    let π := flowUp7 d hd b.l t
    let q := π / 2 / 64
    let packet := upSetRepairPacket S π q (Sum.inl ())
    let stageV := (flowA7_sourcePortRepairStage hd t ht2 ht).exec v
    RankSortedOn packet stageV ∧ packet.card = 64 ∧
      packet ⊆ Chvatal.upSet S π ∧
      (∀ k : Fin q, Disjoint packet
        (upSetRepairPacket S π q (Sum.inr (Sum.inl k)))) ∧
      (∀ k : Fin q, Disjoint packet
        (upSetRepairPacket S π q (Sum.inr (Sum.inr k)))) := by
  let S := wireSets (flowSizes7 d hd) t b
  let π := flowUp7 d hd b.l t
  let q := π / 2 / 64
  let packet := upSetRepairPacket S π q (Sum.inl ())
  let stageV := (flowA7_sourcePortRepairStage hd t ht2 ht).exec v
  have hfam := flowA7_sourcePortRepairStage_upSetFamily
    hd t ht2 ht b hdown hbad v hpack
  have hsorted := hfam.1 (Sum.inl ())
  have hcard := hfam.2.2.2 (Sum.inl ())
  have hsubset : packet ⊆ Chvatal.upSet S π := by
    intro w hw
    have hmem : w ∈ Finset.univ.biUnion (upSetRepairPacket S π q) := by
      simp only [Finset.mem_biUnion, Finset.mem_univ, true_and]
      exact ⟨Sum.inl (), hw⟩
    rw [hfam.2.1] at hmem
    exact hmem
  have hprefixDisjoint : ∀ k : Fin q, Disjoint packet
      (upSetRepairPacket S π q (Sum.inr (Sum.inl k))) := by
    intro k
    exact hfam.2.2.1 (Sum.inl ()) (Sum.inr (Sum.inl k)) (by simp)
  have hsuffixDisjoint : ∀ k : Fin q, Disjoint packet
      (upSetRepairPacket S π q (Sum.inr (Sum.inr k))) := by
    intro k
    exact hfam.2.2.1 (Sum.inl ()) (Sum.inr (Sum.inr k)) (by simp)
  exact ⟨by simpa [packet, S, π, q, stageV] using hsorted,
    by simpa [packet, S, π, q] using hcard,
    by simpa [packet, S, π, q] using hsubset,
    by simpa [packet, S, π, q] using hprefixDisjoint,
    by simpa [packet, S, π, q] using hsuffixDisjoint⟩

/-- The shifted child up-selector decomposes its actual port into two
rank-interval stream families and one sorted endpoint packet, with exact
support coverage. -/
theorem flowA7_shiftedUp_port_partition {d : Nat} {α : Type}
    [LinearOrder α] (hd : 7 ≤ d) (t : Nat) (ht2 : 2 ≤ t)
    (ht : t < tf7 d) (b : KBag 64 d)
    (hdown : 0 < flowDown7 d hd b.l t)
    (hbad : HalfMisaligned (flowUp7 d hd b.l t))
    (v : Fin (64 ^ d) → α)
    (hpack : PacketSortedOn (wireSets (flowSizes7 d hd) t b) v) :
    let S := wireSets (flowSizes7 d hd) t b
    let π := flowUp7 d hd b.l t
    let q := π / 2 / 64
    let stageV := (flowA7_sourcePortRepairStage hd t ht2 ht).exec v
    let A : CanonicalPacketFamily (64 ^ d) := ⟨q, fun k => rankPacketCell S 0 k⟩
    let B : CanonicalPacketFamily (64 ^ d) :=
      ⟨q, fun k => rankPacketCell S (S.card - π / 2 + 32) k⟩
    let endpoint := upSetRepairPacket S π q (Sum.inl ())
    CanonicalPacketPortContract A (Chvatal.blockOf S 0 (64 * q)) stageV ∧
    CanonicalPacketPortContract B
      (Chvatal.blockOf S (S.card - π / 2 + 32) S.card) stageV ∧
    RankSortedOn endpoint stageV ∧ endpoint.card = 64 ∧
    endpoint ⊆ Chvatal.upSet S π ∧
    Finset.univ.biUnion A.packet ∪ Finset.univ.biUnion B.packet ∪ endpoint =
      Chvatal.upSet S π ∧
    Disjoint (Finset.univ.biUnion A.packet) (Finset.univ.biUnion B.packet) ∧
    Disjoint endpoint (Finset.univ.biUnion A.packet) ∧
    Disjoint endpoint (Finset.univ.biUnion B.packet) := by
  let S := wireSets (flowSizes7 d hd) t b
  let π := flowUp7 d hd b.l t
  let q := π / 2 / 64
  let stageV := (flowA7_sourcePortRepairStage hd t ht2 ht).exec v
  let A : CanonicalPacketFamily (64 ^ d) := ⟨q, fun k => rankPacketCell S 0 k⟩
  let B : CanonicalPacketFamily (64 ^ d) :=
    ⟨q, fun k => rankPacketCell S (S.card - π / 2 + 32) k⟩
  let endpoint := upSetRepairPacket S π q (Sum.inl ())
  have hstreams := flowA7_shiftedUp_regularStreams_contract
    hd t ht2 ht b hdown hbad v hpack
  have hendpoint := flowA7_shiftedUp_endpoint_contract
    hd t ht2 ht b hdown hbad v hpack
  have hshape := node_shape_refined d hd t b.l ht2 ht
  have hres := refined_packet_residues hd ht2 ht hshape
  have hπeven : 2 ∣ π := by
    dsimp [π]
    exact (flowSizes7 d hd).hup_even b.l t ht
  have hhalf : π / 2 = 64 * q + 32 := by
    have hmod := Nat.mod_add_div (π / 2) 64
    rw [hbad.2] at hmod
    dsimp [q]
    omega
  have hπeq : π = 64 * (2 * q + 1) := by
    have htwice : π = 2 * (π / 2) := (Nat.mul_div_cancel' hπeven).symm
    rw [htwice, hhalf]
    omega
  have hSdiv : 64 ∣ S.card := by
    rw [wireSets_card (flowSizes7 d hd) (Nat.le_of_lt ht) b]
    exact hres.1
  obtain ⟨C, hScard⟩ := hSdiv
  have hbag : S.card = π + 64 * flowDown7 d hd b.l t := by
    dsimp [S, π]
    rw [wireSets_card (flowSizes7 d hd) (Nat.le_of_lt ht) b]
    exact (flowSizes7 d hd).hsplit b.l t b.hl ht
  have hπcard : π ≤ S.card := by rw [hbag]; omega
  have hprefix : Finset.univ.biUnion A.packet =
      Finset.univ.biUnion (fun k : Fin q => upSetPrefixCell S k) := by
    rw [hstreams.1.2.1]
    simpa [A, upSetPrefixCell] using blockOf_packetCell_partition S 0 q
  have hsufEnd : S.card - π / 2 + 32 + 64 * q = S.card := by
    rw [hbag, hhalf, hπeq]
    omega
  have hsuffix : Finset.univ.biUnion B.packet =
      Finset.univ.biUnion (fun k : Fin q => upSetSuffixCell S π k) := by
    rw [hstreams.2.2.1]
    have hpart := blockOf_packetCell_partition S (S.card - π / 2 + 32) q
    rw [hsufEnd] at hpart
    simpa [B, upSetSuffixCell] using hpart
  have hpartition := upSetEndpoint_partition S π q C hπeq hScard hπcard
  have hAB : Disjoint (Finset.univ.biUnion A.packet)
      (Finset.univ.biUnion B.packet) := by
    apply Finset.disjoint_left.mpr
    intro w hwA hwB
    rw [hstreams.1.2.1] at hwA
    rw [hstreams.2.2.1] at hwB
    have ha := Chvatal.mem_blockOf.mp hwA
    have hb := Chvatal.mem_blockOf.mp hwB
    have htotal : 128 * q + 64 ≤ S.card := by
      rw [hπeq] at hπcard
      omega
    have hstart : 64 * q < S.card - π / 2 + 32 := by
      rw [hhalf]
      omega
    rcases ha with ⟨_, _, haHi⟩
    rcases hb with ⟨_, hbLo, _⟩
    have hrank : 64 * q < Chvatal.rankIn S w := lt_of_lt_of_le hstart hbLo
    change Chvatal.rankIn S w < 64 * q at haHi
    omega
  have hEA : Disjoint endpoint (Finset.univ.biUnion A.packet) := by
    apply Finset.disjoint_left.mpr
    intro w hwe hwa
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and] at hwa
    obtain ⟨k, hwa⟩ := hwa
    have hsel := hendpoint.2.2.2.1 k
    have hwa' : w ∈ upSetRepairPacket S π q (Sum.inr (Sum.inl k)) := by
      simpa [A, upSetRepairPacket, upSetPrefixCell] using hwa
    exact Finset.disjoint_left.mp hsel hwe hwa'
  have hEB : Disjoint endpoint (Finset.univ.biUnion B.packet) := by
    apply Finset.disjoint_left.mpr
    intro w hwe hwb
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and] at hwb
    obtain ⟨k, hwb⟩ := hwb
    have hsel := hendpoint.2.2.2.2 k
    have hwb' : w ∈ upSetRepairPacket S π q (Sum.inr (Sum.inr k)) := by
      simpa [B, upSetRepairPacket, upSetSuffixCell] using hwb
    exact Finset.disjoint_left.mp hsel hwe hwb'
  refine ⟨?_, ?_, hendpoint.1, hendpoint.2.1, hendpoint.2.2.1, ?_, hAB, hEA, hEB⟩
  · simpa [A, S, π, q, stageV] using hstreams.1
  · simpa [B, S, π, q, stageV] using hstreams.2
  · rw [hprefix, hsuffix]
    change (Finset.univ.biUnion (fun k : Fin q => upSetPrefixCell S k) ∪
      Finset.univ.biUnion (fun k : Fin q => upSetSuffixCell S π k)) ∪ endpoint =
        Chvatal.upSet S π
    rw [Finset.union_comm
      (Finset.univ.biUnion (fun k : Fin q => upSetPrefixCell S k) ∪
        Finset.univ.biUnion (fun k : Fin q => upSetSuffixCell S π k)) endpoint]
    simpa [endpoint, S, π, q] using hpartition.symm

/-- Extract the aligned interior stream from an actual shifted parent
down-cut.  The endpoint pair remains separate for exception pooling. -/
theorem flowA7_shiftedDown_interiorStream_contract {d : Nat} {α : Type}
    [LinearOrder α] (hd : 7 ≤ d) (t : Nat) (ht2 : 2 ≤ t)
    (ht : t < tf7 d) (b : KBag 64 d)
    (hdown : 0 < flowDown7 d hd b.l t)
    (hbad : HalfMisaligned (flowUp7 d hd b.l t))
    (j : Fin 64) (v : Fin (64 ^ d) → α)
    (hpack : PacketSortedOn (wireSets (flowSizes7 d hd) t b) v) :
    let S := wireSets (flowSizes7 d hd) t b
    let π := flowUp7 d hd b.l t
    let τ := flowDown7 d hd b.l t
    let m := τ / 64 - 1
    let lo := π / 2 + j.val * τ + 32
    let stageV := (flowA7_sourcePortRepairStage hd t ht2 ht).exec v
    CanonicalPacketPortContract ⟨m, fun k => rankPacketCell S lo k⟩
      (Chvatal.blockOf S lo (lo + 64 * m)) stageV := by
  let S := wireSets (flowSizes7 d hd) t b
  let π := flowUp7 d hd b.l t
  let τ := flowDown7 d hd b.l t
  let m := τ / 64 - 1
  let lo := π / 2 + j.val * τ + 32
  let stageV := (flowA7_sourcePortRepairStage hd t ht2 ht).exec v
  have hshape := node_shape_refined d hd t b.l ht2 ht
  have hres := refined_packet_residues hd ht2 ht hshape
  have hτdiv : 64 ∣ τ := by
    dsimp [τ]
    exact hres.2.1
  have hτeq : τ = 64 * (m + 1) := by
    have hmod := Nat.mod_add_div τ 64
    have hrem : τ % 64 = 0 := Nat.mod_eq_zero_of_dvd hτdiv
    rw [hrem] at hmod
    dsimp [m]
    omega
  have hbag : S.card = π + 64 * τ := by
    dsimp [S, π, τ]
    rw [wireSets_card (flowSizes7 d hd) (Nat.le_of_lt ht) b]
    exact (flowSizes7 d hd).hsplit b.l t b.hl ht
  have hinteriorEnd : j.val * τ + 32 + 64 * m + 32 = (j.val + 1) * τ := by
    rw [hτeq]
    ring
  have hjle : j.val + 1 ≤ 64 := by omega
  have hmul : (j.val + 1) * τ ≤ 64 * τ := Nat.mul_le_mul_right τ hjle
  have hfinish : lo + 64 * m ≤ S.card := by
    calc
      lo + 64 * m ≤ π / 2 + (j.val + 1) * τ := by
        dsimp [lo]
        omega
      _ ≤ π / 2 + 64 * τ := Nat.add_le_add_left hmul _
      _ ≤ π + 64 * τ := by omega
      _ = S.card := hbag.symm
  have hfam := flowA7_sourcePortRepairStage_downCutFamily
    hd t ht2 ht b hdown hbad v hpack
  have hcell : ∀ k : Fin m, RankSortedOn (rankPacketCell S lo k) stageV := by
    intro k
    have hk := (hfam j).1 (Sum.inr k)
    simpa [S, π, τ, m, lo, stageV, downSetRepairPacket,
      downSetInteriorCell, rankPacketCell] using hk
  exact rankPacketCell_stream_contract S stageV lo m hcell hfinish

/-- Expose the exceptional endpoint packet of an actual shifted parent
down-cut, including its exact size and containment in the selected port. -/
theorem flowA7_shiftedDown_endpoint_contract {d : Nat} {α : Type}
    [LinearOrder α] (hd : 7 ≤ d) (t : Nat) (ht2 : 2 ≤ t)
    (ht : t < tf7 d) (b : KBag 64 d)
    (hdown : 0 < flowDown7 d hd b.l t)
    (hbad : HalfMisaligned (flowUp7 d hd b.l t))
    (j : Fin 64) (v : Fin (64 ^ d) → α)
    (hpack : PacketSortedOn (wireSets (flowSizes7 d hd) t b) v) :
    let S := wireSets (flowSizes7 d hd) t b
    let π := flowUp7 d hd b.l t
    let τ := flowDown7 d hd b.l t
    let m := τ / 64 - 1
    let packet := downSetRepairPacket S π τ j m (Sum.inl ())
    let stageV := (flowA7_sourcePortRepairStage hd t ht2 ht).exec v
    RankSortedOn packet stageV ∧ packet.card = 64 ∧
      packet ⊆ Chvatal.downSet S π τ j.val ∧
      (∀ k : Fin m, Disjoint packet
        (downSetRepairPacket S π τ j m (Sum.inr k))) := by
  let S := wireSets (flowSizes7 d hd) t b
  let π := flowUp7 d hd b.l t
  let τ := flowDown7 d hd b.l t
  let m := τ / 64 - 1
  let packet := downSetRepairPacket S π τ j m (Sum.inl ())
  let stageV := (flowA7_sourcePortRepairStage hd t ht2 ht).exec v
  have hfam := flowA7_sourcePortRepairStage_downCutFamily
    hd t ht2 ht b hdown hbad v hpack
  have hsorted := (hfam j).1 (Sum.inl ())
  have hcard := (hfam j).2.2.2 (Sum.inl ())
  have hsubset : packet ⊆ Chvatal.downSet S π τ j.val := by
    intro w hw
    have hmem : w ∈ Finset.univ.biUnion
        (downSetRepairPacket S π τ j m) := by
      simp only [Finset.mem_biUnion, Finset.mem_univ, true_and]
      exact ⟨Sum.inl (), hw⟩
    rw [(hfam j).2.1] at hmem
    exact hmem
  have hdisjoint : ∀ k : Fin m, Disjoint packet
      (downSetRepairPacket S π τ j m (Sum.inr k)) := by
    intro k
    exact (hfam j).2.2.1 (Sum.inl ()) (Sum.inr k) (by simp)
  exact ⟨by simpa [packet, S, π, τ, m, stageV] using hsorted,
    by simpa [packet, S, π, τ, m] using hcard,
    by simpa [packet, S, π, τ, m] using hsubset,
    by simpa [packet, S, π, τ, m] using hdisjoint⟩

/-- A shifted parent down-cut is exactly its selected sorted endpoint packet
plus the canonical family of regular interior packets. -/
theorem flowA7_shiftedDown_port_partition {d : Nat} {α : Type}
    [LinearOrder α] (hd : 7 ≤ d) (t : Nat) (ht2 : 2 ≤ t)
    (ht : t < tf7 d) (b : KBag 64 d)
    (hdown : 0 < flowDown7 d hd b.l t)
    (hbad : HalfMisaligned (flowUp7 d hd b.l t))
    (j : Fin 64) (v : Fin (64 ^ d) → α)
    (hpack : PacketSortedOn (wireSets (flowSizes7 d hd) t b) v) :
    let S := wireSets (flowSizes7 d hd) t b
    let π := flowUp7 d hd b.l t
    let τ := flowDown7 d hd b.l t
    let m := τ / 64 - 1
    let lo := π / 2 + j.val * τ + 32
    let stageV := (flowA7_sourcePortRepairStage hd t ht2 ht).exec v
    let A : CanonicalPacketFamily (64 ^ d) :=
      ⟨m, fun k => rankPacketCell S lo k⟩
    let endpoint := downSetRepairPacket S π τ j m (Sum.inl ())
    CanonicalPacketPortContract A (Chvatal.blockOf S lo (lo + 64 * m)) stageV ∧
    RankSortedOn endpoint stageV ∧ endpoint.card = 64 ∧
    endpoint ⊆ Chvatal.downSet S π τ j.val ∧
    Finset.univ.biUnion A.packet ∪ endpoint = Chvatal.downSet S π τ j.val ∧
    Disjoint endpoint (Finset.univ.biUnion A.packet) := by
  let S := wireSets (flowSizes7 d hd) t b
  let π := flowUp7 d hd b.l t
  let τ := flowDown7 d hd b.l t
  let m := τ / 64 - 1
  let lo := π / 2 + j.val * τ + 32
  let stageV := (flowA7_sourcePortRepairStage hd t ht2 ht).exec v
  let A : CanonicalPacketFamily (64 ^ d) :=
    ⟨m, fun k => rankPacketCell S lo k⟩
  let endpoint := downSetRepairPacket S π τ j m (Sum.inl ())
  have hstreams := flowA7_shiftedDown_interiorStream_contract
    hd t ht2 ht b hdown hbad j v hpack
  have hendpoint := flowA7_shiftedDown_endpoint_contract
    hd t ht2 ht b hdown hbad j v hpack
  have hshape := node_shape_refined d hd t b.l ht2 ht
  have hres := refined_packet_residues hd ht2 ht hshape
  have hτdiv : 64 ∣ τ := by dsimp [τ]; exact hres.2.1
  have hτeq : τ = 64 * (m + 1) := by
    have hmod := Nat.mod_add_div τ 64
    have hrem : τ % 64 = 0 := Nat.mod_eq_zero_of_dvd hτdiv
    rw [hrem] at hmod
    dsimp [m]
    omega
  have hinterior : Finset.univ.biUnion A.packet =
      Finset.univ.biUnion (fun k : Fin m =>
        downSetInteriorCell S π τ j m k) := by
    rw [hstreams.2.1]
    simpa [A, lo, rankPacketCell, downSetInteriorCell] using
      blockOf_packetCell_partition S lo m
  have hrepair := downSetRepairPacket_union S π τ j m hτeq
  have hrepairSplit : Finset.univ.biUnion (downSetRepairPacket S π τ j m) =
      endpoint ∪ Finset.univ.biUnion (fun k : Fin m =>
        downSetInteriorCell S π τ j m k) := by
    ext w
    simp [downSetRepairPacket, endpoint]
    tauto
  have hcover : endpoint ∪ Finset.univ.biUnion A.packet =
      Chvatal.downSet S π τ j.val := by
    rw [hinterior, ← hrepairSplit]
    exact hrepair
  have hEA : Disjoint endpoint (Finset.univ.biUnion A.packet) := by
    apply Finset.disjoint_left.mpr
    intro w hwe hwa
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and] at hwa
    obtain ⟨k, hwa⟩ := hwa
    have hsel := hendpoint.2.2.2 k
    have hwa' : w ∈ downSetRepairPacket S π τ j m (Sum.inr k) := by
      simpa [A, downSetRepairPacket, downSetInteriorCell, rankPacketCell, lo] using hwa
    exact Finset.disjoint_left.mp hsel hwe hwa'
  refine ⟨?_, hendpoint.1, hendpoint.2.1, hendpoint.2.2.1, ?_, hEA⟩
  · simpa [A, S, π, τ, m, lo, stageV] using hstreams
  · rw [Finset.union_comm]
    exact hcover

/-- Extract the two ordinary rank-cell streams from an actual aligned
source up-port.  Unlike the shifted selector, this case has no endpoint
packet. -/
theorem flowA7_alignedUp_regularStreams_contract {d : Nat} {α : Type}
    [LinearOrder α] (hd : 7 ≤ d) (t : Nat) (ht2 : 2 ≤ t)
    (ht : t < tf7 d) (b : KBag 64 d)
    (hdown : 0 < flowDown7 d hd b.l t)
    (hnotbad : ¬ HalfMisaligned (flowUp7 d hd b.l t))
    (v : Fin (64 ^ d) → α)
    (hpack : PacketSortedOn (wireSets (flowSizes7 d hd) t b) v) :
    let S := wireSets (flowSizes7 d hd) t b
    let π := flowUp7 d hd b.l t
    let q := π / 2 / 64
    let stageV := (flowA7_sourcePortRepairStage hd t ht2 ht).exec v
    CanonicalPacketPortContract ⟨q, fun k => rankPacketCell S 0 k⟩
      (Chvatal.blockOf S 0 (64 * q)) stageV ∧
    CanonicalPacketPortContract ⟨q, fun k => rankPacketCell S (S.card - π / 2) k⟩
      (Chvatal.blockOf S (S.card - π / 2) S.card) stageV := by
  let S := wireSets (flowSizes7 d hd) t b
  let π := flowUp7 d hd b.l t
  let τ := flowDown7 d hd b.l t
  let q := π / 2 / 64
  let stageV := (flowA7_sourcePortRepairStage hd t ht2 ht).exec v
  have hshape := node_shape_refined d hd t b.l ht2 ht
  have hres := refined_packet_residues hd ht2 ht hshape
  have hnot : ¬ HalfMisaligned π := by simpa [π] using hnotbad
  have hhalfResidue : π / 2 % 64 = 0 := by
    rcases hres.2.2 with hzero | hthirtytwo
    · exact hzero
    · have hπpos : 0 < π := by omega
      exact (hnot ⟨hπpos, hthirtytwo⟩).elim
  have hhalf : π / 2 = 64 * q := by
    have hmod := Nat.mod_add_div (π / 2) 64
    rw [hhalfResidue] at hmod
    dsimp [q]
    omega
  have hbag : S.card = π + 64 * τ := by
    dsimp [S, π, τ]
    rw [wireSets_card (flowSizes7 d hd) (Nat.le_of_lt ht) b]
    exact (flowSizes7 d hd).hsplit b.l t b.hl ht
  have hprefixFinish : 64 * q ≤ S.card := by rw [← hhalf, hbag]; omega
  have hsuffixFinish : S.card - π / 2 + 64 * q ≤ S.card := by
    rw [hhalf]
    omega
  have hfam := flowA7_sourcePortRepairStage_alignedUpFamily
    hd t ht2 ht b hdown hnotbad v hpack
  have hprefix : ∀ k : Fin q, RankSortedOn (rankPacketCell S 0 k) stageV := by
    intro k
    have hk := hfam.1 (Sum.inl k)
    simpa [S, π, q, stageV, alignedUpRepairPacket] using hk
  have hsuffix : ∀ k : Fin q,
      RankSortedOn (rankPacketCell S (S.card - π / 2) k) stageV := by
    intro k
    have hk := hfam.1 (Sum.inr k)
    simpa [S, π, q, stageV, alignedUpRepairPacket] using hk
  constructor
  · simpa [S, π, q, stageV] using
      rankPacketCell_stream_contract S stageV 0 q hprefix (by
        simpa using hprefixFinish)
  · have hcontract := rankPacketCell_stream_contract S stageV
      (S.card - π / 2) q hsuffix hsuffixFinish
    have hend : S.card - π / 2 + 64 * q = S.card := by rw [hhalf]; omega
    simpa [S, π, q, stageV, hend] using hcontract

/-- The aligned child up-selector is exactly the union of its two regular
rank-interval stream families; this is the no-endpoint counterpart of the
shifted port partition. -/
theorem flowA7_alignedUp_port_partition {d : Nat} {α : Type}
    [LinearOrder α] (hd : 7 ≤ d) (t : Nat) (ht2 : 2 ≤ t)
    (ht : t < tf7 d) (b : KBag 64 d)
    (hdown : 0 < flowDown7 d hd b.l t)
    (hnotbad : ¬ HalfMisaligned (flowUp7 d hd b.l t))
    (v : Fin (64 ^ d) → α)
    (hpack : PacketSortedOn (wireSets (flowSizes7 d hd) t b) v) :
    let S := wireSets (flowSizes7 d hd) t b
    let π := flowUp7 d hd b.l t
    let q := π / 2 / 64
    let stageV := (flowA7_sourcePortRepairStage hd t ht2 ht).exec v
    let A : CanonicalPacketFamily (64 ^ d) := ⟨q, fun k => rankPacketCell S 0 k⟩
    let B : CanonicalPacketFamily (64 ^ d) :=
      ⟨q, fun k => rankPacketCell S (S.card - π / 2) k⟩
    CanonicalPacketPortContract A (Chvatal.blockOf S 0 (64 * q)) stageV ∧
    CanonicalPacketPortContract B (Chvatal.blockOf S (S.card - π / 2) S.card) stageV ∧
    Finset.univ.biUnion A.packet ∪ Finset.univ.biUnion B.packet =
      Chvatal.upSet S π ∧
    Disjoint (Finset.univ.biUnion A.packet) (Finset.univ.biUnion B.packet) := by
  let S := wireSets (flowSizes7 d hd) t b
  let π := flowUp7 d hd b.l t
  let q := π / 2 / 64
  let stageV := (flowA7_sourcePortRepairStage hd t ht2 ht).exec v
  let A : CanonicalPacketFamily (64 ^ d) := ⟨q, fun k => rankPacketCell S 0 k⟩
  let B : CanonicalPacketFamily (64 ^ d) :=
    ⟨q, fun k => rankPacketCell S (S.card - π / 2) k⟩
  have hstreams := flowA7_alignedUp_regularStreams_contract
    hd t ht2 ht b hdown hnotbad v hpack
  have hshape := node_shape_refined d hd t b.l ht2 ht
  have hres := refined_packet_residues hd ht2 ht hshape
  have hhalfResidue : π / 2 % 64 = 0 := by
    rcases hres.2.2 with hzero | hthirtytwo
    · exact hzero
    · have hπpos : 0 < π := by dsimp [π]; omega
      exact (hnotbad ⟨hπpos, hthirtytwo⟩).elim
  have hhalf : π / 2 = 64 * q := by
    have hmod := Nat.mod_add_div (π / 2) 64
    rw [hhalfResidue] at hmod
    dsimp [q]
    omega
  have hbag : S.card = π + 64 * flowDown7 d hd b.l t := by
    dsimp [S, π]
    rw [wireSets_card (flowSizes7 d hd) (Nat.le_of_lt ht) b]
    exact (flowSizes7 d hd).hsplit b.l t b.hl ht
  have hπcard : π ≤ S.card := by rw [hbag]; omega
  have hprefix : Finset.univ.biUnion A.packet =
      Finset.univ.biUnion (fun k : Fin q => rankPacketCell S 0 k) := by
    rw [hstreams.1.2.1]
  have hsufEnd : S.card - π / 2 + 64 * q = S.card := by rw [hhalf]; omega
  have hsuffix : Finset.univ.biUnion B.packet =
      Finset.univ.biUnion (fun k : Fin q => rankPacketCell S (S.card - π / 2) k) := by
    rw [hstreams.2.2.1]
  have hpacketSplit : Finset.univ.biUnion (alignedUpRepairPacket S π q) =
      Finset.univ.biUnion A.packet ∪ Finset.univ.biUnion B.packet := by
    ext w
    simp [alignedUpRepairPacket, A, B, Finset.mem_union]
  have hpacketUnion := alignedUpRepairPacket_union S π q hhalf hπcard
  have hAB : Disjoint (Finset.univ.biUnion A.packet)
      (Finset.univ.biUnion B.packet) := by
    apply Finset.disjoint_left.mpr
    intro w hwA hwB
    rw [hstreams.1.2.1] at hwA
    rw [hstreams.2.2.1] at hwB
    have ha := Chvatal.mem_blockOf.mp hwA
    have hb := Chvatal.mem_blockOf.mp hwB
    have hπeven : 2 ∣ π := by
      dsimp [π]
      exact (flowSizes7 d hd).hup_even b.l t ht
    have hπeq : π = 128 * q := by
      have htwice : π = 2 * (π / 2) := (Nat.mul_div_cancel' hπeven).symm
      rw [htwice, hhalf]
      omega
    have htotal : 128 * q ≤ S.card := by
      rw [hπeq] at hπcard
      omega
    have hgap : 64 * q ≤ S.card - π / 2 := by
      rw [hhalf]
      omega
    rcases ha with ⟨_, _, haHi⟩
    rcases hb with ⟨_, hbLo, _⟩
    have hrank : 64 * q ≤ Chvatal.rankIn S w := le_trans hgap hbLo
    change Chvatal.rankIn S w < 64 * q at haHi
    omega
  refine ⟨?_, ?_, ?_, hAB⟩
  · simpa [A, S, π, q, stageV] using hstreams.1
  · simpa [B, S, π, q, stageV] using hstreams.2
  · rw [← hpacketSplit]
    exact hpacketUnion

/-- At a zero-down child, the whole up-set is one ordinary aligned stream;
the second stream is empty. This gives the same two-slot interface as the
positive-flow selectors without inventing endpoint packets. -/
theorem flowA7_zeroDownUp_port_partition {d : Nat} {α : Type}
    [LinearOrder α] (hd : 7 ≤ d) (t : Nat) (ht2 : 2 ≤ t)
    (ht : t < tf7 d) (b : KBag 64 d)
    (hzero : flowDown7 d hd b.l t = 0)
    (v : Fin (64 ^ d) → α)
    (hpack : PacketSortedOn (wireSets (flowSizes7 d hd) t b) v) :
    let S := wireSets (flowSizes7 d hd) t b
    let π := flowUp7 d hd b.l t
    let C := (flowSizes7 d hd).a b.l t / 64
    let stageV := (flowA7_sourcePortRepairStage hd t ht2 ht).exec v
    let A : CanonicalPacketFamily (64 ^ d) :=
      ⟨C, fun k => rankPacketCell S 0 k⟩
    let B : CanonicalPacketFamily (64 ^ d) := ⟨0, Fin.elim0⟩
    CanonicalPacketPortContract A (Chvatal.upSet S π) stageV ∧
    CanonicalPacketPortContract B ∅ stageV ∧
    Finset.univ.biUnion A.packet ∪ Finset.univ.biUnion B.packet =
      Chvatal.upSet S π := by
  let S := wireSets (flowSizes7 d hd) t b
  let π := flowUp7 d hd b.l t
  let C := (flowSizes7 d hd).a b.l t / 64
  let stageV := (flowA7_sourcePortRepairStage hd t ht2 ht).exec v
  let A : CanonicalPacketFamily (64 ^ d) :=
    ⟨C, fun k => rankPacketCell S 0 k⟩
  let B : CanonicalPacketFamily (64 ^ d) := ⟨0, Fin.elim0⟩
  have hfamily := flowA7_sourcePortRepairStage_zeroDownUpFamily
    hd t ht2 ht b hzero v hpack
  have hA : CanonicalPacketPortContract A (Chvatal.upSet S π) stageV := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro k
      exact hfamily.1 k
    · simpa [A, S, π, C] using hfamily.2.1
    · intro k k' hne
      exact hfamily.2.2.1 k k' hne
    · intro k
      exact hfamily.2.2.2 k
  have hB : CanonicalPacketPortContract B ∅ stageV := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro k
      exact Fin.elim0 k
    · simp [B]
    · intro k k' hne
      exact Fin.elim0 k
    · intro k
      exact Fin.elim0 k
  refine ⟨hA, hB, ?_⟩
  simpa [B] using hA.2.1

/-- Bundle the two regular streams from every child port using the fact that
all children have the same scheduled selector mode. A shifted child contributes
one additional endpoint packet; aligned and zero-flow children contribute none.
This is the child half of the receiver-wide 129-stream extraction. -/
theorem flowA7_receiver_childPorts_streamPartition {d : Nat} {α : Type}
    [LinearOrder α] (hd : 7 ≤ d) (t : Nat) (ht2 : 2 ≤ t)
    (ht : t < tf7 d) (b : KBag 64 d) (hchildLevel : b.l < d)
    (v : Fin (64 ^ d) → α)
    (hpack : ∀ q : KBag 64 d,
      PacketSortedOn (wireSets (flowSizes7 d hd) t q) v) :
    ∃ A B : Fin 64 → CanonicalPacketFamily (64 ^ d),
    ∃ endpoint : Fin 64 → Finset (Fin (64 ^ d)),
      (∀ j, CanonicalPacketPortContract (A j)
        (Finset.univ.biUnion (A j).packet)
        ((flowA7_sourcePortRepairStage hd t ht2 ht).exec v)) ∧
      (∀ j, CanonicalPacketPortContract (B j)
        (Finset.univ.biUnion (B j).packet)
        ((flowA7_sourcePortRepairStage hd t ht2 ht).exec v)) ∧
      (∀ j, Finset.univ.biUnion (A j).packet ∪
        Finset.univ.biUnion (B j).packet ∪ endpoint j =
          Chvatal.upSet (wireSets (flowSizes7 d hd) t
            (b.child j.val j.isLt hchildLevel)) (flowUp7 d hd (b.l + 1) t)) ∧
      (∀ j, endpoint j = ∅ ∨
        (RankSortedOn (endpoint j)
          ((flowA7_sourcePortRepairStage hd t ht2 ht).exec v) ∧
         (endpoint j).card = 64)) ∧
      (∀ j, Disjoint (Finset.univ.biUnion (A j).packet)
          (Finset.univ.biUnion (B j).packet) ∧
        Disjoint (endpoint j) (Finset.univ.biUnion (A j).packet) ∧
        Disjoint (endpoint j) (Finset.univ.biUnion (B j).packet)) ∧
      (∀ j, ∃ lo, ∀ k : Fin (A j).count,
        (A j).packet k = rankPacketCell
          (wireSets (flowSizes7 d hd) t
            (b.child j.val j.isLt hchildLevel)) lo k) ∧
      (∀ j, ∃ lo, ∀ k : Fin (B j).count,
        (B j).packet k = rankPacketCell
          (wireSets (flowSizes7 d hd) t
            (b.child j.val j.isLt hchildLevel)) lo k) := by
  let stageV := (flowA7_sourcePortRepairStage hd t ht2 ht).exec v
  by_cases hzero : flowDown7 d hd (b.l + 1) t = 0
  · let C := (flowSizes7 d hd).a (b.l + 1) t / 64
    let A : Fin 64 → CanonicalPacketFamily (64 ^ d) := fun j =>
      ⟨C, fun k => rankPacketCell
        (wireSets (flowSizes7 d hd) t (b.child j.val j.isLt hchildLevel)) 0 k⟩
    let B : Fin 64 → CanonicalPacketFamily (64 ^ d) := fun _ => ⟨0, Fin.elim0⟩
    let endpoint : Fin 64 → Finset (Fin (64 ^ d)) := fun _ => ∅
    refine ⟨A, B, endpoint, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro j
      have hzj : flowDown7 d hd (b.child j.val j.isLt hchildLevel).l t = 0 := by
        simpa [KBag.child_l] using hzero
      have hp := flowA7_zeroDownUp_port_partition hd t ht2 ht
        (b.child j.val j.isLt hchildLevel) hzj v
        (hpack (b.child j.val j.isLt hchildLevel))
      have hA := hp.1
      refine ⟨hA.1, rfl, hA.2.2.1, hA.2.2.2⟩
    · intro j
      refine ⟨?_, rfl, ?_, ?_⟩
      · intro k
        exact Fin.elim0 k
      · intro i j hij
        exact Fin.elim0 i
      · intro k
        exact Fin.elim0 k
    · intro j
      have hzj : flowDown7 d hd (b.child j.val j.isLt hchildLevel).l t = 0 := by
        simpa [KBag.child_l] using hzero
      have hp := flowA7_zeroDownUp_port_partition hd t ht2 ht
        (b.child j.val j.isLt hchildLevel) hzj v
        (hpack (b.child j.val j.isLt hchildLevel))
      simpa [A, B, endpoint, stageV] using hp.2.2
    · intro j
      simp [endpoint]
    · intro j
      refine ⟨?_, ?_, ?_⟩
      · simp [B]
      · simp [endpoint]
      · simp [endpoint]
    · intro j
      exact ⟨0, fun k => rfl⟩
    · intro j
      exact ⟨0, fun k => Fin.elim0 k⟩
  · have hdown : 0 < flowDown7 d hd (b.l + 1) t := Nat.pos_of_ne_zero hzero
    by_cases hbad : HalfMisaligned (flowUp7 d hd (b.l + 1) t)
    · let q := (flowUp7 d hd (b.l + 1) t / 2) / 64
      let A : Fin 64 → CanonicalPacketFamily (64 ^ d) := fun j =>
        ⟨q, fun k => rankPacketCell
          (wireSets (flowSizes7 d hd) t (b.child j.val j.isLt hchildLevel)) 0 k⟩
      let B : Fin 64 → CanonicalPacketFamily (64 ^ d) := fun j =>
        ⟨q, fun k => rankPacketCell
          (wireSets (flowSizes7 d hd) t (b.child j.val j.isLt hchildLevel))
          ((wireSets (flowSizes7 d hd) t
            (b.child j.val j.isLt hchildLevel)).card -
              flowUp7 d hd (b.l + 1) t / 2 + 32) k⟩
      let endpoint : Fin 64 → Finset (Fin (64 ^ d)) := fun j =>
        upSetRepairPacket
          (wireSets (flowSizes7 d hd) t (b.child j.val j.isLt hchildLevel))
          (flowUp7 d hd (b.l + 1) t) q (Sum.inl ())
      refine ⟨A, B, endpoint, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro j
        have hdownj : 0 < flowDown7 d hd
            (b.child j.val j.isLt hchildLevel).l t := by
          simpa [KBag.child_l] using hdown
        have hp := flowA7_shiftedUp_port_partition hd t ht2 ht
          (b.child j.val j.isLt hchildLevel) hdownj
          (by simpa [KBag.child_l] using hbad) v
          (hpack (b.child j.val j.isLt hchildLevel))
        have hA := hp.1
        refine ⟨hA.1, rfl, hA.2.2.1, hA.2.2.2⟩
      · intro j
        have hdownj : 0 < flowDown7 d hd
            (b.child j.val j.isLt hchildLevel).l t := by
          simpa [KBag.child_l] using hdown
        have hp := flowA7_shiftedUp_port_partition hd t ht2 ht
          (b.child j.val j.isLt hchildLevel) hdownj
          (by simpa [KBag.child_l] using hbad) v
          (hpack (b.child j.val j.isLt hchildLevel))
        have hB := hp.2.1
        refine ⟨hB.1, rfl, hB.2.2.1, hB.2.2.2⟩
      · intro j
        have hdownj : 0 < flowDown7 d hd
            (b.child j.val j.isLt hchildLevel).l t := by
          simpa [KBag.child_l] using hdown
        have hp := flowA7_shiftedUp_port_partition hd t ht2 ht
          (b.child j.val j.isLt hchildLevel) hdownj
          (by simpa [KBag.child_l] using hbad) v
          (hpack (b.child j.val j.isLt hchildLevel))
        simpa [A, B, endpoint, stageV] using hp.2.2.2.2.2.1
      · intro j
        have hp := flowA7_shiftedUp_endpoint_contract hd t ht2 ht
          (b.child j.val j.isLt hchildLevel) (by
            simpa [KBag.child_l] using hdown)
          (by simpa [KBag.child_l] using hbad) v
          (hpack (b.child j.val j.isLt hchildLevel))
        exact Or.inr ⟨by simpa [endpoint, stageV] using hp.1,
          by simpa [endpoint] using hp.2.1⟩
      · intro j
        have hp := flowA7_shiftedUp_port_partition hd t ht2 ht
          (b.child j.val j.isLt hchildLevel) (by
            simpa [KBag.child_l] using hdown)
          (by simpa [KBag.child_l] using hbad) v
          (hpack (b.child j.val j.isLt hchildLevel))
        exact ⟨by simpa [A, B] using hp.2.2.2.2.2.2.1,
          by simpa [endpoint, A] using hp.2.2.2.2.2.2.2.1,
          by simpa [endpoint, B] using hp.2.2.2.2.2.2.2.2⟩
      · intro j
        exact ⟨0, fun k => rfl⟩
      · intro j
        exact ⟨((wireSets (flowSizes7 d hd) t
          (b.child j.val j.isLt hchildLevel)).card -
            flowUp7 d hd (b.l + 1) t / 2 + 32), fun k => rfl⟩
    · let q := (flowUp7 d hd (b.l + 1) t / 2) / 64
      let A : Fin 64 → CanonicalPacketFamily (64 ^ d) := fun j =>
        ⟨q, fun k => rankPacketCell
          (wireSets (flowSizes7 d hd) t (b.child j.val j.isLt hchildLevel)) 0 k⟩
      let B : Fin 64 → CanonicalPacketFamily (64 ^ d) := fun j =>
        ⟨q, fun k => rankPacketCell
          (wireSets (flowSizes7 d hd) t (b.child j.val j.isLt hchildLevel))
          ((wireSets (flowSizes7 d hd) t
            (b.child j.val j.isLt hchildLevel)).card -
              flowUp7 d hd (b.l + 1) t / 2) k⟩
      let endpoint : Fin 64 → Finset (Fin (64 ^ d)) := fun _ => ∅
      refine ⟨A, B, endpoint, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro j
        have hdownj : 0 < flowDown7 d hd
            (b.child j.val j.isLt hchildLevel).l t := by
          simpa [KBag.child_l] using hdown
        have hnotbad : ¬ HalfMisaligned
            (flowUp7 d hd (b.child j.val j.isLt hchildLevel).l t) := by
          simpa [KBag.child_l] using hbad
        have hp := flowA7_alignedUp_port_partition hd t ht2 ht
          (b.child j.val j.isLt hchildLevel) hdownj hnotbad v
          (hpack (b.child j.val j.isLt hchildLevel))
        have hA := hp.1
        refine ⟨hA.1, rfl, hA.2.2.1, hA.2.2.2⟩
      · intro j
        have hdownj : 0 < flowDown7 d hd
            (b.child j.val j.isLt hchildLevel).l t := by
          simpa [KBag.child_l] using hdown
        have hnotbad : ¬ HalfMisaligned
            (flowUp7 d hd (b.child j.val j.isLt hchildLevel).l t) := by
          simpa [KBag.child_l] using hbad
        have hp := flowA7_alignedUp_port_partition hd t ht2 ht
          (b.child j.val j.isLt hchildLevel) hdownj hnotbad v
          (hpack (b.child j.val j.isLt hchildLevel))
        have hB := hp.2.1
        refine ⟨hB.1, rfl, hB.2.2.1, hB.2.2.2⟩
      · intro j
        have hdownj : 0 < flowDown7 d hd
            (b.child j.val j.isLt hchildLevel).l t := by
          simpa [KBag.child_l] using hdown
        have hnotbad : ¬ HalfMisaligned
            (flowUp7 d hd (b.child j.val j.isLt hchildLevel).l t) := by
          simpa [KBag.child_l] using hbad
        have hp := flowA7_alignedUp_port_partition hd t ht2 ht
          (b.child j.val j.isLt hchildLevel) hdownj hnotbad v
          (hpack (b.child j.val j.isLt hchildLevel))
        simpa [A, B, endpoint, stageV] using hp.2.2.1
      · intro j
        simp [endpoint]
      · intro j
        have hp := flowA7_alignedUp_port_partition hd t ht2 ht
          (b.child j.val j.isLt hchildLevel) (by
            simpa [KBag.child_l] using hdown)
          (by simpa [KBag.child_l] using hbad) v
          (hpack (b.child j.val j.isLt hchildLevel))
        exact ⟨by simpa [A, B] using hp.2.2.2,
          by simp [endpoint], by simp [endpoint]⟩
      · intro j
        exact ⟨0, fun k => rfl⟩
      · intro j
        exact ⟨((wireSets (flowSizes7 d hd) t
          (b.child j.val j.isLt hchildLevel)).card -
            flowUp7 d hd (b.l + 1) t / 2), fun k => rfl⟩

/-- Extract one complete aligned rank-cell stream from each actual
source-port down-cut. -/
theorem flowA7_alignedDown_interiorStream_contract {d : Nat} {α : Type}
    [LinearOrder α] (hd : 7 ≤ d) (t : Nat) (ht2 : 2 ≤ t)
    (ht : t < tf7 d) (b : KBag 64 d)
    (hdown : 0 < flowDown7 d hd b.l t)
    (hnotbad : ¬ HalfMisaligned (flowUp7 d hd b.l t))
    (j : Fin 64) (v : Fin (64 ^ d) → α)
    (hpack : PacketSortedOn (wireSets (flowSizes7 d hd) t b) v) :
    let S := wireSets (flowSizes7 d hd) t b
    let π := flowUp7 d hd b.l t
    let τ := flowDown7 d hd b.l t
    let m := τ / 64
    let lo := π / 2 + j.val * τ
    let stageV := (flowA7_sourcePortRepairStage hd t ht2 ht).exec v
    CanonicalPacketPortContract ⟨m, fun k => rankPacketCell S lo k⟩
      (Chvatal.blockOf S lo (lo + 64 * m)) stageV := by
  let S := wireSets (flowSizes7 d hd) t b
  let π := flowUp7 d hd b.l t
  let τ := flowDown7 d hd b.l t
  let m := τ / 64
  let lo := π / 2 + j.val * τ
  let stageV := (flowA7_sourcePortRepairStage hd t ht2 ht).exec v
  have hshape := node_shape_refined d hd t b.l ht2 ht
  have hres := refined_packet_residues hd ht2 ht hshape
  have hτdiv : 64 ∣ τ := by dsimp [τ]; exact hres.2.1
  have hτeq : τ = 64 * m := by
    have hmod := Nat.mod_add_div τ 64
    have hrem : τ % 64 = 0 := Nat.mod_eq_zero_of_dvd hτdiv
    rw [hrem] at hmod
    dsimp [m]
    omega
  have hbag : S.card = π + 64 * τ := by
    dsimp [S, π, τ]
    rw [wireSets_card (flowSizes7 d hd) (Nat.le_of_lt ht) b]
    exact (flowSizes7 d hd).hsplit b.l t b.hl ht
  have hjle : j.val + 1 ≤ 64 := by omega
  have hmul : (j.val + 1) * τ ≤ 64 * τ := Nat.mul_le_mul_right τ hjle
  have hfinish : lo + 64 * m ≤ S.card := by
    calc
      lo + 64 * m = π / 2 + (j.val + 1) * τ := by
        dsimp [lo]
        rw [hτeq]
        ring
      _ ≤ π / 2 + 64 * τ := Nat.add_le_add_left hmul _
      _ ≤ π + 64 * τ := by omega
      _ = S.card := hbag.symm
  have hfam := flowA7_sourcePortRepairStage_alignedDownCutFamily
    hd t ht2 ht b hdown hnotbad v hpack
  have hcell : ∀ k : Fin m, RankSortedOn (rankPacketCell S lo k) stageV := by
    intro k
    have hk := (hfam j).1 k
    simpa [S, π, τ, m, lo, stageV, alignedDownRepairPacket] using hk
  exact rankPacketCell_stream_contract S stageV lo m hcell hfinish

/-- In the aligned case a parent down-port is one complete interval stream,
with no exceptional packet. -/
theorem flowA7_alignedDown_port_partition {d : Nat} {α : Type}
    [LinearOrder α] (hd : 7 ≤ d) (t : Nat) (ht2 : 2 ≤ t)
    (ht : t < tf7 d) (b : KBag 64 d)
    (hdown : 0 < flowDown7 d hd b.l t)
    (hnotbad : ¬ HalfMisaligned (flowUp7 d hd b.l t))
    (j : Fin 64) (v : Fin (64 ^ d) → α)
    (hpack : PacketSortedOn (wireSets (flowSizes7 d hd) t b) v) :
    let S := wireSets (flowSizes7 d hd) t b
    let π := flowUp7 d hd b.l t
    let τ := flowDown7 d hd b.l t
    let m := τ / 64
    let lo := π / 2 + j.val * τ
    let stageV := (flowA7_sourcePortRepairStage hd t ht2 ht).exec v
    let A : CanonicalPacketFamily (64 ^ d) :=
      ⟨m, fun k => rankPacketCell S lo k⟩
    CanonicalPacketPortContract A (Chvatal.downSet S π τ j.val) stageV := by
  let S := wireSets (flowSizes7 d hd) t b
  let π := flowUp7 d hd b.l t
  let τ := flowDown7 d hd b.l t
  let m := τ / 64
  let lo := π / 2 + j.val * τ
  let stageV := (flowA7_sourcePortRepairStage hd t ht2 ht).exec v
  let A : CanonicalPacketFamily (64 ^ d) :=
    ⟨m, fun k => rankPacketCell S lo k⟩
  have hstream := flowA7_alignedDown_interiorStream_contract
    hd t ht2 ht b hdown hnotbad j v hpack
  have hshape := node_shape_refined d hd t b.l ht2 ht
  have hres := refined_packet_residues hd ht2 ht hshape
  have hτdiv : 64 ∣ τ := by dsimp [τ]; exact hres.2.1
  have hτeq : τ = 64 * m := by
    have hmod := Nat.mod_add_div τ 64
    have hrem : τ % 64 = 0 := Nat.mod_eq_zero_of_dvd hτdiv
    rw [hrem] at hmod
    dsimp [m]
    omega
  have hsupport : Chvatal.blockOf S lo (lo + 64 * m) =
      Chvatal.downSet S π τ j.val := by
    rw [Chvatal.downSet]
    congr 1
    dsimp [lo]
    rw [hτeq]
    ring
  simpa [A, S, π, τ, m, lo, stageV, hsupport] using hstream

/-- A zero-down parent contributes an empty canonical stream, exactly
covering its empty selected down-cut. -/
theorem flowA7_zeroDown_port_partition {d : Nat} (hd : 7 ≤ d)
    (t : Nat) (ht : t < tf7 d) (b : KBag 64 d)
    (hzero : flowDown7 d hd b.l t = 0) (j : Fin 64)
    {α : Type} [LinearOrder α] (v : Fin (64 ^ d) → α) :
    let S := wireSets (flowSizes7 d hd) t b
    let π := flowUp7 d hd b.l t
    let τ := flowDown7 d hd b.l t
    let stageV := v
    let A : CanonicalPacketFamily (64 ^ d) := ⟨0, Fin.elim0⟩
    CanonicalPacketPortContract A (Chvatal.downSet S π τ j.val) stageV := by
  let S := wireSets (flowSizes7 d hd) t b
  let π := flowUp7 d hd b.l t
  let τ := flowDown7 d hd b.l t
  let A : CanonicalPacketFamily (64 ^ d) := ⟨0, Fin.elim0⟩
  have hempty := flowA7_zeroDownSet_empty hd t ht b hzero j
  have hportEmpty : Chvatal.downSet S π τ j.val = ∅ := hempty
  have hcontract : CanonicalPacketPortContract A ∅ v := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro k
      exact Fin.elim0 k
    · simp [A]
    · intro k k' hne
      exact Fin.elim0 k
    · intro k
      exact Fin.elim0 k
  simpa [A, S, π, τ, hportEmpty] using hcontract

/-- Expose the selected parent down-port as one regular stream and, only in
the shifted case, its exceptional endpoint packet. -/
theorem flowA7_receiver_parentPort_streamPartition {d : Nat} {α : Type}
    [LinearOrder α] (hd : 7 ≤ d) (t : Nat) (ht2 : 2 ≤ t)
    (ht : t < tf7 d) (b : KBag 64 d) (hb : 1 ≤ b.l)
    (v : Fin (64 ^ d) → α)
    (hpack : PacketSortedOn (wireSets (flowSizes7 d hd) t b.parent) v) :
    ∃ A : CanonicalPacketFamily (64 ^ d),
    ∃ endpoint : Finset (Fin (64 ^ d)),
      CanonicalPacketPortContract A (Finset.univ.biUnion A.packet)
        ((flowA7_sourcePortRepairStage hd t ht2 ht).exec v) ∧
      Finset.univ.biUnion A.packet ∪ endpoint =
        Chvatal.downSet (wireSets (flowSizes7 d hd) t b.parent)
          (flowUp7 d hd (b.l - 1) t) (flowDown7 d hd (b.l - 1) t)
          (b.x % 64) ∧
      (endpoint = ∅ ∨
        (RankSortedOn endpoint ((flowA7_sourcePortRepairStage hd t ht2 ht).exec v) ∧
          endpoint.card = 64)) ∧
      Disjoint endpoint (Finset.univ.biUnion A.packet) ∧
      ∃ lo, ∀ k : Fin A.count,
        A.packet k = rankPacketCell (wireSets (flowSizes7 d hd) t b.parent) lo k := by
  let q := b.parent
  let j : Fin 64 := ⟨b.x % 64, Nat.mod_lt _ (by norm_num)⟩
  let S := wireSets (flowSizes7 d hd) t q
  let π := flowUp7 d hd q.l t
  let τ := flowDown7 d hd q.l t
  let stageV := (flowA7_sourcePortRepairStage hd t ht2 ht).exec v
  by_cases hzero : flowDown7 d hd (b.l - 1) t = 0
  · have hzeroQ : flowDown7 d hd q.l t = 0 := by
      simpa [q, KBag.parent_l] using hzero
    let A : CanonicalPacketFamily (64 ^ d) := ⟨0, Fin.elim0⟩
    let endpoint : Finset (Fin (64 ^ d)) := ∅
    have hempty := flowA7_zeroDownSet_empty hd t ht q hzeroQ j
    have hcontract : CanonicalPacketPortContract A (Finset.univ.biUnion A.packet) stageV := by
      refine ⟨?_, rfl, ?_, ?_⟩
      · intro k
        exact Fin.elim0 k
      · intro i k hik
        exact Fin.elim0 i
      · intro k
        exact Fin.elim0 k
    refine ⟨A, endpoint, hcontract, ?_, Or.inl rfl, ?_, ⟨0, ?_⟩⟩
    · simpa [q, j, KBag.parent_l, endpoint] using hempty.symm
    · simp [endpoint]
    · intro k
      exact Fin.elim0 k
  · have hdown : 0 < flowDown7 d hd q.l t := by
      have hpos := Nat.pos_of_ne_zero hzero
      simpa [q, KBag.parent_l] using hpos
    by_cases hbad : HalfMisaligned (flowUp7 d hd (b.l - 1) t)
    · have hbadQ : HalfMisaligned (flowUp7 d hd q.l t) := by
        simpa [q, KBag.parent_l] using hbad
      let m := τ / 64 - 1
      let lo := π / 2 + j.val * τ + 32
      let A : CanonicalPacketFamily (64 ^ d) :=
        ⟨m, fun k => rankPacketCell S lo k⟩
      let endpoint := downSetRepairPacket S π τ j m (Sum.inl ())
      have hp := flowA7_shiftedDown_port_partition hd t ht2 ht q hdown hbadQ j v hpack
      have hcontract : CanonicalPacketPortContract A
          (Finset.univ.biUnion A.packet) stageV := by
        refine ⟨hp.1.1, rfl, hp.1.2.2.1, hp.1.2.2.2⟩
      refine ⟨A, endpoint, hcontract, ?_, ?_, ?_, ⟨lo, ?_⟩⟩
      · simpa [q, j, S, π, τ, m, lo, endpoint, KBag.parent_l] using
          hp.2.2.2.2.1
      · exact Or.inr ⟨by simpa [q, j, S, π, τ, m, endpoint, stageV,
          KBag.parent_l] using hp.2.1,
          by simpa [q, j, S, π, τ, m, endpoint, KBag.parent_l] using hp.2.2.1⟩
      · simpa [q, j, S, π, τ, m, lo, endpoint, KBag.parent_l] using
          hp.2.2.2.2.2
      · intro k
        rfl
    · have hnotbad : ¬ HalfMisaligned (flowUp7 d hd q.l t) := by
        simpa [q, KBag.parent_l] using hbad
      let m := τ / 64
      let lo := π / 2 + j.val * τ
      let A : CanonicalPacketFamily (64 ^ d) :=
        ⟨m, fun k => rankPacketCell S lo k⟩
      let endpoint : Finset (Fin (64 ^ d)) := ∅
      have hp := flowA7_alignedDown_port_partition hd t ht2 ht q hdown hnotbad j v hpack
      have hcontract : CanonicalPacketPortContract A
          (Finset.univ.biUnion A.packet) stageV := by
        refine ⟨hp.1, rfl, hp.2.2.1, hp.2.2.2⟩
      refine ⟨A, endpoint, hcontract, ?_, Or.inl rfl, ?_, ⟨lo, ?_⟩⟩
      · simpa [q, j, S, π, τ, m, lo, endpoint, KBag.parent_l] using hp.2.1
      · simp [endpoint]
      · intro k
        rfl

/-- Assemble the parent stream and the two regular streams of each child at
an interior receiver. The endpoint index has one parent slot and one slot per
child; empty slots encode aligned/zero-flow cases. This gives the concrete
129-stream index type and exact support partition needed for residue pooling. -/
theorem flowA7_receiver_regularStreams_bundle {d : Nat} {α : Type}
    [LinearOrder α] (hd : 7 ≤ d) (t : Nat) (ht2 : 2 ≤ t)
    (ht : t < tf7 d) (b : KBag 64 d) (hb : 1 ≤ b.l)
    (hchildLevel : b.l < d) (v : Fin (64 ^ d) → α)
    (hpack : ∀ q : KBag 64 d,
      PacketSortedOn (wireSets (flowSizes7 d hd) t q) v) :
    ∃ stream : (Unit ⊕ (Fin 64 × Bool)) → CanonicalPacketFamily (64 ^ d),
    ∃ endpoint : (Unit ⊕ Fin 64) → Finset (Fin (64 ^ d)),
      (∀ i, CanonicalPacketPortContract (stream i)
        (Finset.univ.biUnion (stream i).packet)
        ((flowA7_sourcePortRepairStage hd t ht2 ht).exec v)) ∧
      (∀ e, endpoint e = ∅ ∨
        (RankSortedOn (endpoint e)
          ((flowA7_sourcePortRepairStage hd t ht2 ht).exec v) ∧
         (endpoint e).card = 64)) ∧
      (∀ i i', i ≠ i' →
        Disjoint (Finset.univ.biUnion (stream i).packet)
          (Finset.univ.biUnion (stream i').packet)) ∧
      (∀ i e, Disjoint (Finset.univ.biUnion (stream i).packet) (endpoint e)) ∧
      (∀ e e', e ≠ e' → Disjoint (endpoint e) (endpoint e')) ∧
      Finset.univ.biUnion (fun i => Finset.univ.biUnion (stream i).packet) ∪
        Finset.univ.biUnion endpoint =
          wireSets (flowSizes7 d hd) (t + 1) b ∧
      (∃ lo, ∀ k : Fin ((stream (Sum.inl ())).count),
        (stream (Sum.inl ())).packet k =
          rankPacketCell (wireSets (flowSizes7 d hd) t b.parent) lo k) ∧
      (∀ j, ∃ lo, ∀ k : Fin ((stream (Sum.inr (j, false))).count),
        (stream (Sum.inr (j, false))).packet k =
          rankPacketCell (wireSets (flowSizes7 d hd) t
            (b.child j.val j.isLt hchildLevel)) lo k) ∧
      (∀ j, ∃ lo, ∀ k : Fin ((stream (Sum.inr (j, true))).count),
        (stream (Sum.inr (j, true))).packet k =
          rankPacketCell (wireSets (flowSizes7 d hd) t
            (b.child j.val j.isLt hchildLevel)) lo k) := by
  let stageV := (flowA7_sourcePortRepairStage hd t ht2 ht).exec v
  obtain ⟨parentStream, parentEndpoint, hpContract, hpCover, hpEndpoint,
      ⟨hpDisjoint, hpRankCells⟩⟩ :=
    flowA7_receiver_parentPort_streamPartition hd t ht2 ht b hb v (hpack b.parent)
  obtain ⟨childA, childB, childEndpoint, hcA, hcB, hcCover, hcEndpoint,
      ⟨hcDisjoint, hcARankCells, hcBRankCells⟩⟩ :=
    flowA7_receiver_childPorts_streamPartition hd t ht2 ht b hchildLevel v hpack
  let stream : (Unit ⊕ (Fin 64 × Bool)) → CanonicalPacketFamily (64 ^ d) :=
    fun i => match i with
      | Sum.inl _ => parentStream
      | Sum.inr (j, false) => childA j
      | Sum.inr (j, true) => childB j
  let endpoint : (Unit ⊕ Fin 64) → Finset (Fin (64 ^ d)) := fun e =>
    match e with
    | Sum.inl _ => parentEndpoint
    | Sum.inr j => childEndpoint j
  have hstreamContract : ∀ i, CanonicalPacketPortContract (stream i)
      (Finset.univ.biUnion (stream i).packet) stageV := by
    intro i
    cases i with
    | inl u => exact hpContract
    | inr p =>
      rcases p with ⟨j, side⟩
      cases side
      · exact hcA j
      · exact hcB j
  have hendpointContract : ∀ e, endpoint e = ∅ ∨
      (RankSortedOn (endpoint e) stageV ∧ (endpoint e).card = 64) := by
    intro e
    cases e with
    | inl u => exact hpEndpoint
    | inr j => exact hcEndpoint j
  have hreceiver :
      wireSets (flowSizes7 d hd) (t + 1) b =
        Chvatal.downSet (wireSets (flowSizes7 d hd) t b.parent)
          (flowUp7 d hd (b.l - 1) t) (flowDown7 d hd (b.l - 1) t) (b.x % 64) ∪
        Finset.univ.biUnion (fun j : Fin 64 =>
          Chvatal.upSet (wireSets (flowSizes7 d hd) t
            (b.child j.val j.isLt hchildLevel)) (flowUp7 d hd (b.l + 1) t)) := by
    rw [wireSets_succ_eq]
    simp [parentPart, childPart, hb, hchildLevel, KBag.parent_l,
      KBag.child_l, flowUp7, flowDown7, flowSizes7]
  let parentPort := Chvatal.downSet (wireSets (flowSizes7 d hd) t b.parent)
    (flowUp7 d hd (b.l - 1) t) (flowDown7 d hd (b.l - 1) t) (b.x % 64)
  let childPort (j : Fin 64) := Chvatal.upSet
    (wireSets (flowSizes7 d hd) t (b.child j.val j.isLt hchildLevel))
    (flowUp7 d hd (b.l + 1) t)
  have hparentChildBagNe (j : Fin 64) :
      b.parent ≠ b.child j.val j.isLt hchildLevel := by
    intro he
    have hl := congrArg KBag.l he
    simp only [KBag.parent_l, KBag.child_l] at hl
    omega
  have hchildBagNe (j j' : Fin 64) (hjj : j ≠ j') :
      b.child j.val j.isLt hchildLevel ≠ b.child j'.val j'.isLt hchildLevel := by
    intro he
    apply hjj
    have hx := congrArg KBag.x he
    apply Fin.ext
    simp [KBag.child] at hx
    omega
  have hparentChildDis (j : Fin 64) : Disjoint parentPort (childPort j) := by
    exact (wireSets_disjoint (flowSizes7 d hd) (Nat.le_of_lt ht)
      b.parent (b.child j.val j.isLt hchildLevel) (hparentChildBagNe j)).mono
      Chvatal.downSet_subset Chvatal.upSet_subset
  have hchildPortsDis (j j' : Fin 64) (hjj : j ≠ j') :
      Disjoint (childPort j) (childPort j') := by
    exact (wireSets_disjoint (flowSizes7 d hd) (Nat.le_of_lt ht)
      (b.child j.val j.isLt hchildLevel) (b.child j'.val j'.isLt hchildLevel)
      (hchildBagNe j j' hjj)).mono Chvatal.upSet_subset Chvatal.upSet_subset
  have hstreamSubset (i : Unit ⊕ (Fin 64 × Bool)) :
      Finset.univ.biUnion (stream i).packet ⊆
        (match i with
        | Sum.inl _ => parentPort
        | Sum.inr (j, _) => childPort j) := by
    cases i with
    | inl u =>
      intro w hw
      have hmem : w ∈ Finset.univ.biUnion parentStream.packet ∪ parentEndpoint :=
        Finset.mem_union.mpr (Or.inl (by simpa [stream] using hw))
      rw [hpCover] at hmem
      exact hmem
    | inr p =>
      rcases p with ⟨j, side⟩
      cases side
      · intro w hw
        have hmem : w ∈ Finset.univ.biUnion (childA j).packet ∪
            Finset.univ.biUnion (childB j).packet ∪ childEndpoint j :=
          Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr
            (Or.inl (by simpa [stream] using hw))))
        rw [hcCover j] at hmem
        exact hmem
      · intro w hw
        have hmem : w ∈ Finset.univ.biUnion (childA j).packet ∪
            Finset.univ.biUnion (childB j).packet ∪ childEndpoint j :=
          Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr
            (Or.inr (by simpa [stream] using hw))))
        rw [hcCover j] at hmem
        exact hmem
  have hendpointSubset (e : Unit ⊕ Fin 64) :
      endpoint e ⊆ (match e with
        | Sum.inl _ => parentPort
        | Sum.inr j => childPort j) := by
    cases e with
    | inl u =>
      intro w hw
      have hmem : w ∈ Finset.univ.biUnion parentStream.packet ∪ parentEndpoint :=
        Finset.mem_union.mpr (Or.inr (by simpa [endpoint] using hw))
      rw [hpCover] at hmem
      exact hmem
    | inr j =>
      intro w hw
      have hmem : w ∈ Finset.univ.biUnion (childA j).packet ∪
          Finset.univ.biUnion (childB j).packet ∪ childEndpoint j :=
        Finset.mem_union.mpr (Or.inr (by simpa [endpoint] using hw))
      rw [hcCover j] at hmem
      exact hmem
  have hstreamDisjoint : ∀ i i', i ≠ i' →
      Disjoint (Finset.univ.biUnion (stream i).packet)
        (Finset.univ.biUnion (stream i').packet) := by
    intro i i' hne
    cases i with
    | inl u =>
      cases i' with
      | inl u' => exact (hne (by cases u; cases u'; rfl)).elim
      | inr p =>
        exact (hparentChildDis p.1).mono (hstreamSubset (Sum.inl u))
          (hstreamSubset (Sum.inr p))
    | inr p =>
      cases i' with
      | inl u =>
        exact (hparentChildDis p.1).symm.mono (hstreamSubset (Sum.inr p))
          (hstreamSubset (Sum.inl u))
      | inr p' =>
        rcases p with ⟨j, side⟩
        rcases p' with ⟨j', side'⟩
        by_cases hjs : j = j'
        · subst j'
          cases side <;> cases side'
          · exact (hne (by rfl)).elim
          · exact (hcDisjoint j).1
          · exact (hcDisjoint j).1.symm
          · exact (hne (by rfl)).elim
        · exact (hchildPortsDis j j' hjs).mono
            (hstreamSubset (Sum.inr (j, side)))
            (hstreamSubset (Sum.inr (j', side')))
  have hstreamEndpointDisjoint : ∀ i e,
      Disjoint (Finset.univ.biUnion (stream i).packet) (endpoint e) := by
    intro i e
    cases i with
    | inl u =>
      cases e with
      | inl u' => exact hpDisjoint.symm
      | inr j =>
        exact (hparentChildDis j).mono
          (by simpa [stream] using hstreamSubset (Sum.inl u))
          (by simpa [endpoint] using hendpointSubset (Sum.inr j))
    | inr p =>
      rcases p with ⟨j, side⟩
      cases e with
      | inl u =>
        exact (hparentChildDis j).symm.mono
          (by simpa [stream] using hstreamSubset (Sum.inr (j, side)))
          (by simpa [endpoint] using hendpointSubset (Sum.inl u))
      | inr j' =>
        by_cases hjs : j = j'
        · subst j'
          cases side
          · exact (hcDisjoint j).2.1.symm
          · exact (hcDisjoint j).2.2.symm
        · exact (hchildPortsDis j j' hjs).mono
            (by simpa [stream] using hstreamSubset (Sum.inr (j, side)))
            (by simpa [endpoint] using hendpointSubset (Sum.inr j'))
  have hendpointPairwise : ∀ e e', e ≠ e' →
      Disjoint (endpoint e) (endpoint e') := by
    intro e e' hne
    cases e with
    | inl u =>
      cases e' with
      | inl u' => exact (hne (by cases u; cases u'; rfl)).elim
      | inr j =>
        exact (hparentChildDis j).mono
          (by simpa [endpoint] using hendpointSubset (Sum.inl u))
          (by simpa [endpoint] using hendpointSubset (Sum.inr j))
    | inr j =>
      cases e' with
      | inl u =>
        exact (hparentChildDis j).symm.mono
          (by simpa [endpoint] using hendpointSubset (Sum.inr j))
          (by simpa [endpoint] using hendpointSubset (Sum.inl u))
      | inr j' =>
        have hjj : j ≠ j' := by
          intro heq
          apply hne
          cases heq
          rfl
        exact (hchildPortsDis j j' hjj).mono
          (by simpa [endpoint] using hendpointSubset (Sum.inr j))
          (by simpa [endpoint] using hendpointSubset (Sum.inr j'))
  have hcover :
      Finset.univ.biUnion (fun i => Finset.univ.biUnion (stream i).packet) ∪
        Finset.univ.biUnion endpoint =
          wireSets (flowSizes7 d hd) (t + 1) b := by
    rw [hreceiver]
    ext w
    simp only [Finset.mem_union, Finset.mem_biUnion, Finset.mem_univ, true_and]
    constructor
    · rintro (⟨i, hi⟩ | ⟨e, he⟩)
      · cases i with
        | inl u =>
          have hi' : w ∈ Finset.univ.biUnion parentStream.packet := by
            simpa [Finset.mem_biUnion, stream] using hi
          have hmem : w ∈ Finset.univ.biUnion parentStream.packet ∪ parentEndpoint :=
            Finset.mem_union.mpr (Or.inl hi')
          rw [hpCover] at hmem
          exact Or.inl hmem
        | inr p =>
          rcases p with ⟨j, side⟩
          cases side
          · have hi' : w ∈ Finset.univ.biUnion (childA j).packet := by
              simpa [Finset.mem_biUnion, stream] using hi
            have hmem : w ∈ Finset.univ.biUnion (childA j).packet ∪
                Finset.univ.biUnion (childB j).packet ∪ childEndpoint j :=
              Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inl hi')))
            rw [hcCover j] at hmem
            exact Or.inr ⟨j, hmem⟩
          · have hi' : w ∈ Finset.univ.biUnion (childB j).packet := by
              simpa [Finset.mem_biUnion, stream] using hi
            have hmem : w ∈ Finset.univ.biUnion (childA j).packet ∪
                Finset.univ.biUnion (childB j).packet ∪ childEndpoint j :=
              Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inr hi')))
            rw [hcCover j] at hmem
            exact Or.inr ⟨j, hmem⟩
      · cases e with
        | inl u =>
          have he' : w ∈ parentEndpoint := by simpa [endpoint] using he
          have hmem : w ∈ Finset.univ.biUnion parentStream.packet ∪ parentEndpoint :=
            Finset.mem_union.mpr (Or.inr he')
          rw [hpCover] at hmem
          exact Or.inl hmem
        | inr j =>
          have he' : w ∈ childEndpoint j := by simpa [endpoint] using he
          have hmem : w ∈ Finset.univ.biUnion (childA j).packet ∪
              Finset.univ.biUnion (childB j).packet ∪ childEndpoint j :=
            Finset.mem_union.mpr (Or.inr he')
          rw [hcCover j] at hmem
          exact Or.inr ⟨j, hmem⟩
    · rintro (hparent | ⟨j, hchild⟩)
      · have hdecomp : w ∈ Finset.univ.biUnion parentStream.packet ∪ parentEndpoint := by
          exact hpCover.symm ▸ hparent
        rcases Finset.mem_union.mp hdecomp with hstream | he
        · exact Or.inl ⟨Sum.inl (), by
            simpa [Finset.mem_biUnion, stream] using hstream⟩
        · exact Or.inr ⟨Sum.inl (), he⟩
      · have hdecomp : w ∈ Finset.univ.biUnion (childA j).packet ∪
            Finset.univ.biUnion (childB j).packet ∪ childEndpoint j := by
          exact (hcCover j).symm ▸ hchild
        rcases Finset.mem_union.mp hdecomp with hstreams | he
        · rcases Finset.mem_union.mp hstreams with hA | hB
          · exact Or.inl ⟨Sum.inr (j, false), by
              simpa [Finset.mem_biUnion, stream] using hA⟩
          · exact Or.inl ⟨Sum.inr (j, true), by
              simpa [Finset.mem_biUnion, stream] using hB⟩
        · exact Or.inr ⟨Sum.inr j, he⟩
  exact ⟨stream, endpoint, hstreamContract, hendpointContract,
    hstreamDisjoint, hstreamEndpointDisjoint, hendpointPairwise, hcover,
    ⟨by simpa [stream] using hpRankCells,
      by simpa [stream] using hcARankCells,
      by simpa [stream] using hcBRankCells⟩⟩

/-- Extract every per-stream residue and filter the empty endpoint slots,
then invoke the generic exception-pool construction on the actual receiver
bundle. This gives at most 8,192 sorted, disjoint 64-wire packets. -/
theorem flowA7_receiver_exceptionPool {d : Nat} {α : Type}
    [LinearOrder α] (hd : 7 ≤ d) (t : Nat) (ht2 : 2 ≤ t)
    (ht : t < tf7 d) (b : KBag 64 d) (hb : 1 ≤ b.l)
    (hchildLevel : b.l < d) (v : Fin (64 ^ d) → α)
    (hpack : ∀ q : KBag 64 d,
      PacketSortedOn (wireSets (flowSizes7 d hd) t q) v) :
    ∃ P : CanonicalPacketFamily (64 ^ d),
      P.count ≤ 8192 ∧
      CanonicalPacketPortContract P (Finset.univ.biUnion P.packet)
        ((flowA7_sourcePortRepairStage hd t ht2 ht).exec v) := by
  classical
  let I := Unit ⊕ (Fin 64 × Bool)
  obtain ⟨stream, endpoint, hstream, hendpoint, hstreamDisjoint,
      hstreamEndpointDisjoint, hendpointDisjoint,
      ⟨hcover, _⟩⟩ :=
    flowA7_receiver_regularStreams_bundle hd t ht2 ht b hb hchildLevel v hpack
  let E := {e : Unit ⊕ Fin 64 // endpoint e ≠ ∅}
  let support : I → Finset (Fin (64 ^ d)) :=
    fun i => Finset.univ.biUnion (stream i).packet
  have hI : Fintype.card I ≤ 129 := by simp [I]
  have hresidueExists : ∀ i : I, ∃ q r, q * 64 + r = (stream i).count ∧
      r < 64 ∧ ∃ tail : CanonicalPacketFamily (64 ^ d),
        tail.count = r ∧
        CanonicalPacketPortContract tail (Finset.univ.biUnion tail.packet)
          ((flowA7_sourcePortRepairStage hd t ht2 ht).exec v) ∧
        (∀ j, ∃ k, tail.packet j ⊆ (stream i).packet k) := by
    intro i
    obtain ⟨q, r, hqr, hr, tail, hcount, hcontract, hsubset⟩ :=
      canonicalPacketFamily_residue_contract (stream i) (support i)
        ((flowA7_sourcePortRepairStage hd t ht2 ht).exec v) (hstream i)
    refine ⟨q, r, hqr, hr, tail, hcount, hcontract, ?_⟩
    intro j
    let j' : Fin r := Fin.cast hcount j
    have hklt : q * 64 + j'.val < (stream i).count := by
      rw [← hqr]
      have hj' := j'.isLt
      omega
    let k : Fin (stream i).count := ⟨q * 64 + j'.val, hklt⟩
    have hsub := hsubset hqr hcount j'
    exact ⟨k, by simpa [k, j'] using hsub⟩
  choose q r hqr hr residue hcount hresidue hsubset using hresidueExists
  have hresidueCount : ∀ i : I, (residue i).count < 64 := by
    intro i
    rw [hcount i]
    exact hr i
  have hresidueSubset : ∀ i j, ∃ k, (residue i).packet j ⊆ (stream i).packet k :=
    hsubset
  have hE : Fintype.card E ≤ 65 := by
    dsimp [E]
    calc
      Fintype.card {e : Unit ⊕ Fin 64 // endpoint e ≠ ∅} ≤
          Fintype.card (Unit ⊕ Fin 64) := Fintype.card_subtype_le _
      _ = 65 := by simp
  have hendpointSorted : ∀ e : E,
      RankSortedOn (endpoint e.1) ((flowA7_sourcePortRepairStage hd t ht2 ht).exec v) := by
    intro e
    rcases hendpoint e.1 with hempty | ⟨hsorted, hcard⟩
    · exact (e.2 hempty).elim
    · exact hsorted
  have hendpointCard : ∀ e : E, (endpoint e.1).card = 64 := by
    intro e
    rcases hendpoint e.1 with hempty | ⟨hsorted, hcard⟩
    · exact (e.2 hempty).elim
    · exact hcard
  have hendpointPairwise : ∀ e e' : E, e ≠ e' →
      Disjoint (endpoint e.1) (endpoint e'.1) := by
    intro e e' hne
    apply hendpointDisjoint e.1 e'.1
    intro heq
    apply hne
    exact Subtype.ext heq
  have hstreamEndpoint : ∀ i (e : E), Disjoint (support i) (endpoint e.1) :=
    fun i e => hstreamEndpointDisjoint i e.1
  obtain ⟨P, hPcount, hP⟩ := canonicalStreamResidues_exceptionPool
    ((flowA7_sourcePortRepairStage hd t ht2 ht).exec v)
    stream support hI hstream hstreamDisjoint residue hresidueCount hresidue
    hresidueSubset (fun e => endpoint e.1) hendpointSorted hE hendpointCard
    hendpointPairwise hstreamEndpoint
  have hPcanonical : CanonicalPacketPortContract P
      (Finset.univ.biUnion P.packet)
      ((flowA7_sourcePortRepairStage hd t ht2 ht).exec v) := by
    exact ⟨hP.1, rfl, hP.2.2.1, hP.2.2.2⟩
  exact ⟨P, hPcount, hPcanonical⟩

/-- The concrete receiver exception pool can itself be reduced to at most 128
sorted 4096-wire merge blocks plus fewer than 64 sorted packets. This turns
the arithmetic pool cap into an actual one-batch network contract. -/
theorem flowA7_receiver_exceptionPool_batch {d : Nat} {α : Type}
    [LinearOrder α] (hd : 7 ≤ d) (t : Nat) (ht2 : 2 ≤ t)
    (ht : t < tf7 d) (b : KBag 64 d) (hb : 1 ≤ b.l)
    (hchildLevel : b.l < d) (v : Fin (64 ^ d) → α)
    (hpack : ∀ q : KBag 64 d,
      PacketSortedOn (wireSets (flowSizes7 d hd) t q) v) :
    ∃ P : CanonicalPacketFamily (64 ^ d), P.count ≤ 8192 ∧
      CanonicalPacketPortContract P (Finset.univ.biUnion P.packet)
        ((flowA7_sourcePortRepairStage hd t ht2 ht).exec v) ∧
    ∃ q r, q * 64 + r = P.count ∧ q ≤ 128 ∧ r < 64 ∧
      ∃ tail : Fin r → Fin 64 ↪ Fin (64 ^ d),
      ∃ blocks : List (Fin 4096 ↪ Fin (64 ^ d)),
        blocks.Nodup ∧
        (∀ e ∈ blocks, ∀ f ∈ blocks, e ≠ f → ∀ x y, e x ≠ f y) ∧
        (genScatterMergeTreeBatch (packetPowerTree6 (α := α)) blocks).depth ≤ 57 ∧
        (∀ e ∈ blocks, Monotone (fun i =>
          (genScatterMergeTreeBatch (packetPowerTree6 (α := α)) blocks).exec
            ((flowA7_sourcePortRepairStage hd t ht2 ht).exec v) (e i))) ∧
        (∀ e ∈ blocks, ∀ j : Fin (packetPowerTree6 (α := α)).leafCount,
          Monotone (fun i =>
            (genScatterMergeTreeBatch (packetPowerTree6 (α := α)) blocks).exec
              ((flowA7_sourcePortRepairStage hd t ht2 ht).exec v)
              (genScatterMergeTreeOutputEmbedding
                (packetPowerTree6 (α := α)) e j i))) ∧
        (∀ j, Monotone (fun i =>
          ((flowA7_sourcePortRepairStage hd t ht2 ht).exec v) (tail j i))) ∧
        (∀ e ∈ blocks, ∀ i j k, e i ≠ tail j k) ∧
        (∀ j j', j ≠ j' → ∀ x y, tail j x ≠ tail j' y) ∧
        (∀ w, ((∃ e ∈ blocks, w ∈ Set.range e) ∨
            ∃ j, w ∈ Set.range (tail j)) ↔
          w ∈ Finset.univ.biUnion P.packet) := by
  obtain ⟨P, hPcount, hPcontract⟩ :=
    flowA7_receiver_exceptionPool hd t ht2 ht b hb hchildLevel v hpack
  obtain ⟨q, r, hqr, hr, tail, blocks, hnd, hdis, hdepth,
      hblockSorted, houtputSorted, htailSorted, _htailStrict, hblockTailDis,
      htailPairwise, ⟨hcover, _hprovenance⟩⟩ :=
    canonicalPacketFamily_fullBlocks_with_tail P
      (Finset.univ.biUnion P.packet)
      ((flowA7_sourcePortRepairStage hd t ht2 ht).exec v) hPcontract
  have hq : q ≤ 128 := by omega
  refine ⟨P, hPcount, hPcontract, q, r, hqr, hq, hr, tail, blocks, hnd, hdis, hdepth,
    hblockSorted, houtputSorted, htailSorted, hblockTailDis, htailPairwise, ?_⟩
  intro w
  simpa using hcover w

/-- The actual receiver stream bundle, endpoint partition, and independently
grouped regular blocks are available together as composable data. -/
def flowA7_receiver_streamSourceSupport {d : Nat} (hd : 7 ≤ d) (t : Nat)
    (b : KBag 64 d) (hchildLevel : b.l < d) :
    (Unit ⊕ (Fin 64 × Bool)) → Finset (Fin (64 ^ d)) := fun i =>
  match i with
  | Sum.inl _ => wireSets (flowSizes7 d hd) t b.parent
  | Sum.inr (j, _) =>
      wireSets (flowSizes7 d hd) t (b.child j.val j.isLt hchildLevel)

/-- Retain the actual receiver streams and all port-local rank intervals of
their generated 4096-wire blocks. The interval endpoints and completeness are
derived from the concrete selector witnesses and packet cardinalities. -/
theorem flowA7_receiver_regularFullBlocks_rankIntervals {d : Nat} {α : Type}
    [LinearOrder α] (hd : 7 ≤ d) (t : Nat) (ht2 : 2 ≤ t)
    (ht : t < tf7 d) (b : KBag 64 d) (hb : 1 ≤ b.l)
    (hchildLevel : b.l < d) (v : Fin (64 ^ d) → α)
    (hpack : ∀ q : KBag 64 d,
      PacketSortedOn (wireSets (flowSizes7 d hd) t q) v) :
    ∃ stream : (Unit ⊕ (Fin 64 × Bool)) → CanonicalPacketFamily (64 ^ d),
    ∃ endpoint : (Unit ⊕ Fin 64) → Finset (Fin (64 ^ d)),
    ∃ D : CanonicalStreamFullBlockData stream
      (fun i => Finset.univ.biUnion (stream i).packet)
      ((flowA7_sourcePortRepairStage hd t ht2 ht).exec v),
      (∀ i, CanonicalPacketPortContract (stream i)
        (Finset.univ.biUnion (stream i).packet)
        ((flowA7_sourcePortRepairStage hd t ht2 ht).exec v)) ∧
      (∀ i e, e ∈ D.blocks i →
        ∃ lo g : Nat, ∃ gi : Fin (D.fullGroups i), gi.val = g ∧
          Set.range e =
            (Chvatal.blockOf
              (flowA7_receiver_streamSourceSupport hd t b hchildLevel i)
              (lo + 4096 * g) (lo + 4096 * (g + 1)) : Set (Fin (64 ^ d)))) ∧
      (∀ i, ∃ lo,
        (∀ k : Fin (stream i).count,
          (stream i).packet k =
            rankPacketCell
              (flowA7_receiver_streamSourceSupport hd t b hchildLevel i) lo k) ∧
        (∀ g : Fin (D.fullGroups i), ∃ e,
          e ∈ D.blocks i ∧ Set.range e =
            (Chvatal.blockOf
              (flowA7_receiver_streamSourceSupport hd t b hchildLevel i)
              (lo + 4096 * g.val) (lo + 4096 * (g.val + 1)) : Set (Fin (64 ^ d))))) ∧
      Finset.univ.biUnion (fun i => Finset.univ.biUnion (stream i).packet) ∪
        Finset.univ.biUnion endpoint = wireSets (flowSizes7 d hd) (t + 1) b := by
  classical
  obtain ⟨stream, endpoint, hcontract, _, hdisjoint, _, _, hcover,
      ⟨hparentCells, ⟨hchildACells, hchildBCells⟩⟩⟩ :=
    flowA7_receiver_regularStreams_bundle hd t ht2 ht b hb hchildLevel v hpack
  let sourceSupport := flowA7_receiver_streamSourceSupport hd t b hchildLevel
  have hcell : ∀ i, ∃ lo, ∀ k : Fin (stream i).count,
      (stream i).packet k = rankPacketCell (sourceSupport i) lo k := by
    intro i
    cases i with
    | inl u =>
        cases u
        obtain ⟨lo, hlo⟩ := hparentCells
        exact ⟨lo, by simpa [sourceSupport,
          flowA7_receiver_streamSourceSupport] using hlo⟩
    | inr p =>
        rcases p with ⟨j, side⟩
        cases side with
        | false =>
            obtain ⟨lo, hlo⟩ := hchildACells j
            exact ⟨lo, by simpa [sourceSupport,
              flowA7_receiver_streamSourceSupport] using hlo⟩
        | true =>
            obtain ⟨lo, hlo⟩ := hchildBCells j
            exact ⟨lo, by simpa [sourceSupport,
              flowA7_receiver_streamSourceSupport] using hlo⟩
  let D := Classical.choice (canonicalStreamFamilies_fullBlocks_data stream
    (fun i => Finset.univ.biUnion (stream i).packet)
    ((flowA7_sourcePortRepairStage hd t ht2 ht).exec v) hcontract hdisjoint)
  have hintervals := D.rankIntervals_of_rankCellStreams hcontract sourceSupport hcell
  have hindexed : ∀ i, ∃ lo,
      (∀ k : Fin (stream i).count,
        (stream i).packet k = rankPacketCell (sourceSupport i) lo k) ∧
      (∀ g : Fin (D.fullGroups i), ∃ e,
        e ∈ D.blocks i ∧ Set.range e =
          (Chvatal.blockOf (sourceSupport i)
            (lo + 4096 * g.val) (lo + 4096 * (g.val + 1)) : Set (Fin (64 ^ d)))) := by
    intro i
    obtain ⟨lo, hlo⟩ := hcell i
    refine ⟨lo, hlo, ?_⟩
    intro g
    let prov := Classical.choice (D.provenance i)
    let e := prov.groupBlocks g
    have he : e ∈ D.blocks i := by
      rw [prov.blockList_eq]
      simp [e]
    have hgroup := D.groupBlock_rankInterval i (sourceSupport i) lo
      (hcontract i) hlo g
    exact ⟨e, he, by simpa [e, prov] using hgroup⟩
  exact ⟨stream, endpoint, D, hcontract, hintervals, hindexed, hcover⟩

theorem flowA7_receiver_regularFullBlocks {d : Nat} {α : Type}
    [LinearOrder α] (hd : 7 ≤ d) (t : Nat) (ht2 : 2 ≤ t)
    (ht : t < tf7 d) (b : KBag 64 d) (hb : 1 ≤ b.l)
    (hchildLevel : b.l < d) (v : Fin (64 ^ d) → α)
    (hpack : ∀ q : KBag 64 d,
      PacketSortedOn (wireSets (flowSizes7 d hd) t q) v) :
    ∃ stream : (Unit ⊕ (Fin 64 × Bool)) → CanonicalPacketFamily (64 ^ d),
    ∃ endpoint : (Unit ⊕ Fin 64) → Finset (Fin (64 ^ d)),
      (∀ i, CanonicalPacketPortContract (stream i)
        (Finset.univ.biUnion (stream i).packet)
        ((flowA7_sourcePortRepairStage hd t ht2 ht).exec v)) ∧
      (∀ e, endpoint e = ∅ ∨
        (RankSortedOn (endpoint e)
          ((flowA7_sourcePortRepairStage hd t ht2 ht).exec v) ∧
         (endpoint e).card = 64)) ∧
      (∀ i i', i ≠ i' →
        Disjoint (Finset.univ.biUnion (stream i).packet)
          (Finset.univ.biUnion (stream i').packet)) ∧
      (∀ i e, Disjoint (Finset.univ.biUnion (stream i).packet) (endpoint e)) ∧
      (∀ e e', e ≠ e' → Disjoint (endpoint e) (endpoint e')) ∧
      Finset.univ.biUnion (fun i => Finset.univ.biUnion (stream i).packet) ∪
        Finset.univ.biUnion endpoint = wireSets (flowSizes7 d hd) (t + 1) b ∧
      Nonempty (CanonicalStreamFullBlockData stream
        (fun i => Finset.univ.biUnion (stream i).packet)
        ((flowA7_sourcePortRepairStage hd t ht2 ht).exec v)) := by
  obtain ⟨stream, endpoint, hcontract, hendpoint, hdisjoint,
      hstreamEndpoint, hendpointPairwise,
      ⟨hcover, _⟩⟩ :=
    flowA7_receiver_regularStreams_bundle hd t ht2 ht b hb hchildLevel v hpack
  exact ⟨stream, endpoint, hcontract, hendpoint, hdisjoint,
    hstreamEndpoint, hendpointPairwise, hcover,
    canonicalStreamFamilies_fullBlocks_data stream
      (fun i => Finset.univ.biUnion (stream i).packet)
      ((flowA7_sourcePortRepairStage hd t ht2 ht).exec v)
      hcontract hdisjoint⟩

set_option maxRecDepth 10000 in
/-- Build the exception pool from the same concrete tails chosen by the
receiver's regular full-block decomposition, together with its nonempty
endpoint packets. -/
theorem flowA7_receiver_regularTailPool {d : Nat} {α : Type}
    [LinearOrder α] (hd : 7 ≤ d) (t : Nat) (ht2 : 2 ≤ t)
    (ht : t < tf7 d) (b : KBag 64 d) (hb : 1 ≤ b.l)
    (hchildLevel : b.l < d) (v : Fin (64 ^ d) → α)
    (hpack : ∀ q : KBag 64 d,
      PacketSortedOn (wireSets (flowSizes7 d hd) t q) v) :
    ∃ stream : (Unit ⊕ (Fin 64 × Bool)) → CanonicalPacketFamily (64 ^ d),
    ∃ endpoint : (Unit ⊕ Fin 64) → Finset (Fin (64 ^ d)),
    ∃ D : CanonicalStreamFullBlockData stream
        (fun i => Finset.univ.biUnion (stream i).packet)
        ((flowA7_sourcePortRepairStage hd t ht2 ht).exec v),
    ∃ Q : CanonicalPacketFamily (64 ^ d),
      Q.count ≤ 8192 ∧
      CanonicalPacketPortContract Q (Finset.univ.biUnion Q.packet)
        ((flowA7_sourcePortRepairStage hd t ht2 ht).exec v) ∧
      Finset.univ.biUnion Q.packet =
        Finset.univ.biUnion (canonicalStreamFullBlockExceptionPacket D
          (fun e : {e : Unit ⊕ Fin 64 // endpoint e ≠ ∅} => endpoint e.1)) ∧
      (∀ i i', i ≠ i' →
        Disjoint (Finset.univ.biUnion (stream i).packet)
          (Finset.univ.biUnion (stream i').packet)) ∧
      (∀ i e, Disjoint (Finset.univ.biUnion (stream i).packet) (endpoint e)) ∧
      (∀ e e', e ≠ e' → Disjoint (endpoint e) (endpoint e')) ∧
      Finset.univ.biUnion (fun i => Finset.univ.biUnion (stream i).packet) ∪
        Finset.univ.biUnion endpoint = wireSets (flowSizes7 d hd) (t + 1) b ∧
      (∀ w, w ∈ wireSets (flowSizes7 d hd) (t + 1) b ↔
        (∃ i, ∃ e ∈ D.blocks i, w ∈ Set.range e) ∨
          w ∈ Finset.univ.biUnion Q.packet) ∧
      Nonempty (CanonicalPacketFullBlockData Q
        (Finset.univ.biUnion Q.packet)
        ((flowA7_sourcePortRepairStage hd t ht2 ht).exec v)) := by
  classical
  let I := Unit ⊕ (Fin 64 × Bool)
  obtain ⟨stream, endpoint, hcontract, hendpoint, hdisjoint,
      hstreamEndpoint, hendpointPairwise, hcover, hD⟩ :=
    flowA7_receiver_regularFullBlocks hd t ht2 ht b hb hchildLevel v hpack
  let E := {e : Unit ⊕ Fin 64 // endpoint e ≠ ∅}
  obtain ⟨D⟩ := hD
  have hStreamCount : Fintype.card I ≤ 129 := by simp [I]
  have hEndpointCount : Fintype.card E ≤ 65 := by
    dsimp [E]
    calc
      Fintype.card {e : Unit ⊕ Fin 64 // endpoint e ≠ ∅} ≤
          Fintype.card (Unit ⊕ Fin 64) := Fintype.card_subtype_le _
      _ = 65 := by simp
  have hEndpointSorted : ∀ e : E,
      RankSortedOn (endpoint e.1)
        ((flowA7_sourcePortRepairStage hd t ht2 ht).exec v) := by
    intro e
    rcases hendpoint e.1 with hempty | ⟨hsorted, hcard⟩
    · exact (e.2 hempty).elim
    · exact hsorted
  have hEndpointCard : ∀ e : E, (endpoint e.1).card = 64 := by
    intro e
    rcases hendpoint e.1 with hempty | ⟨hsorted, hcard⟩
    · exact (e.2 hempty).elim
    · exact hcard
  have hEndpointDisjoint : ∀ e e' : E, e ≠ e' →
      Disjoint (endpoint e.1) (endpoint e'.1) := by
    intro e e' hne
    apply hendpointPairwise e.1 e'.1
    intro heq
    apply hne
    exact Subtype.ext heq
  have hStreamEndpoint : ∀ i (e : E),
      Disjoint (Finset.univ.biUnion (stream i).packet) (endpoint e.1) :=
    fun i e => hstreamEndpoint i e.1
  obtain ⟨Q, hQcount, hQcontract, hQsupport⟩ :=
    canonicalStreamFullBlock_exceptionPool D hStreamCount hdisjoint
      (fun e : E => endpoint e.1) hEndpointCount hEndpointSorted hEndpointCard
      hEndpointDisjoint hStreamEndpoint
  refine ⟨stream, endpoint, D, Q, hQcount, hQcontract, hQsupport,
    hdisjoint, hstreamEndpoint, hendpointPairwise, hcover, ?_,
    canonicalPacketFamily_fullBlocks_data Q
      (Finset.univ.biUnion Q.packet)
      ((flowA7_sourcePortRepairStage hd t ht2 ht).exec v) hQcontract⟩
  intro w
  rw [← hcover]
  constructor
  · intro hw
    rcases Finset.mem_union.mp hw with hs | he
    · obtain ⟨i, -, hi⟩ := Finset.mem_biUnion.mp hs
      rcases D.perStream i with
        ⟨_, _, _, _, _, _, _, _, _, _, _, hlocalCover⟩
      rcases (hlocalCover w).mpr hi with hblock | htail
      · left
        obtain ⟨e, he, hrange⟩ := hblock
        exact ⟨i, e, he, hrange⟩
      · right
        obtain ⟨j, hrange⟩ := htail
        rw [hQsupport]
        apply Finset.mem_biUnion.mpr
        refine ⟨Sum.inl ⟨i, j⟩, Finset.mem_univ _, ?_⟩
        exact (packetEmbeddingSupport_mem_iff (D.tail i j) w).2 hrange
    · obtain ⟨e, -, he⟩ := Finset.mem_biUnion.mp he
      have hne : endpoint e ≠ ∅ := by
        intro hzero
        rw [hzero] at he
        simp at he
      right
      rw [hQsupport]
      apply Finset.mem_biUnion.mpr
      exact ⟨Sum.inr ⟨e, hne⟩, Finset.mem_univ _, he⟩
  · rintro (hblock | hpool)
    · rcases hblock with ⟨i, e, he, hrange⟩
      apply Finset.mem_union.mpr
      left
      apply Finset.mem_biUnion.mpr
      exact ⟨i, Finset.mem_univ _, D.block_subset_support i e he hrange⟩
    · rw [hQsupport] at hpool
      obtain ⟨j, -, hj⟩ := Finset.mem_biUnion.mp hpool
      cases j with
      | inl ij =>
          rcases ij with ⟨i, k⟩
          apply Finset.mem_union.mpr
          left
          apply Finset.mem_biUnion.mpr
          exact ⟨i, Finset.mem_univ _, D.tail_subset_support i k hj⟩
      | inr e =>
          apply Finset.mem_union.mpr
          right
          apply Finset.mem_biUnion.mpr
          exact ⟨e.1, Finset.mem_univ _, hj⟩
/-- Compose the all-case `WireFlow` receiver partition with the embedding
adapter, so an actual corrected receiver register is ready to enter an
indexed logical matching round. -/
theorem flowA7_receiver_allCases_embeddingFamily {d : Nat} {α : Type}
    [LinearOrder α]
    (hd : 7 ≤ d) (t : Nat) (ht2 : 2 ≤ t) (ht : t < tf7 d)
    (b : KBag 64 d) (hb : 1 ≤ b.l) (hchild : b.l < d)
    (v : Fin (64 ^ d) → α)
    (hpack : ∀ q : KBag 64 d,
      PacketSortedOn (wireSets (flowSizes7 d hd) t q) v) :
    ∃ m : Nat, ∃ packets : Fin m → Fin 64 ↪ Fin (64 ^ d),
      (∀ i, Monotone (fun k =>
        ((flowA7_sourcePortRepairStage hd t ht2 ht).exec v) (packets i k))) ∧
      (∀ i i', i ≠ i' → ∀ x y, packets i x ≠ packets i' y) ∧
      Finset.univ.biUnion (fun i => packetEmbeddingSupport (packets i)) =
        wireSets (flowSizes7 d hd) (t + 1) b := by
  obtain ⟨receiver, hreceiver⟩ := flowA7_receiver_allCases_canonical
    hd t ht2 ht b hb hchild v hpack
  exact ⟨receiver.count,
    canonicalPacketEmbedding receiver hreceiver.2.2.2,
    canonicalPacketFamily_toEmbeddings receiver
      (wireSets (flowSizes7 d hd) (t + 1) b)
      ((flowA7_sourcePortRepairStage hd t ht2 ht).exec v) hreceiver⟩

/-- At any actual receiver, reindex the `k`th up-set packet from each of its
64 child senders into one 4096-wire cohort. The cohorts are pairwise disjoint
and their merge outputs are sorted after at most 57 additional layers. -/
theorem flowA7_receiver_childCohorts_merge {d : Nat} {α : Type}
    [LinearOrder α]
    (hd : 7 ≤ d) (t : Nat) (ht2 : 2 ≤ t) (ht : t < tf7 d)
    (b : KBag 64 d) (hb : 1 ≤ b.l) (hchildLevel : b.l < d)
    (v : Fin (64 ^ d) → α)
    (hpack : ∀ q : KBag 64 d,
      PacketSortedOn (wireSets (flowSizes7 d hd) t q) v) :
    ∃ childCount : Nat, ∃ child : Fin 64 → Fin childCount → Finset (Fin (64 ^ d)),
    ∃ blocks : List (Fin 4096 ↪ Fin (64 ^ d)),
      blocks.Nodup ∧
      (∀ e ∈ blocks, ∀ f ∈ blocks, e ≠ f → ∀ x y, e x ≠ f y) ∧
      (genScatterMergeTreeBatch (packetPowerTree6 (α := α)) blocks).depth ≤ 57 ∧
      (∀ e ∈ blocks, Monotone (fun i =>
        (genScatterMergeTreeBatch (packetPowerTree6 (α := α)) blocks).exec
          ((flowA7_sourcePortRepairStage hd t ht2 ht).exec v) (e i))) ∧
      (∀ e ∈ blocks, ∀ j : Fin (packetPowerTree6 (α := α)).leafCount,
        Monotone (fun i =>
          (genScatterMergeTreeBatch (packetPowerTree6 (α := α)) blocks).exec
            ((flowA7_sourcePortRepairStage hd t ht2 ht).exec v)
            (genScatterMergeTreeOutputEmbedding (packetPowerTree6 (α := α)) e j i))) ∧
      (∀ w, (∃ e ∈ blocks, w ∈ Set.range e) ↔ ∃ j k, w ∈ child j k) := by
  let stageV := (flowA7_sourcePortRepairStage hd t ht2 ht).exec v
  obtain ⟨parent, hparent⟩ := flowA7_receiver_parentPort_canonical
    hd t ht2 ht b v (hpack b.parent)
  obtain ⟨childCount, child, hchildren⟩ := flowA7_receiver_childPorts_canonical
    hd t ht2 ht b hchildLevel v hpack
  have hassembly := flowA7_receiver_packetAssembly hd t ht b hb hchildLevel
    parent.packet child stageV hparent.2.1 (fun j => (hchildren j).2.1)
    (fun i => hparent.1 i) (fun j k => (hchildren j).1 k)
    (fun i i' => hparent.2.2.1 i i')
    (fun j k k' => (hchildren j).2.2.1 k k')
    (fun i => hparent.2.2.2 i) (fun j k => (hchildren j).2.2.2 k)
  have hchildDisjoint : ∀ j k j' k', (j, k) ≠ (j', k') →
      Disjoint (child j k) (child j' k') := by
    intro j k j' k' hne
    have hne' : (Sum.inr (j, k) : Fin parent.count ⊕ (Fin 64 × Fin childCount)) ≠
        Sum.inr (j', k') := by
      intro h
      apply hne
      exact Sum.inr.inj h
    exact hassembly.2.2.1 (Sum.inr (j, k)) (Sum.inr (j', k')) hne'
  obtain ⟨blocks, hnodup, hblocksDis, hdepth, hblockSorted, hsortedOut, hcover⟩ :=
    receiverChildFamilies_transpose_merge child
    (fun j k => (hchildren j).2.2.2 k) stageV
    (fun j k => (hchildren j).1 k) hchildDisjoint
  exact ⟨childCount, child, blocks, hnodup, hblocksDis, hdepth, hblockSorted, hsortedOut, hcover⟩

/-- At an actual receiver, the child up-ports can be merged into sorted
4096-wire cohorts while the parent down-port remains as its canonical sorted
64-wire packets. These two pieces partition the complete receiver register.
This is the source-side decomposition needed to build a macro receiver; it
does not yet group the parent packets into 4096-wire blocks. -/
theorem flowA7_receiver_childCohorts_parentPartition {d : Nat} {α : Type}
    [LinearOrder α]
    (hd : 7 ≤ d) (t : Nat) (ht2 : 2 ≤ t) (ht : t < tf7 d)
    (b : KBag 64 d) (hb : 1 ≤ b.l) (hchildLevel : b.l < d)
    (v : Fin (64 ^ d) → α)
    (hpack : ∀ q : KBag 64 d,
      PacketSortedOn (wireSets (flowSizes7 d hd) t q) v) :
    ∃ parent : CanonicalPacketFamily (64 ^ d),
    ∃ childCount : Nat,
    ∃ child : Fin 64 → Fin childCount → Finset (Fin (64 ^ d)),
    ∃ blocks : List (Fin 4096 ↪ Fin (64 ^ d)),
      CanonicalPacketPortContract parent
        (Chvatal.downSet (wireSets (flowSizes7 d hd) t b.parent)
          (flowUp7 d hd (b.l - 1) t) (flowDown7 d hd (b.l - 1) t)
          (b.x % 64)) ((flowA7_sourcePortRepairStage hd t ht2 ht).exec v) ∧
      (∀ j, CanonicalPacketPortContract ⟨childCount, child j⟩
        (Chvatal.upSet (wireSets (flowSizes7 d hd) t
          (b.child j.val j.isLt hchildLevel)) (flowUp7 d hd (b.l + 1) t))
        ((flowA7_sourcePortRepairStage hd t ht2 ht).exec v)) ∧
      blocks.Nodup ∧
      (∀ e ∈ blocks, ∀ f ∈ blocks, e ≠ f → ∀ x y, e x ≠ f y) ∧
      (genScatterMergeTreeBatch (packetPowerTree6 (α := α)) blocks).depth ≤ 57 ∧
      (∀ e ∈ blocks, Monotone (fun i =>
        (genScatterMergeTreeBatch (packetPowerTree6 (α := α)) blocks).exec
          ((flowA7_sourcePortRepairStage hd t ht2 ht).exec v) (e i))) ∧
      (∀ e ∈ blocks, ∀ j : Fin (packetPowerTree6 (α := α)).leafCount,
        Monotone (fun i =>
          (genScatterMergeTreeBatch (packetPowerTree6 (α := α)) blocks).exec
            ((flowA7_sourcePortRepairStage hd t ht2 ht).exec v)
            (genScatterMergeTreeOutputEmbedding (packetPowerTree6 (α := α)) e j i))) ∧
      (∀ w, (∃ e ∈ blocks, w ∈ Set.range e) ↔ ∃ j k, w ∈ child j k) ∧
      (∀ w, w ∈ wireSets (flowSizes7 d hd) (t + 1) b ↔
        (∃ e ∈ blocks, w ∈ Set.range e) ∨ ∃ i, w ∈ parent.packet i) := by
  let stageV := (flowA7_sourcePortRepairStage hd t ht2 ht).exec v
  obtain ⟨parent, hparent⟩ := flowA7_receiver_parentPort_canonical
    hd t ht2 ht b v (hpack b.parent)
  obtain ⟨childCount, child, hchildren⟩ := flowA7_receiver_childPorts_canonical
    hd t ht2 ht b hchildLevel v hpack
  obtain ⟨blocks, hnodup, hblocksDis, hdepth, hblockSorted, hsortedOut, hcover⟩ :=
    receiverChildFamilies_transpose_merge child
      (fun j k => (hchildren j).2.2.2 k) stageV
      (fun j k => (hchildren j).1 k)
      (by
        intro j k j' k' hne
        have hne' : (Sum.inr (j, k) :
            Fin parent.count ⊕ (Fin 64 × Fin childCount)) ≠ Sum.inr (j', k') := by
          intro h
          apply hne
          exact Sum.inr.inj h
        have hassembly := flowA7_receiver_packetAssembly hd t ht b hb hchildLevel
          parent.packet child stageV hparent.2.1 (fun j => (hchildren j).2.1)
          (fun i => hparent.1 i) (fun j k => (hchildren j).1 k)
          (fun i i' => hparent.2.2.1 i i')
          (fun j k k' => (hchildren j).2.2.1 k k')
          (fun i => hparent.2.2.2 i) (fun j k => (hchildren j).2.2.2 k)
        exact hassembly.2.2.1 (Sum.inr (j, k)) (Sum.inr (j', k')) hne')
  have hassembly := flowA7_receiver_packetAssembly hd t ht b hb hchildLevel
    parent.packet child stageV hparent.2.1 (fun j => (hchildren j).2.1)
    (fun i => hparent.1 i) (fun j k => (hchildren j).1 k)
    (fun i i' => hparent.2.2.1 i i')
    (fun j k k' => (hchildren j).2.2.1 k k')
    (fun i => hparent.2.2.2 i) (fun j k => (hchildren j).2.2.2 k)
  refine ⟨parent, childCount, child, blocks, hparent, hchildren,
    hnodup, hblocksDis, hdepth, hblockSorted, hsortedOut, hcover, ?_⟩
  intro w
  have hcover' : (∃ e ∈ blocks, w ∈ Set.range e) ↔ ∃ j k, w ∈ child j k :=
    hcover w
  rw [← hassembly.2.1, receiverPacketFamily_union]
  simp only [Finset.mem_union, Finset.mem_biUnion, Finset.mem_univ, true_and]
  rw [hcover']
  exact or_comm

/-- Compose parent-port tail handling with the child transpose merge. Every
actual receiver is partitioned by support into 4096-wire child blocks,
4096-wire parent blocks, and fewer than 64 sorted parent packets. The two
block families are independently mergeable in 57 layers; this theorem makes
their combined source layout explicit for the next macro-routing step. -/
theorem flowA7_receiver_macroSource_partition {d : Nat} {α : Type}
    [LinearOrder α]
    (hd : 7 ≤ d) (t : Nat) (ht2 : 2 ≤ t) (ht : t < tf7 d)
    (b : KBag 64 d) (hb : 1 ≤ b.l) (hchildLevel : b.l < d)
    (v : Fin (64 ^ d) → α)
    (hpack : ∀ q : KBag 64 d,
      PacketSortedOn (wireSets (flowSizes7 d hd) t q) v) :
    ∃ childBlocks parentBlocks : List (Fin 4096 ↪ Fin (64 ^ d)),
    ∃ r : Nat, ∃ tail : Fin r → Fin 64 ↪ Fin (64 ^ d),
      r < 64 ∧
      childBlocks.Nodup ∧
      (∀ e ∈ childBlocks, ∀ f ∈ childBlocks, e ≠ f → ∀ x y, e x ≠ f y) ∧
      (genScatterMergeTreeBatch (packetPowerTree6 (α := α)) childBlocks).depth ≤ 57 ∧
      (∀ e ∈ childBlocks, Monotone (fun i =>
        (genScatterMergeTreeBatch (packetPowerTree6 (α := α)) childBlocks).exec
          ((flowA7_sourcePortRepairStage hd t ht2 ht).exec v) (e i))) ∧
      (∀ e ∈ childBlocks, ∀ j : Fin (packetPowerTree6 (α := α)).leafCount,
        Monotone (fun i =>
          (genScatterMergeTreeBatch (packetPowerTree6 (α := α)) childBlocks).exec
            ((flowA7_sourcePortRepairStage hd t ht2 ht).exec v)
            (genScatterMergeTreeOutputEmbedding (packetPowerTree6 (α := α)) e j i))) ∧
      (∀ e ∈ childBlocks, ∀ f ∈ parentBlocks, ∀ x y, e x ≠ f y) ∧
      parentBlocks.Nodup ∧
      (∀ e ∈ parentBlocks, ∀ f ∈ parentBlocks, e ≠ f → ∀ x y, e x ≠ f y) ∧
      (genScatterMergeTreeBatch (packetPowerTree6 (α := α)) parentBlocks).depth ≤ 57 ∧
      (∀ e ∈ parentBlocks, Monotone (fun i =>
        (genScatterMergeTreeBatch (packetPowerTree6 (α := α)) parentBlocks).exec
          ((flowA7_sourcePortRepairStage hd t ht2 ht).exec v) (e i))) ∧
      (∀ e ∈ parentBlocks, ∀ j : Fin (packetPowerTree6 (α := α)).leafCount,
        Monotone (fun i =>
          (genScatterMergeTreeBatch (packetPowerTree6 (α := α)) parentBlocks).exec
            ((flowA7_sourcePortRepairStage hd t ht2 ht).exec v)
            (genScatterMergeTreeOutputEmbedding (packetPowerTree6 (α := α)) e j i))) ∧
      (∀ j, Monotone (fun i =>
        ((flowA7_sourcePortRepairStage hd t ht2 ht).exec v) (tail j i))) ∧
      (∀ e ∈ childBlocks, ∀ j, ∀ x y, e x ≠ tail j y) ∧
      (∀ e ∈ parentBlocks, ∀ i j k, e i ≠ tail j k) ∧
      (∀ j j', j ≠ j' → ∀ x y, tail j x ≠ tail j' y) ∧
      (∀ w, w ∈ wireSets (flowSizes7 d hd) (t + 1) b ↔
        ((∃ e ∈ childBlocks, w ∈ Set.range e) ∨
         (∃ e ∈ parentBlocks, w ∈ Set.range e) ∨
         ∃ j, w ∈ Set.range (tail j))) := by
  let stageV := (flowA7_sourcePortRepairStage hd t ht2 ht).exec v
  obtain ⟨parent, childCount, child, childBlocks, hparent, hchildren,
      hchildNodup, hchildDis, hchildDepth, hchildBlockSorted, hchildSorted,
      hchildBlockCover, hchildCover⟩ :=
    flowA7_receiver_childCohorts_parentPartition hd t ht2 ht b hb hchildLevel v hpack
  let parentSupport := Chvatal.downSet (wireSets (flowSizes7 d hd) t b.parent)
      (flowUp7 d hd (b.l - 1) t) (flowDown7 d hd (b.l - 1) t) (b.x % 64)
  obtain ⟨q, r, hqr, hr, tail, parentBlocks, hparentNodup, hparentDis,
      hparentDepth, hparentBlockSorted, hparentSorted, htailSorted, _htailStrict,
      hparentTailDis, htailPairwise, ⟨hparentCover, _hparentProvenance⟩⟩ :=
    canonicalPacketFamily_fullBlocks_with_tail parent parentSupport stageV hparent
  let childPortSupport (j : Fin 64) := Chvatal.upSet
      (wireSets (flowSizes7 d hd) t (b.child j.val j.isLt hchildLevel))
      (flowUp7 d hd (b.l + 1) t)
  have hparentChildDis : ∀ j, Disjoint parentSupport (childPortSupport j) := by
    intro j
    have hbag : b.parent ≠ b.child j.val j.isLt hchildLevel := by
      intro heq
      have hl := congrArg KBag.l heq
      rw [KBag.parent_l, KBag.child_l] at hl
      omega
    exact (wireSets_disjoint (flowSizes7 d hd) (Nat.le_of_lt ht) b.parent
      (b.child j.val j.isLt hchildLevel) hbag).mono
      Chvatal.downSet_subset Chvatal.upSet_subset
  have hcross : ∀ e ∈ childBlocks, ∀ f ∈ parentBlocks, ∀ x y, e x ≠ f y := by
    intro e he f hf x y heq
    obtain ⟨j, k, hx⟩ := (hchildBlockCover (e x)).mp ⟨e, he, x, rfl⟩
    have hxPort : e x ∈ childPortSupport j := by
      change e x ∈ Chvatal.upSet
        (wireSets (flowSizes7 d hd) t (b.child j.val j.isLt hchildLevel))
        (flowUp7 d hd (b.l + 1) t)
      have hUnion := (hchildren j).2.1
      rw [← hUnion]
      simp only [Finset.mem_biUnion, Finset.mem_univ, true_and]
      exact ⟨k, hx⟩
    have hyParent : f y ∈ parentSupport :=
      (hparentCover (f y)).mp (Or.inl ⟨f, hf, ⟨y, rfl⟩⟩)
    have hParentAt : e x ∈ parentSupport := by simpa [heq] using hyParent
    exact (Finset.disjoint_left.mp (hparentChildDis j)) hParentAt hxPort
  have hchildTail : ∀ e ∈ childBlocks, ∀ j, ∀ x y, e x ≠ tail j y := by
    intro e he j x y heq
    obtain ⟨k, k', hx⟩ := (hchildBlockCover (e x)).mp ⟨e, he, x, rfl⟩
    have hxPort : e x ∈ childPortSupport k := by
      change e x ∈ Chvatal.upSet
        (wireSets (flowSizes7 d hd) t (b.child k.val k.isLt hchildLevel))
        (flowUp7 d hd (b.l + 1) t)
      rw [← (hchildren k).2.1]
      simp only [Finset.mem_biUnion, Finset.mem_univ, true_and]
      exact ⟨k', hx⟩
    have hyParent : tail j y ∈ parentSupport :=
      (hparentCover (tail j y)).mp (Or.inr ⟨j, y, rfl⟩)
    have hParentAt : e x ∈ parentSupport := by simpa [heq] using hyParent
    exact (Finset.disjoint_left.mp (hparentChildDis k)) hParentAt hxPort
  refine ⟨childBlocks, parentBlocks, r, tail, hr,
    hchildNodup, hchildDis, hchildDepth, hchildBlockSorted, hchildSorted, hcross,
    hparentNodup, hparentDis, hparentDepth, hparentBlockSorted, hparentSorted, htailSorted,
    hchildTail, hparentTailDis, htailPairwise, ?_⟩
  intro w
  have hparentPacketSupport : (∃ i, w ∈ parent.packet i) ↔ w ∈ parentSupport := by
    change (∃ i, w ∈ parent.packet i) ↔
      w ∈ Chvatal.downSet (wireSets (flowSizes7 d hd) t b.parent)
        (flowUp7 d hd (b.l - 1) t) (flowDown7 d hd (b.l - 1) t) (b.x % 64)
    rw [← hparent.2.1]
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and]
  constructor
  · intro hw
    rcases (hchildCover w).mp hw with hchild | hparentPackets
    · exact Or.inl hchild
    · rcases (hparentCover w).mpr (hparentPacketSupport.mp hparentPackets) with
        hparentBlock | htail
      · exact Or.inr (Or.inl hparentBlock)
      · exact Or.inr (Or.inr htail)
  · intro hw
    rcases hw with hchild | hparentMacro
    · exact (hchildCover w).mpr (Or.inl hchild)
    · rcases hparentMacro with hparentBlock | htail
      · exact (hchildCover w).mpr
          (Or.inr (hparentPacketSupport.mpr ((hparentCover w).mp (Or.inl hparentBlock))))
      · exact (hchildCover w).mpr
          (Or.inr (hparentPacketSupport.mpr ((hparentCover w).mp (Or.inr htail))))

/-- The child cohorts and parent blocks of one receiver can be merged by one
common 57-layer batch: their supports are pairwise disjoint, so combining the
two batch lists preserves each block's local execution. The short parent tail
passes through unchanged. -/
theorem flowA7_receiver_macroSource_commonBatch {d : Nat} {α : Type}
    [LinearOrder α]
    (hd : 7 ≤ d) (t : Nat) (ht2 : 2 ≤ t) (ht : t < tf7 d)
    (b : KBag 64 d) (hb : 1 ≤ b.l) (hchildLevel : b.l < d)
    (v : Fin (64 ^ d) → α)
    (hpack : ∀ q : KBag 64 d,
      PacketSortedOn (wireSets (flowSizes7 d hd) t q) v) :
    ∃ blocks : List (Fin 4096 ↪ Fin (64 ^ d)), ∃ r : Nat,
    ∃ tail : Fin r → Fin 64 ↪ Fin (64 ^ d),
      r < 64 ∧
      blocks.Nodup ∧
      (∀ e ∈ blocks, ∀ f ∈ blocks, e ≠ f → ∀ x y, e x ≠ f y) ∧
      (∀ e ∈ blocks, ∀ j, ∀ x y, e x ≠ tail j y) ∧
      (∀ j j', j ≠ j' → ∀ x y, tail j x ≠ tail j' y) ∧
      (genScatterMergeTreeBatch (packetPowerTree6 (α := α)) blocks).depth ≤ 57 ∧
      (∀ e ∈ blocks, Monotone (fun i =>
        (genScatterMergeTreeBatch (packetPowerTree6 (α := α)) blocks).exec
          ((flowA7_sourcePortRepairStage hd t ht2 ht).exec v) (e i))) ∧
      (∀ e ∈ blocks, ∀ j : Fin (packetPowerTree6 (α := α)).leafCount,
        Monotone (fun i =>
          (genScatterMergeTreeBatch (packetPowerTree6 (α := α)) blocks).exec
            ((flowA7_sourcePortRepairStage hd t ht2 ht).exec v)
            (genScatterMergeTreeOutputEmbedding (packetPowerTree6 (α := α)) e j i))) ∧
      (∀ j, Monotone (fun i =>
        ((flowA7_sourcePortRepairStage hd t ht2 ht).exec v) (tail j i))) ∧
      (∀ w, w ∈ wireSets (flowSizes7 d hd) (t + 1) b ↔
        (∃ e ∈ blocks, w ∈ Set.range e) ∨ ∃ j, w ∈ Set.range (tail j)) := by
  let stageV := (flowA7_sourcePortRepairStage hd t ht2 ht).exec v
  obtain ⟨childBlocks, parentBlocks, r, tail, hr,
      hchildNodup, hchildDis, hchildDepth, hchildBlockSorted, hchildSorted, hcross,
      hparentNodup, hparentDis, hparentDepth, hparentBlockSorted, hparentSorted, htailSorted,
      hchildTailDis, hparentTailDis, htailPairwise, hcover⟩ :=
    flowA7_receiver_macroSource_partition hd t ht2 ht b hb hchildLevel v hpack
  let blocks := childBlocks ++ parentBlocks
  have hlistSeparation : ∀ e ∈ childBlocks, e ∉ parentBlocks := by
    intro e he hen
    have hself := hcross e he e hen (0 : Fin 4096) 0
    exact hself rfl
  have hblocksNodup : blocks.Nodup := by
    exact List.Nodup.append hchildNodup hparentNodup hlistSeparation
  have hblocksDis : ∀ e ∈ blocks, ∀ f ∈ blocks, e ≠ f → ∀ x y, e x ≠ f y := by
    intro e he f hf hne x y
    rcases List.mem_append.mp he with heChild | heParent
    · rcases List.mem_append.mp hf with hfChild | hfParent
      · exact hchildDis e heChild f hfChild hne x y
      · exact hcross e heChild f hfParent x y
    · rcases List.mem_append.mp hf with hfChild | hfParent
      · exact (hcross f hfChild e heParent y x).symm
      · exact hparentDis e heParent f hfParent hne x y
  have hblockTailDis : ∀ e ∈ blocks, ∀ j, ∀ x y, e x ≠ tail j y := by
    intro e he j x y
    rcases List.mem_append.mp he with heChild | heParent
    · exact hchildTailDis e heChild j x y
    · exact hparentTailDis e heParent x j y
  have hlocalChild (e : Fin 4096 ↪ Fin (64 ^ d)) (he : e ∈ childBlocks)
      (k : Fin 4096) :
      (genScatterMergeTreeBatch (packetPowerTree6 (α := α)) blocks).exec
          stageV (e k) =
        (genScatterMergeTreeBatch (packetPowerTree6 (α := α)) childBlocks).exec
          stageV (e k) := by
    change (genScatterBatch (packetPowerTree6 (α := α)).network blocks).exec
        stageV (e k) =
      (genScatterBatch (packetPowerTree6 (α := α)).network childBlocks).exec
        stageV (e k)
    rw [genScatterBatch_exec_inside (packetPowerTree6 (α := α)).network
          blocks hblocksNodup hblocksDis stageV e
          (List.mem_append.mpr (Or.inl he)) k,
        genScatterBatch_exec_inside (packetPowerTree6 (α := α)).network
          childBlocks hchildNodup hchildDis stageV e he k]
  have hlocalParent (e : Fin 4096 ↪ Fin (64 ^ d)) (he : e ∈ parentBlocks)
      (k : Fin 4096) :
      (genScatterMergeTreeBatch (packetPowerTree6 (α := α)) blocks).exec
          stageV (e k) =
        (genScatterMergeTreeBatch (packetPowerTree6 (α := α)) parentBlocks).exec
          stageV (e k) := by
    change (genScatterBatch (packetPowerTree6 (α := α)).network blocks).exec
        stageV (e k) =
      (genScatterBatch (packetPowerTree6 (α := α)).network parentBlocks).exec
        stageV (e k)
    rw [genScatterBatch_exec_inside (packetPowerTree6 (α := α)).network
          blocks hblocksNodup hblocksDis stageV e
          (List.mem_append.mpr (Or.inr he)) k,
        genScatterBatch_exec_inside (packetPowerTree6 (α := α)).network
          parentBlocks hparentNodup hparentDis stageV e he k]
  have hsorted : ∀ e ∈ blocks,
      ∀ j : Fin (packetPowerTree6 (α := α)).leafCount,
        Monotone (fun i =>
          (genScatterMergeTreeBatch (packetPowerTree6 (α := α)) blocks).exec
            stageV (genScatterMergeTreeOutputEmbedding
              (packetPowerTree6 (α := α)) e j i)) := by
    intro e he j
    rcases List.mem_append.mp he with heChild | heParent
    · intro i k hik
      change (genScatterMergeTreeBatch (packetPowerTree6 (α := α)) blocks).exec
          stageV (e (PacketMergeTree.chunkIndex (packetPowerTree6 (α := α)) j i)) ≤
        (genScatterMergeTreeBatch (packetPowerTree6 (α := α)) blocks).exec
          stageV (e (PacketMergeTree.chunkIndex (packetPowerTree6 (α := α)) j k))
      rw [hlocalChild e heChild _, hlocalChild e heChild _]
      exact hchildSorted e heChild j hik
    · intro i k hik
      change (genScatterMergeTreeBatch (packetPowerTree6 (α := α)) blocks).exec
          stageV (e (PacketMergeTree.chunkIndex (packetPowerTree6 (α := α)) j i)) ≤
        (genScatterMergeTreeBatch (packetPowerTree6 (α := α)) blocks).exec
          stageV (e (PacketMergeTree.chunkIndex (packetPowerTree6 (α := α)) j k))
      rw [hlocalParent e heParent _, hlocalParent e heParent _]
      exact hparentSorted e heParent j hik
  have hblockSorted : ∀ e ∈ blocks, Monotone (fun i =>
      (genScatterMergeTreeBatch (packetPowerTree6 (α := α)) blocks).exec
        stageV (e i)) := by
    intro e he
    rcases List.mem_append.mp he with heChild | heParent
    · intro i k hik
      change (genScatterMergeTreeBatch (packetPowerTree6 (α := α)) blocks).exec
          stageV (e i) ≤
        (genScatterMergeTreeBatch (packetPowerTree6 (α := α)) blocks).exec
          stageV (e k)
      rw [hlocalChild e heChild i, hlocalChild e heChild k]
      exact hchildBlockSorted e heChild hik
    · intro i k hik
      change (genScatterMergeTreeBatch (packetPowerTree6 (α := α)) blocks).exec
          stageV (e i) ≤
        (genScatterMergeTreeBatch (packetPowerTree6 (α := α)) blocks).exec
          stageV (e k)
      rw [hlocalParent e heParent i, hlocalParent e heParent k]
      exact hparentBlockSorted e heParent hik
  have hdepth :
      (genScatterMergeTreeBatch (packetPowerTree6 (α := α)) blocks).depth ≤ 57 :=
    genScatterMergeTreeBatch_depth_le (packetPowerTree6 (α := α)) blocks
      hblocksNodup hblocksDis 57 packetPowerTree6_depth_le
  refine ⟨blocks, r, tail, hr, hblocksNodup, hblocksDis, hblockTailDis,
    htailPairwise, hdepth, hblockSorted, hsorted, htailSorted, ?_⟩
  intro w
  constructor
  · intro hw
    rcases (hcover w).mp hw with hchild | hparent | htail
    · rcases hchild with ⟨e, he, hwe⟩
      exact Or.inl ⟨e, List.mem_append.mpr (Or.inl he), hwe⟩
    · rcases hparent with ⟨e, he, hwe⟩
      exact Or.inl ⟨e, List.mem_append.mpr (Or.inr he), hwe⟩
    · exact Or.inr htail
  · intro hw
    rcases hw with hblock | htail
    · rcases hblock with ⟨e, he, hwe⟩
      rcases List.mem_append.mp he with hchild | hparent
      · exact (hcover w).mpr (Or.inl ⟨e, hchild, hwe⟩)
      · exact (hcover w).mpr (Or.inr (Or.inl ⟨e, hparent, hwe⟩))
    · exact (hcover w).mpr (Or.inr (Or.inr htail))

/- Each 4096-wire block's sorted output chunks, together with the untouched
residue packets, still form an exact pairwise-disjoint packet partition of
the receiver's next-stage support. This turns the local batch result into a
state that can be fed to a subsequent macro-routing step. -/
theorem flowA7_receiver_macroSource_outputPartition {d : Nat} {α : Type}
    [LinearOrder α]
    (hd : 7 ≤ d) (t : Nat) (ht2 : 2 ≤ t) (ht : t < tf7 d)
    (b : KBag 64 d) (hb : 1 ≤ b.l) (hchildLevel : b.l < d)
    (v : Fin (64 ^ d) → α)
    (hpack : ∀ q : KBag 64 d,
      PacketSortedOn (wireSets (flowSizes7 d hd) t q) v) :
    ∃ blocks : List (Fin 4096 ↪ Fin (64 ^ d)), ∃ r : Nat,
    ∃ tail : Fin r → Fin 64 ↪ Fin (64 ^ d),
      r < 64 ∧
      blocks.Nodup ∧
      (∀ e ∈ blocks, ∀ f ∈ blocks, e ≠ f → ∀ x y, e x ≠ f y) ∧
      (∀ e ∈ blocks, ∀ j, ∀ f ∈ blocks, e ≠ f → ∀ j' x y,
        genScatterMergeTreeOutputEmbedding (packetPowerTree6 (α := α)) e j x ≠
          genScatterMergeTreeOutputEmbedding (packetPowerTree6 (α := α)) f j' y) ∧
      (∀ e ∈ blocks, ∀ j j', j ≠ j' → ∀ x y,
        genScatterMergeTreeOutputEmbedding (packetPowerTree6 (α := α)) e j x ≠
          genScatterMergeTreeOutputEmbedding (packetPowerTree6 (α := α)) e j' y) ∧
      (∀ e ∈ blocks, ∀ j : Fin (packetPowerTree6 (α := α)).leafCount,
        ∀ k : Fin r, ∀ x y,
        genScatterMergeTreeOutputEmbedding (packetPowerTree6 (α := α)) e j x ≠ tail k y) ∧
      (∀ j j', j ≠ j' → ∀ x y, tail j x ≠ tail j' y) ∧
      (∀ e ∈ blocks, ∀ j : Fin (packetPowerTree6 (α := α)).leafCount,
        Monotone (fun i =>
          (genScatterMergeTreeBatch (packetPowerTree6 (α := α)) blocks).exec
            ((flowA7_sourcePortRepairStage hd t ht2 ht).exec v)
            (genScatterMergeTreeOutputEmbedding (packetPowerTree6 (α := α)) e j i))) ∧
      (∀ j, Monotone (fun i =>
        ((flowA7_sourcePortRepairStage hd t ht2 ht).exec v) (tail j i))) ∧
      (∀ w, w ∈ wireSets (flowSizes7 d hd) (t + 1) b ↔
        ((∃ e ∈ blocks, ∃ j,
          w ∈ Set.range (genScatterMergeTreeOutputEmbedding
            (packetPowerTree6 (α := α)) e j)) ∨
         (∃ j, w ∈ Set.range (tail j)))) ∧
      (genScatterMergeTreeBatch (packetPowerTree6 (α := α)) blocks).depth ≤ 57 ∧
      (∀ e ∈ blocks, Monotone (fun i =>
        (genScatterMergeTreeBatch (packetPowerTree6 (α := α)) blocks).exec
          ((flowA7_sourcePortRepairStage hd t ht2 ht).exec v) (e i))) := by
  obtain ⟨blocks, r, tail, hr, hblocksNodup, hblocksDis,
      hblockTailDis, htailPairwise, hdepth, hblockSorted, hsorted, htailSorted, hcover⟩ :=
    flowA7_receiver_macroSource_commonBatch hd t ht2 ht b hb hchildLevel v hpack
  let tree := packetPowerTree6 (α := α)
  refine ⟨blocks, r, tail, hr, hblocksNodup, hblocksDis, ?_, ?_, ?_,
    htailPairwise, hsorted, htailSorted, ?_, hdepth, hblockSorted⟩
  · intro e he j f hf hef j' x y heq
    apply hblocksDis e he f hf hef
      (PacketMergeTree.chunkIndex tree j x)
      (PacketMergeTree.chunkIndex tree j' y)
    exact heq
  · intro e he j j' hj x y heq
    have hsame := genScatterMergeTreeOutputEmbedding_disjoint tree e hj x y
    exact hsame heq
  · intro e he j k x y heq
    exact hblockTailDis e he k (PacketMergeTree.chunkIndex tree j x) y heq
  · intro w
    constructor
    · intro hw
      rcases (hcover w).mp hw with hblock | htail
      · obtain ⟨e, he, hwe⟩ := hblock
        have hchunks : ∃ j, w ∈ Set.range
            (genScatterMergeTreeOutputEmbedding tree e j) :=
          (genScatterMergeTreeOutputEmbedding_support_iff tree e w).2 hwe
        exact Or.inl ⟨e, he, hchunks⟩
      · exact Or.inr htail
    · intro hw
      rcases hw with hblocks | htail
      · obtain ⟨e, he, j, hwe⟩ := hblocks
        have hblock : w ∈ Set.range e :=
          (genScatterMergeTreeOutputEmbedding_support_iff tree e w).1 ⟨j, hwe⟩
        exact (hcover w).mpr (Or.inl ⟨e, he, hblock⟩)
      · exact (hcover w).mpr (Or.inr htail)

/- The one-receiver macro partition above requires a genuine parent port. At
the root there is no parent: its next-stage support comes only from the 64
child up-ports. This assembles that frontier as a canonical sorted packet
family, so it can be grouped by the same full-block/tail machinery. -/
theorem flowA7_root_receiver_packetAssembly {d : Nat} {α : Type}
    [LinearOrder α]
    (hd : 7 ≤ d) (t : Nat) (ht2 : 2 ≤ t) (ht : t < tf7 d)
    (v : Fin (64 ^ d) → α)
    (hpack : ∀ q : KBag 64 d,
      PacketSortedOn (wireSets (flowSizes7 d hd) t q) v) :
    ∃ P : CanonicalPacketFamily (64 ^ d),
      CanonicalPacketPortContract P
        (wireSets (flowSizes7 d hd) (t + 1) (KBag.root 64 d))
        ((flowA7_sourcePortRepairStage hd t ht2 ht).exec v) := by
  let b := KBag.root 64 d
  let stageV := (flowA7_sourcePortRepairStage hd t ht2 ht).exec v
  have hbchild : b.l < d := by simp [b, KBag.root]; omega
  obtain ⟨childCount, child, hchildren⟩ :=
    flowA7_receiver_childPorts_canonical hd t ht2 ht b hbchild v hpack
  let childSupport (j : Fin 64) :=
    Chvatal.upSet (wireSets (flowSizes7 d hd) t
      (b.child j.val j.isLt hbchild)) (flowUp7 d hd (b.l + 1) t)
  let parent : Fin 0 → Finset (Fin (64 ^ d)) := Fin.elim0
  let family := receiverPacketFamily parent child
  have hchildUnion : ∀ j, Finset.univ.biUnion (child j) = childSupport j := by
    intro j
    exact (hchildren j).2.1
  have hparentUnion : Finset.univ.biUnion parent = ∅ := by
    ext w
    simp [parent]
  have hparentSorted : ∀ i, RankSortedOn (parent i) stageV := by
    intro i
    exact Fin.elim0 i
  have hparentDisjoint : ∀ i i', i ≠ i' → Disjoint (parent i) (parent i') := by
    intro i
    exact Fin.elim0 i
  have hchildPortsDisjoint : ∀ j j', j ≠ j' → Disjoint (childSupport j) (childSupport j') := by
    intro j j' hjj'
    have hbags : b.child j.val j.isLt hbchild ≠ b.child j'.val j'.isLt hbchild := by
      intro heq
      apply hjj'
      have hx := congrArg KBag.x heq
      apply Fin.ext
      simpa [KBag.child] using hx
    exact (wireSets_disjoint (flowSizes7 d hd) (Nat.le_of_lt ht)
      (b.child j.val j.isLt hbchild) (b.child j'.val j'.isLt hbchild) hbags).mono
      Chvatal.upSet_subset Chvatal.upSet_subset
  have hfamilySorted := receiverPacketFamily_sorted parent child stageV
    hparentSorted (fun j k => (hchildren j).1 k)
  have hfamilyDisjoint := receiverPacketFamily_pairwise_disjoint
    parent child (∅ : Finset (Fin (64 ^ d))) childSupport
    hparentUnion hchildUnion hparentDisjoint
    (fun j k k' hne => (hchildren j).2.2.1 k k' hne)
    (by intro i j k; exact Fin.elim0 i)
    hchildPortsDisjoint
  have hfamilyCard := receiverPacketFamily_card_eq_64 parent child
    (by intro i; exact Fin.elim0 i)
    (fun j k => (hchildren j).2.2.2 k)
  have hfamilyUnion : Finset.univ.biUnion family =
      wireSets (flowSizes7 d hd) (t + 1) b := by
    have hdpos : 0 < d := by omega
    rw [receiverPacketFamily_union, hparentUnion]
    simp_rw [hchildUnion]
    rw [wireSets_succ_eq]
    simp [parentPart, childPart, b, childSupport, KBag.root, flowSizes7, hdpos]
  refine ⟨canonicalPacketFamily family, ?_⟩
  exact canonicalPacketFamily_contract family
    (wireSets (flowSizes7 d hd) (t + 1) b) stageV
    ⟨hfamilySorted, hfamilyUnion, hfamilyDisjoint, hfamilyCard⟩

/- The root packet family can now pass through the same full-block merger as
an interior receiver. This keeps fewer than 64 packets as a sorted residue and
sorts every full 4096-wire block in one 57-layer batch. -/
theorem flowA7_root_receiver_fullBlocksBatch {d : Nat} {α : Type}
    [LinearOrder α]
    (hd : 7 ≤ d) (t : Nat) (ht2 : 2 ≤ t) (ht : t < tf7 d)
    (v : Fin (64 ^ d) → α)
    (hpack : ∀ q : KBag 64 d,
      PacketSortedOn (wireSets (flowSizes7 d hd) t q) v) :
    ∃ r : Nat, ∃ tail : Fin r → Fin 64 ↪ Fin (64 ^ d),
    ∃ blocks : List (Fin 4096 ↪ Fin (64 ^ d)),
      r < 64 ∧ blocks.Nodup ∧
      (∀ e ∈ blocks, ∀ f ∈ blocks, e ≠ f → ∀ x y, e x ≠ f y) ∧
      (genScatterMergeTreeBatch (packetPowerTree6 (α := α)) blocks).depth ≤ 57 ∧
      (∀ e ∈ blocks, Monotone (fun i =>
        (genScatterMergeTreeBatch (packetPowerTree6 (α := α)) blocks).exec
          ((flowA7_sourcePortRepairStage hd t ht2 ht).exec v) (e i))) ∧
      (∀ e ∈ blocks, ∀ j : Fin (packetPowerTree6 (α := α)).leafCount,
        Monotone (fun i =>
          (genScatterMergeTreeBatch (packetPowerTree6 (α := α)) blocks).exec
            ((flowA7_sourcePortRepairStage hd t ht2 ht).exec v)
            (genScatterMergeTreeOutputEmbedding (packetPowerTree6 (α := α)) e j i))) ∧
      (∀ j, Monotone (fun i =>
        ((flowA7_sourcePortRepairStage hd t ht2 ht).exec v) (tail j i))) ∧
      (∀ e ∈ blocks, ∀ i j k, e i ≠ tail j k) ∧
      (∀ j j', j ≠ j' → ∀ x y, tail j x ≠ tail j' y) ∧
      (∀ w, ((∃ e ∈ blocks, w ∈ Set.range e) ∨
          ∃ j, w ∈ Set.range (tail j)) ↔
        w ∈ wireSets (flowSizes7 d hd) (t + 1) (KBag.root 64 d)) := by
  obtain ⟨P, hP⟩ := flowA7_root_receiver_packetAssembly hd t ht2 ht v hpack
  obtain ⟨q, r, hqr, hr, tail, blocks, hnd, hdis, hdepth, hblockSorted,
      houtputSorted, htailSorted, _htailStrict, hblockTailDis, htailPairwise,
      ⟨hcover, _hprovenance⟩⟩ :=
    canonicalPacketFamily_fullBlocks_with_tail P
      (wireSets (flowSizes7 d hd) (t + 1) (KBag.root 64 d))
      ((flowA7_sourcePortRepairStage hd t ht2 ht).exec v) hP
  exact ⟨r, tail, blocks, hr, hnd, hdis, hdepth, hblockSorted, houtputSorted,
    htailSorted, hblockTailDis, htailPairwise, hcover⟩

/- No top-level bag has flow at any ordinary or terminal time t ≥ 2: the
active flow window always ends below level d. Consequently its WireFlow
register is empty, so the root plus interior receiver cases cover every wire
at the next stage. -/
theorem flowA7_topReceiver_wireSet_empty {d : Nat}
    (hd : 7 ≤ d) (u : Nat) (hu2 : 2 ≤ u) (hu : u ≤ tf7 d)
    (b : KBag 64 d) (hb : b.l = d) :
    wireSets (flowSizes7 d hd) u b = ∅ := by
  have hflow : flowA7 d hd d u = 0 := by
    have hω := omega7_lt_d d u hd hu
    unfold flowA7
    rw [if_neg (by omega : u ≠ 0), if_neg (by omega : u ≠ 1)]
    rw [allocation_inactive d d u (by
      unfold Active
      omega)]
    simp
  have hcard : (wireSets (flowSizes7 d hd) u b).card = 0 := by
    rw [wireSets_card (flowSizes7 d hd) hu b]
    simpa [flowSizes7, hb] using hflow
  exact Finset.card_eq_zero.mp hcard

/-- Pack the local root/interior/empty-top proofs into one receiver record.
This is the per-index input needed to instantiate the finite batching lemma. -/
structure FlowA7ReceiverMacroData {d : Nat} {α : Type} [LinearOrder α]
    (hd : 7 ≤ d) (t : Nat) (ht2 : 2 ≤ t) (ht : t < tf7 d)
    (v : Fin (64 ^ d) → α) (b : KBag 64 d) where
  tailCount : Nat
  tail : Fin tailCount → Fin 64 ↪ Fin (64 ^ d)
  blocks : List (Fin 4096 ↪ Fin (64 ^ d))
  tailCount_lt : tailCount < 64
  blocks_nodup : blocks.Nodup
  blocks_disjoint : ∀ e ∈ blocks, ∀ f ∈ blocks, e ≠ f → ∀ x y, e x ≠ f y
  block_tail_disjoint : ∀ e ∈ blocks, ∀ k x y, e x ≠ tail k y
  tail_pairwise : ∀ k k', k ≠ k' → ∀ x y, tail k x ≠ tail k' y
  output_blockSorted : ∀ e ∈ blocks, Monotone (fun i =>
    (genScatterMergeTreeBatch (packetPowerTree6 (α := α)) blocks).exec
      ((flowA7_sourcePortRepairStage hd t ht2 ht).exec v) (e i))
  output_sorted : ∀ e ∈ blocks, ∀ j : Fin (packetPowerTree6 (α := α)).leafCount,
    Monotone (fun i =>
      (genScatterMergeTreeBatch (packetPowerTree6 (α := α)) blocks).exec
        ((flowA7_sourcePortRepairStage hd t ht2 ht).exec v)
        (genScatterMergeTreeOutputEmbedding (packetPowerTree6 (α := α)) e j i))
  tail_sorted : ∀ k, Monotone (fun i =>
    ((flowA7_sourcePortRepairStage hd t ht2 ht).exec v)
      (tail k i))
  support_cover : ∀ w,
    w ∈ wireSets (flowSizes7 d hd) (t + 1) b ↔
      ((∃ e ∈ blocks, ∃ j,
        w ∈ Set.range (genScatterMergeTreeOutputEmbedding
          (packetPowerTree6 (α := α)) e j)) ∨
       ∃ k, w ∈ Set.range (tail k))

/-- Every bag has a local macro partition: root and interior bags use their
checked constructions, while top-level bags have empty support. -/
theorem flowA7_receiverMacroData_exists {d : Nat} {α : Type} [LinearOrder α]
    (hd : 7 ≤ d) (t : Nat) (ht2 : 2 ≤ t) (ht : t < tf7 d)
    (v : Fin (64 ^ d) → α)
    (hpack : ∀ q : KBag 64 d,
      PacketSortedOn (wireSets (flowSizes7 d hd) t q) v)
    (b : KBag 64 d) :
    ∃ data : FlowA7ReceiverMacroData hd t ht2 ht v b, True := by
  by_cases hbroot : b = KBag.root 64 d
  · subst b
    obtain ⟨r, tail, blocks, hr, hnd, hdis, hdepth, hblockSorted, hsorted,
        htailSorted, hblockTail, htailPairwise, hcover⟩ :=
      flowA7_root_receiver_fullBlocksBatch hd t ht2 ht v hpack
    have hblockTail' : ∀ e ∈ blocks, ∀ k x y, e x ≠ tail k y := by
      intro e he k x y
      exact hblockTail e he x k y
    have hcover' : ∀ w,
        w ∈ wireSets (flowSizes7 d hd) (t + 1) (KBag.root 64 d) ↔
          ((∃ e ∈ blocks, ∃ j, w ∈ Set.range
              (genScatterMergeTreeOutputEmbedding
                (packetPowerTree6 (α := α)) e j)) ∨
            ∃ k, w ∈ Set.range (tail k)) := by
      intro w
      constructor
      · intro hw
        rcases (hcover w).2 hw with hin | htail
        · obtain ⟨e, he, hwe⟩ := hin
          exact Or.inl ⟨e, he, (genScatterMergeTreeOutputEmbedding_support_iff
            (packetPowerTree6 (α := α)) e w).2 hwe⟩
        · exact Or.inr htail
      · intro hw
        apply (hcover w).1
        rcases hw with hblocks | htail
        · obtain ⟨e, he, j, hwe⟩ := hblocks
          exact Or.inl ⟨e, he, (genScatterMergeTreeOutputEmbedding_support_iff
            (packetPowerTree6 (α := α)) e w).1 ⟨j, hwe⟩⟩
        · exact Or.inr htail
    refine ⟨⟨r, tail, blocks, hr, hnd, hdis, hblockTail',
      htailPairwise, hblockSorted, hsorted, htailSorted, hcover'⟩, trivial⟩
  · by_cases hbtop : b.l = d
    · have hempty := flowA7_topReceiver_wireSet_empty hd (t + 1) (by omega)
        (by omega) b hbtop
      refine ⟨{
        tailCount := 0
        tail := Fin.elim0
        blocks := []
        tailCount_lt := by decide
        blocks_nodup := by simp
        blocks_disjoint := by simp
        block_tail_disjoint := by simp
        tail_pairwise := by simp
        output_blockSorted := by simp
        output_sorted := by simp
        tail_sorted := by intro k; exact Fin.elim0 k
        support_cover := ?_ }, trivial⟩
      intro w
      simp [hempty]
    · have hbpos : 1 ≤ b.l := by
        by_contra hpos
        have hl0 : b.l = 0 := by omega
        have hx0 : b.x = 0 := by
          have hx := b.hx
          simp [hl0] at hx
          omega
        apply hbroot
        apply KBag.ext <;> simp [KBag.root, hl0, hx0]
      have hbchild : b.l < d := Nat.lt_of_le_of_ne b.hl hbtop
      obtain ⟨blocks, r, tail, hr, hnd, hdis, houtputDis, hchunkDis,
          hblockTail, htailPairwise, hsorted, htailSorted, hcover, hdepth,
          hblockSorted⟩ :=
        flowA7_receiver_macroSource_outputPartition hd t ht2 ht b hbpos
          hbchild v hpack
      have hblockTail' : ∀ e ∈ blocks, ∀ k x y, e x ≠ tail k y := by
        intro e he k x y heq
        obtain ⟨j, z, hz⟩ :=
          (genScatterMergeTreeOutputEmbedding_support_iff
            (packetPowerTree6 (α := α)) e (e x)).2
            (by exact ⟨x, rfl⟩)
        have houtEq : genScatterMergeTreeOutputEmbedding
            (packetPowerTree6 (α := α)) e j z = tail k y := by
          exact hz.trans heq
        exact hblockTail e he j k z y houtEq
      refine ⟨⟨r, tail, blocks, hr, hnd, hdis, hblockTail',
        htailPairwise, hblockSorted, hsorted, htailSorted, hcover⟩, trivial⟩

/- Combine finite receiver-local block/tail decompositions into one physical
batch. The receiver supports provide cross-family separation; consequently
all local 57-layer merge trees can execute in parallel in a single 57-layer
network, with the untouched tails retained as sorted packets. -/
set_option maxHeartbeats 1000000 in
theorem finiteReceiverMacroBatch_of_list {ι : Type} {N : Nat} [Fintype ι] [DecidableEq ι]
    {α : Type} [LinearOrder α]
    (v : Fin N → α) (tree : PacketMergeTree α 4096)
    (hdepth : tree.network.depth ≤ 57)
    (support : ι → Finset (Fin N))
    (blocks : ι → List (Fin 4096 ↪ Fin N))
    (allBlocks : List (Fin 4096 ↪ Fin N))
    (hallBlocks : ∀ e, e ∈ allBlocks ↔ ∃ i, e ∈ blocks i)
    (hallBlocksNodup : allBlocks.Nodup)
    (tailCount : ι → Nat)
    (tail : ∀ i, Fin (tailCount i) → Fin 64 ↪ Fin N)
    (hsupportDisjoint : ∀ i i', i ≠ i' → Disjoint (support i) (support i'))
    (hblocksNodup : ∀ i, (blocks i).Nodup)
    (hblocksDisjoint : ∀ i, ∀ e ∈ blocks i, ∀ f ∈ blocks i,
      e ≠ f → ∀ x y, e x ≠ f y)
    (hblockTailDisjoint : ∀ i, ∀ e ∈ blocks i, ∀ k x y,
      e x ≠ tail i k y)
    (htailPairwise : ∀ i, ∀ k k', k ≠ k' → ∀ x y,
      tail i k x ≠ tail i k' y)
    (houtputSorted : ∀ i, ∀ e ∈ blocks i,
      ∀ j : Fin tree.leafCount,
      Monotone (fun x =>
        (genScatterMergeTreeBatch tree (blocks i)).exec v
          (genScatterMergeTreeOutputEmbedding
            tree e j x)))
    (htailSorted : ∀ i k, Monotone (fun x => v (tail i k x)))
    (hsupportCover : ∀ i w,
      w ∈ support i ↔
        ((∃ e ∈ blocks i, ∃ j,
          w ∈ Set.range (genScatterMergeTreeOutputEmbedding tree e j)) ∨
         ∃ k, w ∈ Set.range (tail i k))) :
    allBlocks.Nodup ∧
      (∀ e ∈ allBlocks, ∀ f ∈ allBlocks, e ≠ f → ∀ x y, e x ≠ f y) ∧
      (genScatterMergeTreeBatch tree allBlocks).depth ≤ 57 ∧
      (∀ e ∈ allBlocks, ∀ j : Fin tree.leafCount,
        Monotone (fun x =>
          (genScatterMergeTreeBatch tree allBlocks).exec v
            (genScatterMergeTreeOutputEmbedding tree e j x))) ∧
      (∀ e ∈ allBlocks, ∀ k : (Σ i, Fin (tailCount i)), ∀ x y,
        e x ≠ (tail k.1 k.2) y) ∧
      (∀ k k' : (Σ i, Fin (tailCount i)), k ≠ k' → ∀ x y,
        (tail k.1 k.2) x ≠ (tail k'.1 k'.2) y) ∧
      (∀ k : (Σ i, Fin (tailCount i)), Monotone (fun x => v (tail k.1 k.2 x))) ∧
      (∀ w, w ∈ Finset.univ.biUnion support ↔
        ((∃ e ∈ allBlocks, ∃ j,
          w ∈ Set.range (genScatterMergeTreeOutputEmbedding tree e j)) ∨
         ∃ k : (Σ i, Fin (tailCount i)), w ∈ Set.range (tail k.1 k.2))) := by
  classical
  let allTail : (Σ i, Fin (tailCount i)) → Fin 64 ↪ Fin N :=
    fun k => tail k.1 k.2
  have hmemLocal (e : Fin 4096 ↪ Fin N) (he : e ∈ allBlocks) :
      ∃ i, e ∈ blocks i := by
    exact hallBlocks e |>.1 he
  have hblockSupport (i : ι) (e : Fin 4096 ↪ Fin N)
      (he : e ∈ blocks i) (x : Fin 4096) : e x ∈ support i := by
    have hchunks : ∃ j, e x ∈ Set.range
        (genScatterMergeTreeOutputEmbedding tree e j) :=
      (genScatterMergeTreeOutputEmbedding_support_iff tree e (e x)).2 ⟨x, rfl⟩
    obtain ⟨j, y, hy⟩ := hchunks
    exact (hsupportCover i (e x)).2
      (Or.inl ⟨e, he, j, y, hy⟩)
  have hGlobalDisjoint : ∀ e ∈ allBlocks, ∀ f ∈ allBlocks,
      e ≠ f → ∀ x y, e x ≠ f y := by
    intro e he f hf hne x y heq
    obtain ⟨i, hei⟩ := hmemLocal e he
    obtain ⟨i', hfi'⟩ := hmemLocal f hf
    by_cases hii' : i = i'
    · subst i'
      exact hblocksDisjoint i e hei f hfi' hne x y heq
    · have hmemE := hblockSupport i e hei x
      have hmemF := hblockSupport i' f hfi' y
      exact (Finset.disjoint_left.mp (hsupportDisjoint i i' hii')) hmemE
        (by simpa [heq] using hmemF)
  have hGlobalNodup : allBlocks.Nodup := hallBlocksNodup
  have hGlobalDepth :
      (genScatterMergeTreeBatch tree allBlocks).depth ≤ 57 :=
    genScatterMergeTreeBatch_depth_le tree allBlocks hGlobalNodup
      hGlobalDisjoint 57 hdepth
  have hGlobalBlockTail : ∀ e ∈ allBlocks,
      ∀ k : (Σ i, Fin (tailCount i)), ∀ x y,
        e x ≠ (allTail k) y := by
    intro e he k x y heq
    obtain ⟨i, hei⟩ := hmemLocal e he
    rcases k with ⟨i', k⟩
    by_cases hii' : i = i'
    · subst i'
      exact hblockTailDisjoint i e hei k x y heq
    · have hmemE := hblockSupport i e hei x
      have hmemTail := (hsupportCover i' (tail i' k y)).2
        (Or.inr ⟨k, y, rfl⟩)
      exact (Finset.disjoint_left.mp (hsupportDisjoint i i' hii')) hmemE
        (by simpa [heq] using hmemTail)
  have hGlobalTailPairwise : ∀ k k' : (Σ i, Fin (tailCount i)),
      k ≠ k' → ∀ x y, (allTail k) x ≠ (allTail k') y := by
    intro k k' hne x y heq
    rcases k with ⟨i, j⟩
    rcases k' with ⟨i', j'⟩
    by_cases hii' : i = i'
    · subst i'
      have hjj' : j ≠ j' := by
        intro hj
        apply hne
        cases hj
        rfl
      exact htailPairwise i j j' hjj' x y heq
    · have hmemTail := (hsupportCover i (tail i j x)).2
        (Or.inr ⟨j, x, rfl⟩)
      have hmemTail' := (hsupportCover i' (tail i' j' y)).2
        (Or.inr ⟨j', y, rfl⟩)
      have hmemTailEq : tail i j x ∈ support i' := by
        rw [heq]
        exact hmemTail'
      exact (Finset.disjoint_left.mp (hsupportDisjoint i i' hii')) hmemTail
        hmemTailEq
  refine ⟨hGlobalNodup, hGlobalDisjoint, hGlobalDepth, ?_,
    hGlobalBlockTail, hGlobalTailPairwise, ?_, ?_⟩
  · intro e he j
    obtain ⟨i, hei⟩ := hmemLocal e he
    intro x y hxy
    change (genScatterMergeTreeBatch tree allBlocks).exec v
        (e (PacketMergeTree.chunkIndex tree j x)) ≤
      (genScatterMergeTreeBatch tree allBlocks).exec v
        (e (PacketMergeTree.chunkIndex tree j y))
    have hglobalAt (z : Fin 64) :
        (genScatterMergeTreeBatch tree allBlocks).exec v
            (e (PacketMergeTree.chunkIndex tree j z)) =
          (genScatter tree.network e).exec v
            (e (PacketMergeTree.chunkIndex tree j z)) :=
      genScatterMergeTreeBatch_exec_inside tree allBlocks
        hGlobalNodup hGlobalDisjoint v e he
        (PacketMergeTree.chunkIndex tree j z)
    have hlocalAt (z : Fin 64) :
        (genScatterMergeTreeBatch tree (blocks i)).exec v
            (e (PacketMergeTree.chunkIndex tree j z)) =
          (genScatter tree.network e).exec v
            (e (PacketMergeTree.chunkIndex tree j z)) :=
      genScatterMergeTreeBatch_exec_inside tree (blocks i)
        (hblocksNodup i) (hblocksDisjoint i) v e hei
        (PacketMergeTree.chunkIndex tree j z)
    rw [hglobalAt x, hglobalAt y, ← hlocalAt x, ← hlocalAt y]
    exact houtputSorted i e hei j hxy
  · intro k
    exact htailSorted k.1 k.2
  · intro w
    constructor
    · intro hw
      obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hw
      rcases (hsupportCover i w).1 hi with hout | htail
      · obtain ⟨e, he, j, y, hy⟩ := hout
        have heGlobal : e ∈ allBlocks := (hallBlocks e).2 ⟨i, he⟩
        exact Or.inl ⟨e, heGlobal, j, y, hy⟩
      · obtain ⟨k, y, hy⟩ := htail
        exact Or.inr ⟨⟨i, k⟩, y, hy⟩
    · intro hw
      rcases hw with hout | htail
      · obtain ⟨e, he, j, y, hy⟩ := hout
        obtain ⟨i, hei⟩ := hmemLocal e he
        have hsource : w ∈ support i :=
          (hsupportCover i w).2 (Or.inl ⟨e, hei, j, y, hy⟩)
        exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, hsource⟩
      · rcases htail with ⟨⟨i, k⟩, y, hy⟩
        have hsource : w ∈ support i :=
          (hsupportCover i w).2 (Or.inr ⟨k, y, hy⟩)
        exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, hsource⟩

set_option maxRecDepth 10000 in
/-- Combine the regular full blocks of disjoint canonical streams with the
full blocks of their pooled residues and endpoints in one physical batch. -/
theorem canonicalStreamAndExceptionPool_fullBlocks_batch
    {N : Nat} {α I E : Type} [LinearOrder α] [Fintype I] [DecidableEq I]
    [Fintype E] [DecidableEq E]
    {P : I → CanonicalPacketFamily N}
    {streamSupport : I → Finset (Fin N)} {v : Fin N → α}
    (D : CanonicalStreamFullBlockData P streamSupport v)
    (endpoint : E → Finset (Fin N))
    (hstreamDisjoint : ∀ i i', i ≠ i' →
      Disjoint (streamSupport i) (streamSupport i'))
    (hstreamEndpoint : ∀ i e, Disjoint (streamSupport i) (endpoint e))
    (Q : CanonicalPacketFamily N) (qSupport : Finset (Fin N))
    (hQsupport : qSupport = Finset.univ.biUnion
      (canonicalStreamFullBlockExceptionPacket D endpoint))
    (B : CanonicalPacketFullBlockData Q qSupport v)
     :
    let J := I ⊕ Unit
    let batchSupport : J → Finset (Fin N) := fun j =>
      match j with
      | Sum.inl i => packetBlockListSupport (D.blocks i)
      | Sum.inr _ => qSupport
    let blocks : J → List (Fin 4096 ↪ Fin N) := fun j =>
      match j with
      | Sum.inl i => D.blocks i
      | Sum.inr _ => B.blocks
    let tailCount : J → Nat := fun j =>
      match j with
      | Sum.inl _ => 0
      | Sum.inr _ => B.remainder
    let tail : ∀ j, Fin (tailCount j) → Fin 64 ↪ Fin N := fun j =>
      match j with
      | Sum.inl _ => Fin.elim0
      | Sum.inr _ => B.tail
    ∃ allBlocks : List (Fin 4096 ↪ Fin N),
      allBlocks.Nodup ∧
      (∀ e ∈ allBlocks, ∀ f ∈ allBlocks, e ≠ f → ∀ x y, e x ≠ f y) ∧
      (genScatterMergeTreeBatch (packetPowerTree6 (α := α)) allBlocks).depth ≤ 57 ∧
      (∀ e ∈ allBlocks, ∀ j : Fin (packetPowerTree6 (α := α)).leafCount,
        Monotone (fun x =>
          (genScatterMergeTreeBatch (packetPowerTree6 (α := α)) allBlocks).exec v
            (genScatterMergeTreeOutputEmbedding (packetPowerTree6 (α := α)) e j x))) ∧
      (∀ e ∈ allBlocks, ∀ k : (Σ j : J, Fin (tailCount j)), ∀ x y,
        e x ≠ tail k.1 k.2 y) ∧
      (∀ k k' : (Σ j : J, Fin (tailCount j)), k ≠ k' → ∀ x y,
        tail k.1 k.2 x ≠ tail k'.1 k'.2 y) ∧
      (∀ k : (Σ j : J, Fin (tailCount j)),
        Monotone (fun x => v (tail k.1 k.2 x))) ∧
      (∀ w, w ∈ Finset.univ.biUnion batchSupport ↔
        (∃ e ∈ allBlocks, ∃ j,
          w ∈ Set.range (genScatterMergeTreeOutputEmbedding (packetPowerTree6 (α := α)) e j)) ∨
         ∃ k : (Σ j : J, Fin (tailCount j)), w ∈ Set.range (tail k.1 k.2)) := by
  classical
  let J := I ⊕ Unit
  let batchSupport : J → Finset (Fin N) := fun j =>
    match j with
    | Sum.inl i => packetBlockListSupport (D.blocks i)
    | Sum.inr _ => qSupport
  let blocks : J → List (Fin 4096 ↪ Fin N) := fun j =>
    match j with
    | Sum.inl i => D.blocks i
    | Sum.inr _ => B.blocks
  let tailCount : J → Nat := fun j =>
    match j with
    | Sum.inl _ => 0
    | Sum.inr _ => B.remainder
  let tail : ∀ j, Fin (tailCount j) → Fin 64 ↪ Fin N := fun j =>
    match j with
    | Sum.inl _ => Fin.elim0
    | Sum.inr _ => B.tail
  let blockSet : Finset (Fin 4096 ↪ Fin N) :=
    Finset.univ.biUnion (fun j => (blocks j).toFinset)
  let allBlocks := blockSet.toList
  have hallBlocks (e : Fin 4096 ↪ Fin N) :
      e ∈ allBlocks ↔ ∃ j, e ∈ blocks j := by
    simp [allBlocks, blockSet, Finset.mem_biUnion]
  have hblocksNodup : ∀ j, (blocks j).Nodup := by
    intro j
    cases j with
    | inl i =>
        rcases D.perStream i with ⟨_, _, hnd, _, _, _, _, _, _, _, _, _⟩
        exact hnd
    | inr _ => exact B.blocks_nodup
  have hblocksDisjoint : ∀ j, ∀ e ∈ blocks j, ∀ f ∈ blocks j,
      e ≠ f → ∀ x y, e x ≠ f y := by
    intro j
    cases j with
    | inl i =>
        rcases D.perStream i with ⟨_, _, _, hdis, _, _, _, _, _, _, _, _⟩
        exact hdis
    | inr _ => exact B.blocks_disjoint
  have hblockSupport (j : J) (e : Fin 4096 ↪ Fin N)
      (he : e ∈ blocks j) (x : Fin 4096) : e x ∈ batchSupport j := by
    cases j with
    | inl i =>
        exact (packetBlockListSupport_mem_iff (D.blocks i) (e x)).2
          ⟨e, he, x, rfl⟩
    | inr _ =>
        exact (B.support_cover (e x)).1
          (Or.inl ⟨e, he, x, rfl⟩)
  have htailSupport (j : J) (k : Fin (tailCount j)) (x : Fin 64) :
      tail j k x ∈ batchSupport j := by
    cases j with
    | inl i => exact Fin.elim0 k
    | inr _ =>
        exact (B.support_cover (B.tail k x)).1
          (Or.inr ⟨k, x, rfl⟩)
  have hsupportDisjoint : ∀ j j', j ≠ j' →
      Disjoint (batchSupport j) (batchSupport j') := by
    intro j j' hne
    cases j with
    | inl i =>
        cases j' with
        | inl i' =>
            have hii : i ≠ i' := by
              intro heq
              subst i'
              exact hne rfl
            apply Finset.disjoint_left.mpr
            intro w hw hw'
            obtain ⟨e, he, x, rfl⟩ :=
              (packetBlockListSupport_mem_iff (D.blocks i) w).mp hw
            obtain ⟨f, hf, y, heq⟩ :=
              (packetBlockListSupport_mem_iff (D.blocks i') (e x)).mp hw'
            have heIn : e x ∈ streamSupport i :=
              D.block_subset_support i e he (Set.mem_range_self x)
            have hfIn : f y ∈ streamSupport i' :=
              D.block_subset_support i' f hf (Set.mem_range_self y)
            exact (Finset.disjoint_left.mp (hstreamDisjoint i i' hii)) heIn
              (by simpa [heq] using hfIn)
        | inr _ =>
            have hdis : Disjoint (packetBlockListSupport (D.blocks i)) qSupport := by
              rw [hQsupport]
              exact canonicalStreamFullBlock_blocks_disjoint_exceptionPool
                D endpoint hstreamDisjoint hstreamEndpoint i
            exact hdis
    | inr _ =>
        cases j' with
        | inl i' =>
            have hdis : Disjoint (packetBlockListSupport (D.blocks i')) qSupport := by
              rw [hQsupport]
              exact canonicalStreamFullBlock_blocks_disjoint_exceptionPool
                D endpoint hstreamDisjoint hstreamEndpoint i'
            exact hdis.symm
        | inr _ => exact (hne rfl).elim
  have hblocksGlobalDisjoint : ∀ e ∈ allBlocks, ∀ f ∈ allBlocks,
      e ≠ f → ∀ x y, e x ≠ f y := by
    intro e he f hf hne x y heq
    obtain ⟨j, hj⟩ := (hallBlocks e).mp he
    obtain ⟨j', hj'⟩ := (hallBlocks f).mp hf
    by_cases hsame : j = j'
    · subst j'
      exact hblocksDisjoint j e hj f hj' hne x y heq
    · have hx := hblockSupport j e hj x
      have hy := hblockSupport j' f hj' y
      exact (Finset.disjoint_left.mp (hsupportDisjoint j j' hsame)) hx
        (by simpa [heq] using hy)
  have hblockTailDisjoint : ∀ j, ∀ e ∈ blocks j,
      ∀ k : Fin (tailCount j), ∀ x y, e x ≠ tail j k y := by
    intro j
    cases j with
    | inl i => intro e he k x y; exact Fin.elim0 k
    | inr _ =>
        intro e he k x y
        exact B.block_tail_disjoint e he x k y
  have htailPairwise : ∀ j, ∀ k k' : Fin (tailCount j), k ≠ k' →
      ∀ x y, tail j k x ≠ tail j k' y := by
    intro j
    cases j with
    | inl i => intro k; exact Fin.elim0 k
    | inr _ => exact B.tail_pairwise
  have houtputSorted : ∀ j, ∀ e ∈ blocks j,
      ∀ k : Fin (packetPowerTree6 (α := α)).leafCount,
        Monotone (fun x =>
          (genScatterMergeTreeBatch (packetPowerTree6 (α := α)) (blocks j)).exec v
            (genScatterMergeTreeOutputEmbedding (packetPowerTree6 (α := α)) e k x)) := by
    intro j
    cases j with
    | inl i =>
        rcases D.perStream i with
          ⟨_, _, _, _, _, _, hsorted, _, _, _, _, _⟩
        exact hsorted
    | inr _ => exact B.output_sorted
  have htailSorted : ∀ j k, Monotone (fun x => v (tail j k x)) := by
    intro j
    cases j with
    | inl i => intro k; exact Fin.elim0 k
    | inr _ => exact B.tail_sorted
  have hsupportCover : ∀ j w,
      w ∈ batchSupport j ↔
        ((∃ e ∈ blocks j, ∃ k,
          w ∈ Set.range (genScatterMergeTreeOutputEmbedding (packetPowerTree6 (α := α)) e k)) ∨
         ∃ k, w ∈ Set.range (tail j k)) := by
    intro j w
    cases j with
    | inl i =>
        simpa [batchSupport, blocks, Set.mem_range] using
          (packetBlockListSupport_eq_outputChunks
            (packetPowerTree6 (α := α)) (D.blocks i) w)
    | inr _ =>
        constructor
        · intro hw
          rcases (B.support_cover w).2 hw with hblock | htail
          · obtain ⟨e, he, hwe⟩ := hblock
            exact Or.inl ⟨e, he,
              (genScatterMergeTreeOutputEmbedding_support_iff (packetPowerTree6 (α := α)) e w).2 hwe⟩
          · exact Or.inr htail
        · intro hw
          rcases hw with hblock | htail
          · obtain ⟨e, he, hwe⟩ := hblock
            exact (B.support_cover w).1 (Or.inl ⟨e, he,
              (genScatterMergeTreeOutputEmbedding_support_iff (packetPowerTree6 (α := α)) e w).1 hwe⟩)
          · exact (B.support_cover w).1 (Or.inr htail)
  have hnodup : allBlocks.Nodup := blockSet.nodup_toList
  have hglobal := finiteReceiverMacroBatch_of_list v (packetPowerTree6 (α := α)) packetPowerTree6_depth_le batchSupport
    blocks allBlocks hallBlocks hnodup tailCount tail hsupportDisjoint
    hblocksNodup hblocksDisjoint hblockTailDisjoint htailPairwise
    houtputSorted htailSorted hsupportCover
  rcases hglobal with
    ⟨hglobalNodup, hglobalDisjoint, hglobalDepth, hglobalSorted,
      hglobalBlockTail, hglobalTailPairwise, hglobalTailSorted, hglobalCover⟩
  exact ⟨allBlocks, hglobalNodup, hglobalDisjoint, hglobalDepth,
    hglobalSorted, hglobalBlockTail, hglobalTailPairwise,
    hglobalTailSorted, hglobalCover⟩

set_option maxRecDepth 10000 in
/-- Apply the regular-stream plus exception-pool batch theorem to an actual
interior receiver. The receiver is covered by the batch output chunks and the
pool's fewer-than-64 leftover packets. -/
theorem flowA7_receiver_regularTailPool_commonBatch
    {d : Nat} {α : Type} [LinearOrder α]
    (hd : 7 ≤ d) (t : Nat) (ht2 : 2 ≤ t) (ht : t < tf7 d)
    (b : KBag 64 d) (hb : 1 ≤ b.l) (hchildLevel : b.l < d)
    (v : Fin (64 ^ d) → α)
    (hpack : ∀ q : KBag 64 d,
      PacketSortedOn (wireSets (flowSizes7 d hd) t q) v) :
    ∃ allBlocks : List (Fin 4096 ↪ Fin (64 ^ d)),
    ∃ r : Nat, ∃ tail : Fin r → Fin 64 ↪ Fin (64 ^ d),
      allBlocks.Nodup ∧
      (∀ e ∈ allBlocks, ∀ f ∈ allBlocks, e ≠ f → ∀ x y, e x ≠ f y) ∧
      (genScatterMergeTreeBatch (packetPowerTree6 (α := α)) allBlocks).depth ≤ 57 ∧
      (∀ e ∈ allBlocks, ∀ j : Fin (packetPowerTree6 (α := α)).leafCount,
        Monotone (fun x =>
          (genScatterMergeTreeBatch (packetPowerTree6 (α := α)) allBlocks).exec
            ((flowA7_sourcePortRepairStage hd t ht2 ht).exec v)
            (genScatterMergeTreeOutputEmbedding
              (packetPowerTree6 (α := α)) e j x))) ∧
      r < 64 ∧
      (∀ e ∈ allBlocks, ∀ k : Fin r, ∀ x y, e x ≠ tail k y) ∧
      (∀ k k' : Fin r, k ≠ k' → ∀ x y, tail k x ≠ tail k' y) ∧
      (∀ k, Monotone (fun x =>
        ((flowA7_sourcePortRepairStage hd t ht2 ht).exec v) (tail k x))) ∧
      (∀ w, w ∈ wireSets (flowSizes7 d hd) (t + 1) b ↔
        ((∃ e ∈ allBlocks, ∃ j,
          w ∈ Set.range (genScatterMergeTreeOutputEmbedding
            (packetPowerTree6 (α := α)) e j)) ∨
         ∃ k, w ∈ Set.range (tail k))) := by
  classical
  obtain ⟨stream, endpoint, D, Q, hQcount, hQcontract, hQsupport,
      hstreamDisjoint, hstreamEndpoint, hendpointPairwise, hreceiverCover,
      hreceiverPartition, hB⟩ :=
    flowA7_receiver_regularTailPool hd t ht2 ht b hb hchildLevel v hpack
  rcases hB with ⟨B⟩
  let I := Unit ⊕ (Fin 64 × Bool)
  let E := {e : Unit ⊕ Fin 64 // endpoint e ≠ ∅}
  let J := I ⊕ Unit
  let streamSupport : I → Finset (Fin (64 ^ d)) :=
    fun i => Finset.univ.biUnion (stream i).packet
  let batchSupport : J → Finset (Fin (64 ^ d)) := fun j =>
    match j with
    | Sum.inl i => packetBlockListSupport (D.blocks i)
    | Sum.inr _ => Finset.univ.biUnion Q.packet
  let tailCount : J → Nat := fun j =>
    match j with
    | Sum.inl _ => 0
    | Sum.inr _ => B.remainder
  let batchTail : ∀ j, Fin (tailCount j) → Fin 64 ↪ Fin (64 ^ d) := fun j =>
    match j with
    | Sum.inl _ => Fin.elim0
    | Sum.inr _ => B.tail
  have hcombined := canonicalStreamAndExceptionPool_fullBlocks_batch
    D (fun e : E => endpoint e.1) hstreamDisjoint
    (fun i e => hstreamEndpoint i e.1) Q
    (Finset.univ.biUnion Q.packet) hQsupport B
  rcases hcombined with
    ⟨allBlocks, hnodup, hblockDisjoint, hdepth, houtputSorted,
      hblockTail, htailPairwise, htailSorted, hbatchCover⟩
  have hbatchSupportEq :
      Finset.univ.biUnion batchSupport = wireSets (flowSizes7 d hd) (t + 1) b := by
    ext w
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨j, hj⟩
      cases j with
      | inl i =>
          obtain ⟨e, he, hwe⟩ :=
            (packetBlockListSupport_mem_iff (D.blocks i) w).mp hj
          exact (hreceiverPartition w).2 (Or.inl ⟨i, e, he, hwe⟩)
      | inr _ => exact (hreceiverPartition w).2 (Or.inr hj)
    · intro hw
      rcases (hreceiverPartition w).1 hw with hregular | hpool
      · obtain ⟨i, e, he, hwe⟩ := hregular
        exact ⟨Sum.inl i,
          (packetBlockListSupport_mem_iff (D.blocks i) w).2 ⟨e, he, hwe⟩⟩
      · exact ⟨Sum.inr (), hpool⟩
  have htailCover (w : Fin (64 ^ d)) :
      (∃ k : (Σ j : J, Fin (tailCount j)),
        w ∈ Set.range (batchTail k.1 k.2)) ↔
      ∃ k : Fin B.remainder, w ∈ Set.range (B.tail k) := by
    constructor
    · rintro ⟨⟨j, k⟩, hk⟩
      cases j with
      | inl i => exact Fin.elim0 k
      | inr _ => exact ⟨k, by simpa [batchTail, tailCount] using hk⟩
    · rintro ⟨k, hk⟩
      exact ⟨⟨Sum.inr (), k⟩, by simpa [batchTail, tailCount] using hk⟩
  have hblockTail' : ∀ e ∈ allBlocks, ∀ k : Fin B.remainder,
      ∀ x y, e x ≠ B.tail k y := by
    intro e he k x y
    exact hblockTail e he ⟨Sum.inr (), k⟩ x y
  have htailPairwise' : ∀ k k' : Fin B.remainder, k ≠ k' →
      ∀ x y, B.tail k x ≠ B.tail k' y := by
    intro k k' hne x y
    apply htailPairwise ⟨Sum.inr (), k⟩ ⟨Sum.inr (), k'⟩ ?_ x y
    intro heq
    apply hne
    cases heq
    rfl
  have htailSorted' : ∀ k : Fin B.remainder,
      Monotone (fun x =>
        ((flowA7_sourcePortRepairStage hd t ht2 ht).exec v) (B.tail k x)) := by
    intro k
    exact htailSorted ⟨Sum.inr (), k⟩
  have hcoverage : ∀ w, w ∈ wireSets (flowSizes7 d hd) (t + 1) b ↔
      ((∃ e ∈ allBlocks, ∃ j,
        w ∈ Set.range (genScatterMergeTreeOutputEmbedding
          (packetPowerTree6 (α := α)) e j)) ∨
       ∃ k : Fin B.remainder, w ∈ Set.range (B.tail k)) := by
    intro w
    have hc := hbatchCover w
    rw [hbatchSupportEq] at hc
    constructor
    · intro hw
      rcases hc.mp hw with houtput | htail
      · exact Or.inl houtput
      · exact Or.inr ((htailCover w).1 htail)
    · intro hw
      rcases hw with houtput | htail
      · exact hc.mpr (Or.inl houtput)
      · exact hc.mpr (Or.inr ((htailCover w).2 htail))
  exact ⟨allBlocks, B.remainder, B.tail, hnodup, hblockDisjoint, hdepth,
    houtputSorted, B.remainder_lt, hblockTail', htailPairwise', htailSorted',
    hcoverage⟩

/-- Choose the checked local macro partition for every receiver bag. -/
noncomputable def flowA7_receiverMacroData {d : Nat} {α : Type}
    [LinearOrder α] (hd : 7 ≤ d) (t : Nat) (ht2 : 2 ≤ t)
    (ht : t < tf7 d) (v : Fin (64 ^ d) → α)
    (hpack : ∀ q : KBag 64 d,
      PacketSortedOn (wireSets (flowSizes7 d hd) t q) v)
    (b : KBag 64 d) : FlowA7ReceiverMacroData hd t ht2 ht v b :=
  Classical.choose (flowA7_receiverMacroData_exists hd t ht2 ht v hpack b)

/-- The receiver-local root/interior/frontier partitions assemble into one
57-layer merge batch over every wire at the next scheduled stage. -/
theorem flowA7_globalReceiverMacroBatch {d : Nat} {α : Type} [LinearOrder α]
    (hd : 7 ≤ d) (t : Nat) (ht2 : 2 ≤ t) (ht : t < tf7 d)
    (v : Fin (64 ^ d) → α)
    (hpack : ∀ q : KBag 64 d,
      PacketSortedOn (wireSets (flowSizes7 d hd) t q) v) :
    ∃ allBlocks : List (Fin 4096 ↪ Fin (64 ^ d)),
      allBlocks.Nodup ∧
      (∀ e ∈ allBlocks, ∀ f ∈ allBlocks, e ≠ f → ∀ x y, e x ≠ f y) ∧
      (genScatterMergeTreeBatch (packetPowerTree6 (α := α)) allBlocks).depth ≤ 57 ∧
      (∀ e ∈ allBlocks, Monotone (fun i =>
        (genScatterMergeTreeBatch (packetPowerTree6 (α := α)) allBlocks).exec
          ((flowA7_sourcePortRepairStage hd t ht2 ht).exec v) (e i))) ∧
      (∀ e ∈ allBlocks, ∀ j : Fin (packetPowerTree6 (α := α)).leafCount,
        Monotone (fun i =>
          (genScatterMergeTreeBatch (packetPowerTree6 (α := α)) allBlocks).exec
            ((flowA7_sourcePortRepairStage hd t ht2 ht).exec v)
            (genScatterMergeTreeOutputEmbedding
              (packetPowerTree6 (α := α)) e j i))) ∧
      (∀ e ∈ allBlocks, ∀ j, ∀ f ∈ allBlocks, ∀ j',
        (e, j) ≠ (f, j') → ∀ x y,
          genScatterMergeTreeOutputEmbedding (packetPowerTree6 (α := α)) e j x ≠
            genScatterMergeTreeOutputEmbedding (packetPowerTree6 (α := α)) f j' y) ∧
      (∀ e ∈ allBlocks, ∀ b : KBag 64 d,
        ∀ k : Fin (FlowA7ReceiverMacroData.tailCount
          (flowA7_receiverMacroData hd t ht2 ht v hpack b)),
        ∀ x y, e x ≠ (FlowA7ReceiverMacroData.tail
          (flowA7_receiverMacroData hd t ht2 ht v hpack b)) k y) ∧
      (∀ e ∈ allBlocks, ∀ j, ∀ b : KBag 64 d,
        ∀ k : Fin (FlowA7ReceiverMacroData.tailCount
          (flowA7_receiverMacroData hd t ht2 ht v hpack b)),
        ∀ x y, genScatterMergeTreeOutputEmbedding
          (packetPowerTree6 (α := α)) e j x ≠
            (FlowA7ReceiverMacroData.tail
              (flowA7_receiverMacroData hd t ht2 ht v hpack b)) k y) ∧
      (∀ b b' : KBag 64 d, ∀ k k',
        (⟨b, k⟩ : Σ q : KBag 64 d,
          Fin (FlowA7ReceiverMacroData.tailCount
            (flowA7_receiverMacroData hd t ht2 ht v hpack q))) ≠ ⟨b', k'⟩ →
        ∀ x y,
          (FlowA7ReceiverMacroData.tail
            (flowA7_receiverMacroData hd t ht2 ht v hpack b)) k x ≠
          (FlowA7ReceiverMacroData.tail
            (flowA7_receiverMacroData hd t ht2 ht v hpack b')) k' y) ∧
      (∀ b k, Monotone (fun i =>
        ((flowA7_sourcePortRepairStage hd t ht2 ht).exec v)
          ((FlowA7ReceiverMacroData.tail
            (flowA7_receiverMacroData hd t ht2 ht v hpack b)) k i))) ∧
      (∀ w, w ∈ Finset.univ ↔
        ((∃ e ∈ allBlocks, ∃ j,
          w ∈ Set.range (genScatterMergeTreeOutputEmbedding
            (packetPowerTree6 (α := α)) e j)) ∨
         ∃ b, ∃ k : Fin (FlowA7ReceiverMacroData.tailCount
            (flowA7_receiverMacroData hd t ht2 ht v hpack b)),
           w ∈ Set.range (FlowA7ReceiverMacroData.tail
             (flowA7_receiverMacroData hd t ht2 ht v hpack b) k))) := by
  classical
  let data := flowA7_receiverMacroData hd t ht2 ht v hpack
  let support : KBag 64 d → Finset (Fin (64 ^ d)) :=
    fun b => wireSets (flowSizes7 d hd) (t + 1) b
  let blocks : KBag 64 d → List (Fin 4096 ↪ Fin (64 ^ d)) :=
    fun b => (data b).blocks
  let tailCount : KBag 64 d → Nat := fun b => (data b).tailCount
  let tail : ∀ b, Fin (tailCount b) → Fin 64 ↪ Fin (64 ^ d) :=
    fun b => (data b).tail
  let blockSet : Finset (Fin 4096 ↪ Fin (64 ^ d)) :=
    Finset.univ.biUnion (fun b => (blocks b).toFinset)
  let allBlocks := blockSet.toList
  have hsupportDisjoint : ∀ b b', b ≠ b' → Disjoint (support b) (support b') := by
    intro b b' hne
    exact wireSets_disjoint (flowSizes7 d hd) (t := t + 1) (by omega) b b' hne
  have hallBlocks (e : Fin 4096 ↪ Fin (64 ^ d)) :
      e ∈ allBlocks ↔ ∃ b, e ∈ blocks b := by
    simp [allBlocks, blockSet, Finset.mem_biUnion]
  have hblocksNodup : ∀ b, (blocks b).Nodup := fun b => (data b).blocks_nodup
  have hblocksDisjoint : ∀ b, ∀ e ∈ blocks b, ∀ f ∈ blocks b,
      e ≠ f → ∀ x y, e x ≠ f y := fun b => (data b).blocks_disjoint
  have hblockTailDisjoint : ∀ b, ∀ e ∈ blocks b, ∀ k x y,
      e x ≠ tail b k y := fun b => (data b).block_tail_disjoint
  have htailPairwise : ∀ b, ∀ k k', k ≠ k' → ∀ x y,
      tail b k x ≠ tail b k' y := fun b => (data b).tail_pairwise
  have houtputSorted : ∀ b, ∀ e ∈ blocks b,
      ∀ j : Fin (packetPowerTree6 (α := α)).leafCount,
        Monotone (fun x =>
          (genScatterMergeTreeBatch (packetPowerTree6 (α := α)) (blocks b)).exec
            ((flowA7_sourcePortRepairStage hd t ht2 ht).exec v)
            (genScatterMergeTreeOutputEmbedding
              (packetPowerTree6 (α := α)) e j x)) :=
    fun b => (data b).output_sorted
  have htailSorted : ∀ b k, Monotone (fun x =>
      ((flowA7_sourcePortRepairStage hd t ht2 ht).exec v) (tail b k x)) :=
    fun b => (data b).tail_sorted
  have hsupportCover : ∀ b w,
      w ∈ support b ↔
        ((∃ e ∈ blocks b, ∃ j, w ∈ Set.range
          (genScatterMergeTreeOutputEmbedding (packetPowerTree6 (α := α)) e j)) ∨
         ∃ k, w ∈ Set.range (tail b k)) :=
    fun b => (data b).support_cover
  have hnodup : allBlocks.Nodup := blockSet.nodup_toList
  have hglobal := finiteReceiverMacroBatch_of_list
    ((flowA7_sourcePortRepairStage hd t ht2 ht).exec v)
    (packetPowerTree6 (α := α)) packetPowerTree6_depth_le support blocks allBlocks
    hallBlocks hnodup tailCount tail hsupportDisjoint hblocksNodup
    hblocksDisjoint hblockTailDisjoint htailPairwise houtputSorted htailSorted
    hsupportCover
  have hcoverAll : Finset.univ.biUnion support = Finset.univ := by
    ext w
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and]
    constructor
    · intro _
      trivial
    · intro _
      obtain ⟨b, hb⟩ := wireSets_complete (flowSizes7 d hd)
        (t := t + 1) (by omega) w
      exact ⟨b, hb⟩
  rcases hglobal with ⟨hnd, hdis, hdepth, hsorted, hblockTail,
      htailPair, htailSortedGlobal, hcover⟩
  have hglobalBlockSorted : ∀ e ∈ allBlocks, Monotone (fun i =>
      (genScatterMergeTreeBatch (packetPowerTree6 (α := α)) allBlocks).exec
        ((flowA7_sourcePortRepairStage hd t ht2 ht).exec v) (e i)) := by
    intro e he
    obtain ⟨b, hb⟩ := (hallBlocks e).mp he
    intro i k hik
    change (genScatterMergeTreeBatch (packetPowerTree6 (α := α)) allBlocks).exec
        ((flowA7_sourcePortRepairStage hd t ht2 ht).exec v) (e i) ≤
      (genScatterMergeTreeBatch (packetPowerTree6 (α := α)) allBlocks).exec
        ((flowA7_sourcePortRepairStage hd t ht2 ht).exec v) (e k)
    have hglobalAt (x : Fin 4096) :
        (genScatterMergeTreeBatch (packetPowerTree6 (α := α)) allBlocks).exec
            ((flowA7_sourcePortRepairStage hd t ht2 ht).exec v) (e x) =
          (genScatterMergeTreeBatch (packetPowerTree6 (α := α)) (blocks b)).exec
            ((flowA7_sourcePortRepairStage hd t ht2 ht).exec v) (e x) := by
      change (genScatterBatch (packetPowerTree6 (α := α)).network allBlocks).exec
          ((flowA7_sourcePortRepairStage hd t ht2 ht).exec v) (e x) =
        (genScatterBatch (packetPowerTree6 (α := α)).network (blocks b)).exec
          ((flowA7_sourcePortRepairStage hd t ht2 ht).exec v) (e x)
      rw [genScatterBatch_exec_inside (packetPowerTree6 (α := α)).network
            allBlocks hnd hdis ((flowA7_sourcePortRepairStage hd t ht2 ht).exec v)
            e he x,
          genScatterBatch_exec_inside (packetPowerTree6 (α := α)).network
            (blocks b) (data b).blocks_nodup (data b).blocks_disjoint
            ((flowA7_sourcePortRepairStage hd t ht2 ht).exec v) e hb x]
    rw [hglobalAt i, hglobalAt k]
    exact (data b).output_blockSorted e hb hik
  have htailSortedB : ∀ b k, Monotone (fun i =>
      ((flowA7_sourcePortRepairStage hd t ht2 ht).exec v) (tail b k i)) := by
    intro b k
    exact htailSortedGlobal ⟨b, k⟩
  have hchunkSupport (e : Fin 4096 ↪ Fin (64 ^ d))
      (j : Fin (packetPowerTree6 (α := α)).leafCount) (x : Fin 64) :
      genScatterMergeTreeOutputEmbedding (packetPowerTree6 (α := α)) e j x ∈
        Set.range e := by
    exact (genScatterMergeTreeOutputEmbedding_support_iff
      (packetPowerTree6 (α := α)) e _).1 ⟨j, x, rfl⟩
  have houtputPairwise : ∀ e ∈ allBlocks, ∀ j, ∀ f ∈ allBlocks, ∀ j',
      (e, j) ≠ (f, j') → ∀ x y,
        genScatterMergeTreeOutputEmbedding (packetPowerTree6 (α := α)) e j x ≠
          genScatterMergeTreeOutputEmbedding (packetPowerTree6 (α := α)) f j' y := by
    intro e he j f hf j' hpair x y heq
    by_cases hef : e = f
    · subst f
      have hj : j ≠ j' := by
        intro hj
        apply hpair
        cases hj
        rfl
      exact genScatterMergeTreeOutputEmbedding_disjoint
        (packetPowerTree6 (α := α)) e hj x y heq
    · obtain ⟨a, ha⟩ := hchunkSupport e j x
      obtain ⟨b, hb⟩ := hchunkSupport f j' y
      exact hdis e he f hf hef a b (ha.trans (heq.trans hb.symm))
  have houtputTail : ∀ e ∈ allBlocks, ∀ j, ∀ b : KBag 64 d,
      ∀ k : Fin (tailCount b), ∀ x y,
        genScatterMergeTreeOutputEmbedding (packetPowerTree6 (α := α)) e j x ≠
          tail b k y := by
    intro e he j b k x y
    obtain ⟨a, ha⟩ := hchunkSupport e j x
    exact fun heq => hblockTail e he ⟨b, k⟩ a y (ha.trans heq)
  have htailPairwiseB : ∀ b b' : KBag 64 d, ∀ k k',
      (⟨b, k⟩ : Σ q : KBag 64 d, Fin (tailCount q)) ≠ ⟨b', k'⟩ →
      ∀ x y, tail b k x ≠ tail b' k' y := by
    intro b b' k k' hne x y
    exact htailPair ⟨b, k⟩ ⟨b', k'⟩ hne x y
  refine ⟨allBlocks, hnd, hdis, hdepth, hglobalBlockSorted, hsorted, houtputPairwise,
    ?_, houtputTail, htailPairwiseB, htailSortedB, ?_⟩
  · intro e he b k x y
    exact hblockTail e he ⟨b, k⟩ x y
  · intro w
    rw [← hcoverAll]
    constructor
    · intro hw
      rcases (hcover w).1 hw with hblocks | htail
      · exact Or.inl hblocks
      · rcases htail with ⟨⟨b, k⟩, y, hy⟩
        exact Or.inr ⟨b, k, y, hy⟩
    · intro hw
      rcases hw with hblocks | ⟨b, k, y, hy⟩
      · exact (hcover w).2 (Or.inl hblocks)
      · exact (hcover w).2 (Or.inr ⟨⟨b, k⟩, y, hy⟩)
/-- The canonical packet count produced by a receiver is exactly the
scheduler's next-stage wire count divided by 64. -/
theorem flowA7_receiver_allCases_packetCount {d : Nat} {α : Type}
    [LinearOrder α]
    (hd : 7 ≤ d) (t : Nat) (ht2 : 2 ≤ t) (ht : t < tf7 d)
    (b : KBag 64 d) (hb : 1 ≤ b.l) (hchild : b.l < d)
    (v : Fin (64 ^ d) → α)
    (hpack : ∀ q : KBag 64 d,
      PacketSortedOn (wireSets (flowSizes7 d hd) t q) v) :
    ∃ m : Nat, ∃ packets : Fin m → Fin 64 ↪ Fin (64 ^ d),
      (∀ i, Monotone (fun k =>
        ((flowA7_sourcePortRepairStage hd t ht2 ht).exec v) (packets i k))) ∧
      (∀ i i', i ≠ i' → ∀ x y, packets i x ≠ packets i' y) ∧
      Finset.univ.biUnion (fun i => packetEmbeddingSupport (packets i)) =
        wireSets (flowSizes7 d hd) (t + 1) b ∧
      m = flowA7 d hd b.l (t + 1) / 64 := by
  obtain ⟨receiver, hreceiver⟩ := flowA7_receiver_allCases_canonical
    hd t ht2 ht b hb hchild v hpack
  let packets := canonicalPacketEmbedding receiver hreceiver.2.2.2
  have hmul := canonicalPacketFamily_count_mul_64 receiver
    (wireSets (flowSizes7 d hd) (t + 1) b)
    ((flowA7_sourcePortRepairStage hd t ht2 ht).exec v) hreceiver
  have hcard : receiver.count * 64 = flowA7 d hd b.l (t + 1) := by
    rw [wireSets_card (flowSizes7 d hd) (by omega) b] at hmul
    simpa [flowSizes7] using hmul
  refine ⟨receiver.count, packets, ?_, ?_, ?_, ?_⟩
  · exact (canonicalPacketFamily_toEmbeddings receiver
      (wireSets (flowSizes7 d hd) (t + 1) b)
      ((flowA7_sourcePortRepairStage hd t ht2 ht).exec v) hreceiver).1
  · exact (canonicalPacketFamily_toEmbeddings receiver
      (wireSets (flowSizes7 d hd) (t + 1) b)
      ((flowA7_sourcePortRepairStage hd t ht2 ht).exec v) hreceiver).2.1
  · exact (canonicalPacketFamily_toEmbeddings receiver
      (wireSets (flowSizes7 d hd) (t + 1) b)
      ((flowA7_sourcePortRepairStage hd t ht2 ht).exec v) hreceiver).2.2
  · omega

/-- When a scheduled receiver has a packet count divisible by 64, its actual
output family decomposes into disjoint full blocks that can all be merged in
57 layers. -/
theorem flowA7_receiver_allCases_divisible64_batch {d : Nat} {α : Type}
    [LinearOrder α]
    (hd : 7 ≤ d) (t : Nat) (ht2 : 2 ≤ t) (ht : t < tf7 d)
    (b : KBag 64 d) (hb : 1 ≤ b.l) (hchild : b.l < d)
    (v : Fin (64 ^ d) → α)
    (hpack : ∀ q : KBag 64 d,
      PacketSortedOn (wireSets (flowSizes7 d hd) t q) v)
    (hdiv : 64 ∣ flowA7 d hd b.l (t + 1) / 64) :
    ∃ blocks : List (Fin 4096 ↪ Fin (64 ^ d)),
      blocks.Nodup ∧
      (∀ e ∈ blocks, ∀ f ∈ blocks, e ≠ f → ∀ x y, e x ≠ f y) ∧
      (genScatterMergeTreeBatch (packetPowerTree6 (α := α)) blocks).depth ≤ 57 ∧
      (∀ e ∈ blocks, Monotone (fun i =>
        (genScatterMergeTreeBatch (packetPowerTree6 (α := α)) blocks).exec
          ((flowA7_sourcePortRepairStage hd t ht2 ht).exec v) (e i))) ∧
      (∀ e ∈ blocks, ∀ j : Fin (packetPowerTree6 (α := α)).leafCount,
        Monotone (fun i =>
          (genScatterMergeTreeBatch (packetPowerTree6 (α := α)) blocks).exec
            ((flowA7_sourcePortRepairStage hd t ht2 ht).exec v)
            (genScatterMergeTreeOutputEmbedding (packetPowerTree6 (α := α)) e j i))) := by
  obtain ⟨m, packets, hsorted, hdis, hcover, hcount⟩ :=
    flowA7_receiver_allCases_packetCount hd t ht2 ht b hb hchild v hpack
  have hdivM : 64 ∣ m := by
    simpa [hcount] using hdiv
  obtain ⟨blocks, hnodup, hblocksDisjoint, hdepth, hblockSorted, hsortedOut⟩ :=
    packetFamily_divisible64_merge packets hdivM hdis
      ((flowA7_sourcePortRepairStage hd t ht2 ht).exec v) hsorted
  exact ⟨blocks, hnodup, hblocksDisjoint, hdepth, hblockSorted, hsortedOut⟩

/-- The residue-63 receiver case reindexes its canonical packet family into
the `64*q+63` form and applies the proved mixed full-block/tail merge. -/
theorem flowA7_receiver_allCases_residue63_batch {d : Nat} {α : Type}
    [LinearOrder α]
    (hd : 7 ≤ d) (t : Nat) (ht2 : 2 ≤ t) (ht : t < tf7 d)
    (b : KBag 64 d) (hb : 1 ≤ b.l) (hchild : b.l < d)
    (v : Fin (64 ^ d) → α)
    (hpack : ∀ q : KBag 64 d,
      PacketSortedOn (wireSets (flowSizes7 d hd) t q) v)
    (hrem : (flowA7 d hd b.l (t + 1) / 64) % 64 = 63) :
    ∃ blocks : List (Fin 4096 ↪ Fin (64 ^ d)), ∃ tail : Fin 4032 ↪ Fin (64 ^ d),
      blocks.Nodup ∧
      (∀ e ∈ blocks, ∀ f ∈ blocks, e ≠ f → ∀ x y, e x ≠ f y) ∧
      (∀ e ∈ blocks, ∀ i j, e i ≠ tail j) ∧
      (genMergeTreeFullTailBatch (packetPowerTree6 (α := α))
        (packetOddTree6 (α := α)) blocks tail).depth ≤ 57 ∧
      (∀ e ∈ blocks,
        (packetPowerTree6 (α := α)).RunsSorted
          (fun i => ((flowA7_sourcePortRepairStage hd t ht2 ht).exec v) (e i))) ∧
      (packetOddTree6 (α := α)).RunsSorted
        (fun i => ((flowA7_sourcePortRepairStage hd t ht2 ht).exec v) (tail i)) ∧
      (∀ e ∈ blocks, ∀ j : Fin (packetPowerTree6 (α := α)).leafCount,
        Monotone (fun i =>
          (genMergeTreeFullTailBatch (packetPowerTree6 (α := α))
            (packetOddTree6 (α := α)) blocks tail).exec
            ((flowA7_sourcePortRepairStage hd t ht2 ht).exec v)
            (genScatterMergeTreeOutputEmbedding (packetPowerTree6 (α := α)) e j i))) ∧
      (∀ j : Fin (packetOddTree6 (α := α)).leafCount,
        Monotone (fun i =>
          (genMergeTreeFullTailBatch (packetPowerTree6 (α := α))
            (packetOddTree6 (α := α)) blocks tail).exec
            ((flowA7_sourcePortRepairStage hd t ht2 ht).exec v)
            (genScatterMergeTreeOutputEmbedding (packetOddTree6 (α := α)) tail j i))) := by
  obtain ⟨m, packets, hsorted, hdis, hcover, hcount⟩ :=
    flowA7_receiver_allCases_packetCount hd t ht2 ht b hb hchild v hpack
  have hmrem : m % 64 = 63 := by simpa [hcount] using hrem
  let q := m / 64
  have hsize : m = q * 64 + 63 := by
    have hdecomp := Nat.mod_add_div m 64
    dsimp [q]
    rw [hmrem] at hdecomp
    omega
  let packets' : Fin (q * 64 + 63) → Fin 64 ↪ Fin (64 ^ d) :=
    fun i => packets (Fin.cast hsize.symm i)
  have hdis' : ∀ a b, a ≠ b → ∀ x y, packets' a x ≠ packets' b y := by
    intro a b hab x y heq
    apply hdis (Fin.cast hsize.symm a) (Fin.cast hsize.symm b)
    · intro h
      apply hab
      exact Fin.cast_injective hsize.symm h
    · exact heq
  obtain ⟨blocks, tail, hnodup, hblocksDisjoint, htailDisjoint,
      hdepth, hRunsFull, hRunsTail, hsortedFull, hsortedTail⟩ := packetFamily_residue63_merge
    packets' hdis' ((flowA7_sourcePortRepairStage hd t ht2 ht).exec v)
    (fun a => hsorted (Fin.cast hsize.symm a))
  exact ⟨blocks, tail, hnodup, hblocksDisjoint, htailDisjoint,
    hdepth, hRunsFull, hRunsTail, hsortedFull, hsortedTail⟩

/-- At every nonterminal receiver stage, the actual output packet family is
immediately in one of the existing 64-block/tail configurations. -/
theorem flowA7_receiver_allCases_packetCount_block_shape
    (d : Nat) (hd : 7 ≤ d) (t : Nat) (ht2 : 2 ≤ t)
    (ht : t < tf7 d) (htnext : t + 1 < tf7 d) (i : Nat)
    (m : Nat) (hmEq : m = flowA7 d hd i (t + 1) / 64) :
    m = 0 ∨ m = 1 ∨ 64 ∣ m ∨ (m % 64 = 63 ∧ 4095 ≤ m) := by
  rw [hmEq]
  exact flowA7_packet_count_block_shape d hd (t + 1) i (by omega) htnext

/-- At the terminal time, every scheduled bag is empty or has a packet count
divisible by 64, so no exceptional tail remains to schedule. -/
theorem flowA7_terminal_packet_count_shape (d : Nat) (hd : 7 ≤ d) (i : Nat) :
    flowA7 d hd i (tf7 d) / 64 = 0 ∨
      64 ∣ flowA7 d hd i (tf7 d) / 64 := by
  by_cases hi : i = d - 6
  · right
    rw [flowA7_tf d hd i, if_pos hi]
    rw [show (64 : Nat) ^ 6 = 64 * 64 ^ 5 by norm_num]
    simp
  · left
    rw [flowA7_tf d hd i, if_neg hi]

/-- Convert the output list of an indexed merge-and-deal round to a canonical
`Fin`-indexed embedding family. If the matching covers every input ID, this
preserves the full support union and logical sortedness. -/
theorem genIndexedPacketRound_canonicalOutput {m N : Nat} {α : Type}
    [LinearOrder α]
    (packets : Fin m → Fin 64 ↪ Fin N)
    (hpacketDisjoint : ∀ i j, i ≠ j → ∀ x y, packets i x ≠ packets j y)
    (edges : List (Fin m × Fin m)) (hedges : edges.Nodup)
    (hnoFixed : ∀ e ∈ edges, e.1 ≠ e.2)
    (hvertexDisjoint : ∀ e ∈ edges, ∀ f ∈ edges, e ≠ f →
      e.1 ≠ f.1 ∧ e.1 ≠ f.2 ∧ e.2 ≠ f.1 ∧ e.2 ≠ f.2)
    (hcover : ∀ i, ∃ e ∈ edges, e.1 = i ∨ e.2 = i)
    (v : Fin N → α)
    (hsorted : ∀ i, Monotone (fun k : Fin 64 => v (packets i k))) :
    let round := genIndexedPacketRound packets hpacketDisjoint edges hnoFixed
    let output := genIndexedPacketRoundOutput packets hpacketDisjoint edges hnoFixed
    ∃ nextCount : Nat, ∃ next : Fin nextCount → Fin 64 ↪ Fin N,
      (∀ i, Monotone (fun k => round.exec v (next i k))) ∧
      (∀ i i', i ≠ i' → ∀ x y, next i x ≠ next i' y) ∧
      Finset.univ.biUnion (fun i => packetEmbeddingSupport (next i)) =
        Finset.univ.biUnion (fun i => packetEmbeddingSupport (packets i)) ∧
      round.depth ≤ 7 := by
  let round := genIndexedPacketRound packets hpacketDisjoint edges hnoFixed
  let output := genIndexedPacketRoundOutput packets hpacketDisjoint edges hnoFixed
  let next : Fin output.length → Fin 64 ↪ Fin N := fun i => output.get i
  have hsortedOut : ∀ i, Monotone (fun k => round.exec v (next i k)) := by
    intro i
    exact genIndexedPacketRound_output_sorted packets hpacketDisjoint edges hedges
      hnoFixed hvertexDisjoint v hsorted (output.get i) (List.get_mem output i)
  have hdisjointOut : ∀ i i', i ≠ i' → ∀ x y, next i x ≠ next i' y := by
    intro i i' hne x y
    have hpair := genIndexedPacketRound_output_disjoint packets hpacketDisjoint
      edges hedges hnoFixed hvertexDisjoint
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact hpair.rel_get_of_lt hlt x y
    · exact (hpair.rel_get_of_lt hgt y x).symm
  have hsupportOut : Finset.univ.biUnion
      (fun i => packetEmbeddingSupport (next i)) =
      Finset.univ.biUnion (fun i => packetEmbeddingSupport (packets i)) := by
    ext w
    have hout : w ∈ Finset.univ.biUnion
        (fun i => packetEmbeddingSupport (next i)) ↔
        ∃ p ∈ output, w ∈ Set.range p := by
      simp only [Finset.mem_biUnion, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨i, hi⟩
        exact ⟨output.get i, List.get_mem output i,
          (packetEmbeddingSupport_mem_iff _ _).mp hi⟩
      · rintro ⟨p, hp, hw⟩
        obtain ⟨i, hi⟩ :=
          (List.exists_mem_iff_get (l := output) (p := fun x => x = p)).mp
            ⟨p, hp, rfl⟩
        refine ⟨i, ?_⟩
        change w ∈ packetEmbeddingSupport (output.get i)
        rw [packetEmbeddingSupport_mem_iff, hi]
        exact hw
    have hin : w ∈ Finset.univ.biUnion
        (fun i => packetEmbeddingSupport (packets i)) ↔
        ∃ i, w ∈ Set.range (packets i) := by
      simp only [Finset.mem_biUnion, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨i, hi⟩
        exact ⟨i, (packetEmbeddingSupport_mem_iff _ _).mp hi⟩
      · rintro ⟨i, hi⟩
        exact ⟨i, (packetEmbeddingSupport_mem_iff _ _).mpr hi⟩
    rw [hout, genIndexedPacketRound_output_support packets hpacketDisjoint
      edges hnoFixed hcover w, hin]
  have hdepth : round.depth ≤ 7 :=
    genIndexedPacketRound_depth_le packets hpacketDisjoint edges hedges hnoFixed
      hvertexDisjoint
  exact ⟨output.length, next, hsortedOut, hdisjointOut, hsupportOut, hdepth⟩

/-- The output packets of a partial matching cover exactly the packets incident
to its edges; this formulation does not assume the matching is perfect. -/
theorem genIndexedPacketRound_output_support_incident {m N : Nat}
    (packets : Fin m → Fin 64 ↪ Fin N)
    (hpacketDisjoint : ∀ i j, i ≠ j → ∀ x y, packets i x ≠ packets j y)
    (edges : List (Fin m × Fin m))
    (hnoFixed : ∀ e ∈ edges, e.1 ≠ e.2) (w : Fin N) :
    (∃ p ∈ genIndexedPacketRoundOutput packets hpacketDisjoint edges hnoFixed,
      w ∈ Set.range p) ↔
    ∃ e ∈ edges, w ∈ Set.range (packets e.1) ∨ w ∈ Set.range (packets e.2) := by
  change (∃ p ∈ genPacketRound_outputPackets
      (genIndexedPairSupports packets hpacketDisjoint edges hnoFixed),
        w ∈ Set.range p) ↔ _
  rw [genPacketRound_outputPackets_support]
  constructor
  · rintro ⟨joined, hj, hw⟩
    simp only [genIndexedPairSupports, List.mem_map, List.mem_attach] at hj
    obtain ⟨edge, hedge, rfl⟩ := hj
    rw [joinPacketEmbedding_range _ _
      (hpacketDisjoint edge.1.1 edge.1.2 (hnoFixed edge.1 edge.2))] at hw
    rcases hw with hw | hw
    · exact ⟨edge.1, edge.2, Or.inl hw⟩
    · exact ⟨edge.1, edge.2, Or.inr hw⟩
  · rintro ⟨e, he, hw | hw⟩
    · let joined := joinPacketEmbedding (packets e.1) (packets e.2)
        (hpacketDisjoint e.1 e.2 (hnoFixed e he))
      have hj : joined ∈ genIndexedPairSupports packets hpacketDisjoint edges hnoFixed := by
        simp only [genIndexedPairSupports, List.mem_map, List.mem_attach]
        exact ⟨⟨e, he⟩, trivial, rfl⟩
      have hrange : w ∈ Set.range joined := by
        rw [joinPacketEmbedding_range _ _
          (hpacketDisjoint e.1 e.2 (hnoFixed e he))]
        exact Or.inl hw
      exact ⟨joined, hj, hrange⟩
    · let joined := joinPacketEmbedding (packets e.1) (packets e.2)
        (hpacketDisjoint e.1 e.2 (hnoFixed e he))
      have hj : joined ∈ genIndexedPairSupports packets hpacketDisjoint edges hnoFixed := by
        simp only [genIndexedPairSupports, List.mem_map, List.mem_attach]
        exact ⟨⟨e, he⟩, trivial, rfl⟩
      have hrange : w ∈ Set.range joined := by
        rw [joinPacketEmbedding_range _ _
          (hpacketDisjoint e.1 e.2 (hnoFixed e he))]
        exact Or.inr hw
      exact ⟨joined, hj, hrange⟩

/-- A packet not incident to an edge of a vertex-disjoint matching is left
pointwise unchanged by the indexed merge-and-deal round. This is the local
adapter needed to retain unmatched vertices as singleton packets. -/
theorem genIndexedPacketRound_unmatched_unchanged {m N : Nat} {α : Type}
    [LinearOrder α]
    (packets : Fin m → Fin 64 ↪ Fin N)
    (hpacketDisjoint : ∀ i j, i ≠ j → ∀ x y, packets i x ≠ packets j y)
    (edges : List (Fin m × Fin m)) (hedges : edges.Nodup)
    (hnoFixed : ∀ e ∈ edges, e.1 ≠ e.2)
    (hvertexDisjoint : ∀ e ∈ edges, ∀ f ∈ edges, e ≠ f →
      e.1 ≠ f.1 ∧ e.1 ≠ f.2 ∧ e.2 ≠ f.1 ∧ e.2 ≠ f.2)
    (i : Fin m)
    (hfree : ∀ e ∈ edges, e.1 ≠ i ∧ e.2 ≠ i)
    (v : Fin N → α) (k : Fin 64) :
    (genIndexedPacketRound packets hpacketDisjoint edges hnoFixed).exec v
      (packets i k) = v (packets i k) := by
  let supports := genIndexedPairSupports packets hpacketDisjoint edges hnoFixed
  have hsupportsNodup : supports.Nodup :=
    genIndexedPairSupports_nodup packets hpacketDisjoint edges hedges hnoFixed
      hvertexDisjoint
  have hsupportsDisjoint : ∀ e ∈ supports, ∀ f ∈ supports, e ≠ f →
      ∀ x y, e x ≠ f y :=
    genIndexedPairSupports_disjoint packets hpacketDisjoint edges hnoFixed
      hvertexDisjoint
  have houtside : ∀ e ∈ supports, packets i k ∉ Set.range e := by
    intro e he
    simp only [supports, genIndexedPairSupports, List.mem_map,
      List.mem_attach] at he
    obtain ⟨edge, hedge, rfl⟩ := he
    have hleft : i ≠ edge.1.1 := (hfree edge.1 edge.2).1.symm
    have hright : i ≠ edge.1.2 := (hfree edge.1 edge.2).2.symm
    have hwithin := hpacketDisjoint edge.1.1 edge.1.2
      (hnoFixed edge.1 edge.2)
    rw [joinPacketEmbedding_range _ _ hwithin]
    simp only [Set.mem_union, Set.mem_range]
    intro hx
    rcases hx with hx | hx
    · obtain ⟨x, hx⟩ := hx
      exact hpacketDisjoint i edge.1.1 hleft k x (by simpa using hx.symm)
    · obtain ⟨x, hx⟩ := hx
      exact hpacketDisjoint i edge.1.2 hright k x (by simpa using hx.symm)
  change (genPacketRound supports).exec v (packets i k) = _
  exact genPacketRound_exec_outside supports hsupportsNodup hsupportsDisjoint
    (packets i k) houtside v

/-- Combine the dealt outputs of a partial matching with its untouched
singleton packets. -/
def genIndexedPacketRoundOutputWithSingletons {m N : Nat}
    (packets : Fin m → Fin 64 ↪ Fin N)
    (hpacketDisjoint : ∀ i j, i ≠ j → ∀ x y, packets i x ≠ packets j y)
    (edges : List (Fin m × Fin m))
    (hnoFixed : ∀ e ∈ edges, e.1 ≠ e.2)
    (singles : List (Fin m)) : List (Fin 64 ↪ Fin N) :=
  genIndexedPacketRoundOutput packets hpacketDisjoint edges hnoFixed ++
    singles.map packets

/-- A partial matching preserves increasing physical packet embeddings when
each matched pair is ordered and each untouched singleton is increasing. -/
theorem genIndexedPacketRound_withSingletons_output_strictMono {m N : Nat}
    (packets : Fin m → Fin 64 ↪ Fin N)
    (hpacketDisjoint : ∀ i j, i ≠ j → ∀ x y, packets i x ≠ packets j y)
    (edges : List (Fin m × Fin m))
    (hnoFixed : ∀ e ∈ edges, e.1 ≠ e.2)
    (singles : List (Fin m))
    (hpacketMono : ∀ i, StrictMono (packets i))
    (hordered : ∀ e ∈ edges, ∀ x y, packets e.1 x < packets e.2 y) :
    ∀ p ∈ genIndexedPacketRoundOutputWithSingletons packets hpacketDisjoint
      edges hnoFixed singles,
      StrictMono p := by
  intro p hp
  simp only [genIndexedPacketRoundOutputWithSingletons, List.mem_append] at hp
  rcases hp with hmatched | hsingle
  · exact genIndexedPacketRound_output_strictMono packets hpacketDisjoint edges
      hnoFixed hpacketMono hordered p hmatched
  · simp only [List.mem_map] at hsingle
    obtain ⟨i, hi, rfl⟩ := hsingle
    exact hpacketMono i

/-- A partial matching together with a pairwise-disjoint list of untouched
singletons gives a sorted, pairwise-disjoint packet family covering precisely
the input packet support, provided every input ID is either matched or listed
as a singleton. -/
theorem genIndexedPacketRound_withSingletons_contract {m N : Nat} {α : Type}
    [LinearOrder α]
    (packets : Fin m → Fin 64 ↪ Fin N)
    (hpacketDisjoint : ∀ i j, i ≠ j → ∀ x y, packets i x ≠ packets j y)
    (edges : List (Fin m × Fin m)) (hedges : edges.Nodup)
    (hnoFixed : ∀ e ∈ edges, e.1 ≠ e.2)
    (hvertexDisjoint : ∀ e ∈ edges, ∀ f ∈ edges, e ≠ f →
      e.1 ≠ f.1 ∧ e.1 ≠ f.2 ∧ e.2 ≠ f.1 ∧ e.2 ≠ f.2)
    (singles : List (Fin m))
    (hsingleDisjoint : List.Pairwise
      (fun i j => ∀ x y, packets i x ≠ packets j y) singles)
    (hfree : ∀ i ∈ singles, ∀ e ∈ edges, e.1 ≠ i ∧ e.2 ≠ i)
    (hcover : ∀ i, (∃ e ∈ edges, e.1 = i ∨ e.2 = i) ∨ i ∈ singles)
    (v : Fin N → α)
    (hsorted : ∀ i, Monotone (fun k => v (packets i k))) :
    (∀ p ∈ genIndexedPacketRoundOutputWithSingletons packets hpacketDisjoint
        edges hnoFixed singles,
      Monotone (fun k =>
        (genIndexedPacketRound packets hpacketDisjoint edges hnoFixed).exec v
          (p k))) ∧
    List.Pairwise (fun p q : Fin 64 ↪ Fin N => ∀ x y, p x ≠ q y)
      (genIndexedPacketRoundOutputWithSingletons packets hpacketDisjoint
        edges hnoFixed singles) ∧
    (∀ w, (∃ p ∈ genIndexedPacketRoundOutputWithSingletons packets
        hpacketDisjoint edges hnoFixed singles, w ∈ Set.range p) ↔
      ∃ i, w ∈ Set.range (packets i)) := by
  let output := genIndexedPacketRoundOutput packets hpacketDisjoint edges hnoFixed
  let family := genIndexedPacketRoundOutputWithSingletons packets hpacketDisjoint
    edges hnoFixed singles
  have hsortedMatched : ∀ p ∈ output,
      Monotone (fun k =>
        (genIndexedPacketRound packets hpacketDisjoint edges hnoFixed).exec v
          (p k)) := by
    intro p hp
    exact genIndexedPacketRound_output_sorted packets hpacketDisjoint edges hedges
      hnoFixed hvertexDisjoint v hsorted p hp
  have hsortedFamily : ∀ p ∈ family,
      Monotone (fun k =>
        (genIndexedPacketRound packets hpacketDisjoint edges hnoFixed).exec v
          (p k)) := by
    intro p hp
    simp only [family, genIndexedPacketRoundOutputWithSingletons,
      List.mem_append] at hp
    rcases hp with hp | hp
    · exact hsortedMatched p hp
    · simp only [List.mem_map] at hp
      obtain ⟨i, hi, rfl⟩ := hp
      intro a b hab
      change (genIndexedPacketRound packets hpacketDisjoint edges hnoFixed).exec v
          (packets i a) ≤
        (genIndexedPacketRound packets hpacketDisjoint edges hnoFixed).exec v
          (packets i b)
      rw [genIndexedPacketRound_unmatched_unchanged packets hpacketDisjoint edges
        hedges hnoFixed hvertexDisjoint i (fun e he => hfree i hi e he) v a,
        genIndexedPacketRound_unmatched_unchanged packets hpacketDisjoint edges
        hedges hnoFixed hvertexDisjoint i (fun e he => hfree i hi e he) v b]
      exact hsorted i hab
  have hmatchedDisjoint : List.Pairwise
      (fun p q : Fin 64 ↪ Fin N => ∀ x y, p x ≠ q y) output := by
    exact genIndexedPacketRound_output_disjoint packets hpacketDisjoint edges hedges
      hnoFixed hvertexDisjoint
  have hsingleOutputDisjoint : List.Pairwise
      (fun p q : Fin 64 ↪ Fin N => ∀ x y, p x ≠ q y) (singles.map packets) := by
    rw [List.pairwise_map]
    exact hsingleDisjoint
  have hcross : ∀ p ∈ output, ∀ q ∈ singles.map packets,
      ∀ x y, p x ≠ q y := by
    intro p hp q hq x y heq
    simp only [List.mem_map] at hq
    obtain ⟨i, hi, rfl⟩ := hq
    have hincident :=
      (genIndexedPacketRound_output_support_incident packets hpacketDisjoint
        edges hnoFixed (p x)).1 ⟨p, hp, ⟨x, rfl⟩⟩
    rcases hincident with ⟨e, he, hleft | hright⟩
    · obtain ⟨j, hj⟩ := hleft
      exact hpacketDisjoint e.1 i (hfree i hi e he).1 j y (hj.trans heq)
    · obtain ⟨j, hj⟩ := hright
      exact hpacketDisjoint e.2 i (hfree i hi e he).2 j y (hj.trans heq)
  have hfamilyDisjoint : List.Pairwise
      (fun p q : Fin 64 ↪ Fin N => ∀ x y, p x ≠ q y) family := by
    change List.Pairwise (fun p q : Fin 64 ↪ Fin N => ∀ x y, p x ≠ q y)
      (output ++ singles.map packets)
    rw [List.pairwise_append]
    exact ⟨hmatchedDisjoint, hsingleOutputDisjoint, hcross⟩
  have hfamilySupport : ∀ w,
      (∃ p ∈ family, w ∈ Set.range p) ↔ ∃ i, w ∈ Set.range (packets i) := by
    intro w
    simp only [family, genIndexedPacketRoundOutputWithSingletons,
      List.mem_append]
    constructor
    · rintro ⟨p, hp | hp, hw⟩
      · obtain ⟨e, he, hside⟩ :=
          (genIndexedPacketRound_output_support_incident packets hpacketDisjoint
            edges hnoFixed w).1 ⟨p, hp, hw⟩
        rcases hside with hleft | hright
        · exact ⟨e.1, hleft⟩
        · exact ⟨e.2, hright⟩
      · simp only [List.mem_map] at hp
        obtain ⟨i, hi, rfl⟩ := hp
        exact ⟨i, hw⟩
    · rintro ⟨i, hi⟩
      rcases hcover i with hincident | hsingle
      · have hout :=
          (genIndexedPacketRound_output_support_incident packets hpacketDisjoint
            edges hnoFixed w).2 (by
              obtain ⟨e, he, hside⟩ := hincident
              exact ⟨e, he, hside.elim (fun h => Or.inl (h ▸ hi))
                (fun h => Or.inr (h ▸ hi))⟩)
        rcases hout with ⟨p, hp, hw⟩
        exact ⟨p, Or.inl hp, hw⟩
      · refine ⟨packets i, Or.inr ?_, hi⟩
        simp only [List.mem_map]
        exact ⟨i, hsingle, rfl⟩
  exact ⟨hsortedFamily, hfamilyDisjoint, hfamilySupport⟩

/-- Canonicalize the full output family of a partial matching round, including
unmatched singletons. This makes a partial matching round composable with the
next indexed round without losing packet coverage. -/
theorem genIndexedPacketRound_withSingletons_canonicalOutput {m N : Nat}
    {α : Type} [LinearOrder α]
    (packets : Fin m → Fin 64 ↪ Fin N)
    (hpacketDisjoint : ∀ i j, i ≠ j → ∀ x y, packets i x ≠ packets j y)
    (edges : List (Fin m × Fin m)) (hedges : edges.Nodup)
    (hnoFixed : ∀ e ∈ edges, e.1 ≠ e.2)
    (hvertexDisjoint : ∀ e ∈ edges, ∀ f ∈ edges, e ≠ f →
      e.1 ≠ f.1 ∧ e.1 ≠ f.2 ∧ e.2 ≠ f.1 ∧ e.2 ≠ f.2)
    (singles : List (Fin m))
    (hsingleDisjoint : List.Pairwise
      (fun i j => ∀ x y, packets i x ≠ packets j y) singles)
    (hfree : ∀ i ∈ singles, ∀ e ∈ edges, e.1 ≠ i ∧ e.2 ≠ i)
    (hcover : ∀ i, (∃ e ∈ edges, e.1 = i ∨ e.2 = i) ∨ i ∈ singles)
    (v : Fin N → α)
    (hsorted : ∀ i, Monotone (fun k => v (packets i k))) :
    ∃ nextCount : Nat, ∃ next : Fin nextCount → Fin 64 ↪ Fin N,
      (∀ i, Monotone (fun k =>
        (genIndexedPacketRound packets hpacketDisjoint edges hnoFixed).exec v
          (next i k))) ∧
      (∀ i i', i ≠ i' → ∀ x y, next i x ≠ next i' y) ∧
      Finset.univ.biUnion (fun i => packetEmbeddingSupport (next i)) =
        Finset.univ.biUnion (fun i => packetEmbeddingSupport (packets i)) ∧
      (genIndexedPacketRound packets hpacketDisjoint edges hnoFixed).depth ≤ 7 := by
  let output := genIndexedPacketRoundOutputWithSingletons packets hpacketDisjoint
    edges hnoFixed singles
  have hcontract := genIndexedPacketRound_withSingletons_contract packets
    hpacketDisjoint edges hedges hnoFixed hvertexDisjoint singles hsingleDisjoint
    hfree hcover v hsorted
  let next : Fin output.length → Fin 64 ↪ Fin N := fun i => output.get i
  have hsortedOut : ∀ i, Monotone (fun k =>
      (genIndexedPacketRound packets hpacketDisjoint edges hnoFixed).exec v
        (next i k)) := by
    intro i
    exact hcontract.1 (output.get i) (List.get_mem output i)
  have hdisjointOut : ∀ i i', i ≠ i' → ∀ x y, next i x ≠ next i' y := by
    intro i i' hne x y
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact hcontract.2.1.rel_get_of_lt hlt x y
    · exact (hcontract.2.1.rel_get_of_lt hgt y x).symm
  have hsupportOut : Finset.univ.biUnion
      (fun i => packetEmbeddingSupport (next i)) =
      Finset.univ.biUnion (fun i => packetEmbeddingSupport (packets i)) := by
    ext w
    have hout : w ∈ Finset.univ.biUnion
        (fun i => packetEmbeddingSupport (next i)) ↔
        ∃ p ∈ output, w ∈ Set.range p := by
      simp only [Finset.mem_biUnion, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨i, hi⟩
        exact ⟨output.get i, List.get_mem output i,
          (packetEmbeddingSupport_mem_iff _ _).mp hi⟩
      · rintro ⟨p, hp, hw⟩
        obtain ⟨i, hi⟩ :=
          (List.exists_mem_iff_get (l := output) (p := fun x => x = p)).mp
            ⟨p, hp, rfl⟩
        refine ⟨i, ?_⟩
        change w ∈ packetEmbeddingSupport (output.get i)
        rw [packetEmbeddingSupport_mem_iff, hi]
        exact hw
    have hin : w ∈ Finset.univ.biUnion
        (fun i => packetEmbeddingSupport (packets i)) ↔
        ∃ i, w ∈ Set.range (packets i) := by
      simp only [Finset.mem_biUnion, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨i, hi⟩
        exact ⟨i, (packetEmbeddingSupport_mem_iff _ _).mp hi⟩
      · rintro ⟨i, hi⟩
        exact ⟨i, (packetEmbeddingSupport_mem_iff _ _).mpr hi⟩
    rw [hout, hcontract.2.2 w, hin]
  have hdepth :
      (genIndexedPacketRound packets hpacketDisjoint edges hnoFixed).depth ≤ 7 :=
    genIndexedPacketRound_depth_le packets hpacketDisjoint edges hedges hnoFixed
      hvertexDisjoint
  exact ⟨output.length, next, hsortedOut, hdisjointOut, hsupportOut, hdepth⟩

/-- A partial matching round, including untouched singleton packets, can be
reindexed to the same packet-count type. The length premise accounts for both
dealt pairs and singletons, so odd packet counts are supported directly. -/
theorem genIndexedPacketRound_withSingletons_canonicalOutput_fixedCount
    {m N : Nat} {α : Type}
    [LinearOrder α]
    (packets : Fin m → Fin 64 ↪ Fin N)
    (hpacketDisjoint : ∀ i j, i ≠ j → ∀ x y, packets i x ≠ packets j y)
    (edges : List (Fin m × Fin m)) (hedges : edges.Nodup)
    (hnoFixed : ∀ e ∈ edges, e.1 ≠ e.2)
    (hvertexDisjoint : ∀ e ∈ edges, ∀ f ∈ edges, e ≠ f →
      e.1 ≠ f.1 ∧ e.1 ≠ f.2 ∧ e.2 ≠ f.1 ∧ e.2 ≠ f.2)
    (singles : List (Fin m))
    (hsingleDisjoint : List.Pairwise
      (fun i j => ∀ x y, packets i x ≠ packets j y) singles)
    (hfree : ∀ i ∈ singles, ∀ e ∈ edges, e.1 ≠ i ∧ e.2 ≠ i)
    (hcover : ∀ i, (∃ e ∈ edges, e.1 = i ∨ e.2 = i) ∨ i ∈ singles)
    (hlen : 2 * edges.length + singles.length = m)
    (v : Fin N → α)
    (hsorted : ∀ i, Monotone (fun k : Fin 64 => v (packets i k))) :
    let round := genIndexedPacketRound packets hpacketDisjoint edges hnoFixed
    ∃ next : Fin m → Fin 64 ↪ Fin N,
      (∀ i, Monotone (fun k => round.exec v (next i k))) ∧
      (∀ i i', i ≠ i' → ∀ x y, next i x ≠ next i' y) ∧
      Finset.univ.biUnion (fun i => packetEmbeddingSupport (next i)) =
        Finset.univ.biUnion (fun i => packetEmbeddingSupport (packets i)) ∧
      round.depth ≤ 7 := by
  let output := genIndexedPacketRoundOutputWithSingletons packets hpacketDisjoint
    edges hnoFixed singles
  have houtputLen : output.length = m := by
    have hmatchedLen :
        (genIndexedPacketRoundOutput packets hpacketDisjoint edges hnoFixed).length =
          2 * edges.length := by
      have hsum : ∀ xs : List {e // e ∈ edges},
          (xs.map fun _ => 2).sum = 2 * xs.length := by
        intro xs
        induction xs with
        | nil => simp
        | cons e xs ih =>
            simp only [List.map_cons, List.sum_cons, List.length_cons]
            rw [ih]
            omega
      simpa [genIndexedPacketRoundOutput, genPacketRound_outputPackets,
        genIndexedPairSupports, List.length_flatMap, Function.comp_def] using
        hsum edges.attach
    simp [output, genIndexedPacketRoundOutputWithSingletons,
      List.length_append, List.length_map, hmatchedLen]
    omega
  have hcontract := genIndexedPacketRound_withSingletons_contract
    packets hpacketDisjoint edges hedges hnoFixed hvertexDisjoint singles
    hsingleDisjoint hfree hcover v hsorted
  have hsortedList : ∀ p ∈ output,
      Monotone (fun k => (genIndexedPacketRound packets hpacketDisjoint
        edges hnoFixed).exec v (p k)) := by
    simpa [output, genIndexedPacketRoundOutputWithSingletons] using hcontract.1
  have hdisjointList : List.Pairwise
      (fun p p' : Fin 64 ↪ Fin N => ∀ x y, p x ≠ p' y) output := by
    simpa [output, genIndexedPacketRoundOutputWithSingletons] using hcontract.2.1
  have hsupportList : ∀ w,
      (∃ p ∈ output, w ∈ Set.range p) ↔
        ∃ i, w ∈ Set.range (packets i) := by
    intro w
    simpa [output, genIndexedPacketRoundOutputWithSingletons] using hcontract.2.2 w
  let next : Fin m → Fin 64 ↪ Fin N := fun i =>
    output.get (Fin.cast houtputLen.symm i)
  have hsortedNext : ∀ i, Monotone (fun k =>
      (genIndexedPacketRound packets hpacketDisjoint edges hnoFixed).exec v
        (next i k)) := by
    intro i
    exact hsortedList _ (List.get_mem output (Fin.cast houtputLen.symm i))
  have hdisjointNext : ∀ i i', i ≠ i' → ∀ x y, next i x ≠ next i' y := by
    intro i i' hii' x y
    have hne : Fin.cast houtputLen.symm i ≠ Fin.cast houtputLen.symm i' := by
      intro h
      apply hii'
      apply Fin.ext
      have hv := congrArg Fin.val h
      simpa using hv
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact hdisjointList.rel_get_of_lt hlt x y
    · exact (hdisjointList.rel_get_of_lt hgt y x).symm
  have hsupportNext : Finset.univ.biUnion
      (fun i => packetEmbeddingSupport (next i)) =
      Finset.univ.biUnion (fun i => packetEmbeddingSupport (packets i)) := by
    ext w
    have hout : w ∈ Finset.univ.biUnion
        (fun i => packetEmbeddingSupport (next i)) ↔
        ∃ p ∈ output, w ∈ Set.range p := by
      simp only [Finset.mem_biUnion, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨i, hi⟩
        exact ⟨output.get (Fin.cast houtputLen.symm i),
          List.get_mem output (Fin.cast houtputLen.symm i),
          (packetEmbeddingSupport_mem_iff _ _).mp hi⟩
      · rintro ⟨p, hp, hw⟩
        obtain ⟨i, hi⟩ :=
          (List.exists_mem_iff_get (l := output) (p := fun z => z = p)).mp
            ⟨p, hp, rfl⟩
        refine ⟨Fin.cast houtputLen i, ?_⟩
        change w ∈ packetEmbeddingSupport (output.get (Fin.cast houtputLen.symm
          (Fin.cast houtputLen i)))
        rw [Fin.cast_trans, Fin.cast_eq_self, hi]
        exact (packetEmbeddingSupport_mem_iff _ _).mpr hw
    have hin : w ∈ Finset.univ.biUnion
        (fun i => packetEmbeddingSupport (packets i)) ↔
        ∃ i, w ∈ Set.range (packets i) := by
      simp only [Finset.mem_biUnion, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨i, hi⟩
        exact ⟨i, (packetEmbeddingSupport_mem_iff _ _).mp hi⟩
      · rintro ⟨i, hi⟩
        exact ⟨i, (packetEmbeddingSupport_mem_iff _ _).mpr hi⟩
    rw [hout, hsupportList w, hin]
  have hdepth : (genIndexedPacketRound packets hpacketDisjoint
      edges hnoFixed).depth ≤ 7 :=
    genIndexedPacketRound_depth_le packets hpacketDisjoint edges hedges
      hnoFixed hvertexDisjoint
  exact ⟨next, hsortedNext, hdisjointNext, hsupportNext, hdepth⟩

/-- Two perfect matching rounds compose at the logical packet layer. The
second matching acts on the fixed-count output of the first, while exact
support coverage and the seven-layer bound are retained at both steps. -/
theorem genIndexedPacketRound_canonicalOutput_fixedCount {m N : Nat} {α : Type}
    [LinearOrder α]
    (packets : Fin m → Fin 64 ↪ Fin N)
    (hpacketDisjoint : ∀ i j, i ≠ j → ∀ x y, packets i x ≠ packets j y)
    (edges : List (Fin m × Fin m)) (hedges : edges.Nodup)
    (hnoFixed : ∀ e ∈ edges, e.1 ≠ e.2)
    (hvertexDisjoint : ∀ e ∈ edges, ∀ f ∈ edges, e ≠ f →
      e.1 ≠ f.1 ∧ e.1 ≠ f.2 ∧ e.2 ≠ f.1 ∧ e.2 ≠ f.2)
    (hcover : ∀ i, ∃ e ∈ edges, e.1 = i ∨ e.2 = i)
    (hlen : 2 * edges.length = m)
    (v : Fin N → α)
    (hsorted : ∀ i, Monotone (fun k : Fin 64 => v (packets i k))) :
    let round := genIndexedPacketRound packets hpacketDisjoint edges hnoFixed
    ∃ next : Fin m → Fin 64 ↪ Fin N,
      (∀ i, Monotone (fun k => round.exec v (next i k))) ∧
      (∀ i i', i ≠ i' → ∀ x y, next i x ≠ next i' y) ∧
      Finset.univ.biUnion (fun i => packetEmbeddingSupport (next i)) =
        Finset.univ.biUnion (fun i => packetEmbeddingSupport (packets i)) ∧
      round.depth ≤ 7 := by
  simpa [genIndexedPacketRoundOutputWithSingletons] using
    (genIndexedPacketRound_withSingletons_canonicalOutput_fixedCount
      packets hpacketDisjoint edges hedges hnoFixed hvertexDisjoint
      ([] : List (Fin m)) (by simp) (by simp)
      (fun i => Or.inl (hcover i)) (by simpa using hlen) v hsorted)

theorem genIndexedPacketRounds_twoStep {m N : Nat} {α : Type}
    [LinearOrder α]
    (packets : Fin m → Fin 64 ↪ Fin N)
    (hpacketDisjoint : ∀ i j, i ≠ j → ∀ x y, packets i x ≠ packets j y)
    (edges₁ edges₂ : List (Fin m × Fin m))
    (hedges₁ : edges₁.Nodup) (hedges₂ : edges₂.Nodup)
    (hnoFixed₁ : ∀ e ∈ edges₁, e.1 ≠ e.2)
    (hnoFixed₂ : ∀ e ∈ edges₂, e.1 ≠ e.2)
    (hvertexDisjoint₁ : ∀ e ∈ edges₁, ∀ f ∈ edges₁, e ≠ f →
      e.1 ≠ f.1 ∧ e.1 ≠ f.2 ∧ e.2 ≠ f.1 ∧ e.2 ≠ f.2)
    (hvertexDisjoint₂ : ∀ e ∈ edges₂, ∀ f ∈ edges₂, e ≠ f →
      e.1 ≠ f.1 ∧ e.1 ≠ f.2 ∧ e.2 ≠ f.1 ∧ e.2 ≠ f.2)
    (hcover₁ : ∀ i, ∃ e ∈ edges₁, e.1 = i ∨ e.2 = i)
    (hcover₂ : ∀ i, ∃ e ∈ edges₂, e.1 = i ∨ e.2 = i)
    (hlen₁ : 2 * edges₁.length = m) (hlen₂ : 2 * edges₂.length = m)
    (v : Fin N → α)
    (hsorted : ∀ i, Monotone (fun k : Fin 64 => v (packets i k))) :
    ∃ next₁ : Fin m → Fin 64 ↪ Fin N,
    ∃ hnext₁ : ∀ i j, i ≠ j → ∀ x y, next₁ i x ≠ next₁ j y,
    ∃ next₂ : Fin m → Fin 64 ↪ Fin N,
      (∀ i, Monotone (fun k =>
        (genIndexedPacketRound next₁ hnext₁ edges₂ hnoFixed₂).exec
          ((genIndexedPacketRound packets hpacketDisjoint edges₁ hnoFixed₁).exec v)
          (next₂ i k))) ∧
      (∀ i j, i ≠ j → ∀ x y, next₂ i x ≠ next₂ j y) ∧
      Finset.univ.biUnion (fun i => packetEmbeddingSupport (next₂ i)) =
        Finset.univ.biUnion (fun i => packetEmbeddingSupport (packets i)) ∧
      (genIndexedPacketRound packets hpacketDisjoint edges₁ hnoFixed₁).depth ≤ 7 ∧
      (genIndexedPacketRound next₁ hnext₁ edges₂ hnoFixed₂).depth ≤ 7 := by
  obtain ⟨next₁, hsorted₁, hnext₁, hsupp₁, hdepth₁⟩ :=
    genIndexedPacketRound_canonicalOutput_fixedCount packets hpacketDisjoint
      edges₁ hedges₁ hnoFixed₁ hvertexDisjoint₁ hcover₁ hlen₁ v hsorted
  let value₁ := (genIndexedPacketRound packets hpacketDisjoint
    edges₁ hnoFixed₁).exec v
  have hsorted₁' : ∀ i, Monotone (fun k => value₁ (next₁ i k)) := by
    simpa [value₁] using hsorted₁
  obtain ⟨next₂, hsorted₂, hnext₂, hsupp₂, hdepth₂⟩ :=
    genIndexedPacketRound_canonicalOutput_fixedCount next₁ hnext₁
      edges₂ hedges₂ hnoFixed₂ hvertexDisjoint₂ hcover₂ hlen₂ value₁ hsorted₁'
  refine ⟨next₁, hnext₁, next₂, ?_, hnext₂, ?_, hdepth₁, hdepth₂⟩
  · simpa [value₁] using hsorted₂
  · calc
      Finset.univ.biUnion (fun i => packetEmbeddingSupport (next₂ i)) =
          Finset.univ.biUnion (fun i => packetEmbeddingSupport (next₁ i)) := hsupp₂
      _ = Finset.univ.biUnion (fun i => packetEmbeddingSupport (packets i)) := hsupp₁

/-- A perfect matching on the current logical packet IDs, together with the
combinatorial facts needed by one seven-layer round. -/
structure IndexedPacketPerfectMatching (m : Nat) where
  edges : List (Fin m × Fin m)
  nodup : edges.Nodup
  noFixed : ∀ e ∈ edges, e.1 ≠ e.2
  vertexDisjoint : ∀ e ∈ edges, ∀ f ∈ edges, e ≠ f →
    e.1 ≠ f.1 ∧ e.1 ≠ f.2 ∧ e.2 ≠ f.1 ∧ e.2 ≠ f.2
  covers : ∀ i, ∃ e ∈ edges, e.1 = i ∨ e.2 = i
  edgeCount : 2 * edges.length = m

/-- A possibly partial matching plus its untouched packet IDs. This supports
odd packet counts without adding dummy wires. -/
structure IndexedPacketMatching (m : Nat) where
  edges : List (Fin m × Fin m)
  nodup : edges.Nodup
  noFixed : ∀ e ∈ edges, e.1 ≠ e.2
  vertexDisjoint : ∀ e ∈ edges, ∀ f ∈ edges, e ≠ f →
    e.1 ≠ f.1 ∧ e.1 ≠ f.2 ∧ e.2 ≠ f.1 ∧ e.2 ≠ f.2
  singles : List (Fin m)
  singleDisjoint : List.Pairwise (fun i j => i ≠ j) singles
  free : ∀ i ∈ singles, ∀ e ∈ edges, e.1 ≠ i ∧ e.2 ≠ i
  covers : ∀ i, (∃ e ∈ edges, e.1 = i ∨ e.2 = i) ∨ i ∈ singles
  count : 2 * edges.length + singles.length = m

/-- Pair the right lane of each even output block with the left lane of the
following odd block. The two outer lanes in each pair remain singletons. -/
def interBlockBoundaryEdges (r : Nat) :
    List (Fin (2 * (2 * r)) × Fin (2 * (2 * r))) :=
  (List.finRange r).map fun j =>
    (⟨4 * j.val + 1, by omega⟩, ⟨4 * j.val + 2, by omega⟩)

/-- Enumerate the untouched outer lanes in the same block order. -/
def interBlockBoundarySingletons (r : Nat) : List (Fin (2 * (2 * r))) :=
  (List.finRange (2 * r)).map fun i =>
    ⟨2 * i.val + i.val % 2, by have := i.isLt; omega⟩

theorem interBlockBoundaryEdges_nodup (r : Nat) :
    (interBlockBoundaryEdges r).Nodup := by
  unfold interBlockBoundaryEdges
  apply List.Nodup.map_on
  · intro j hj l hl heq
    have hv := congrArg (fun e : Fin (2 * (2 * r)) × Fin (2 * (2 * r)) => e.1.val) heq
    simp at hv
    apply Fin.ext
    omega
  · exact List.nodup_finRange r

theorem interBlockBoundaryEdges_noFixed (r : Nat) :
    ∀ e ∈ interBlockBoundaryEdges r, e.1 ≠ e.2 := by
  intro e he
  simp only [interBlockBoundaryEdges, List.mem_map, List.mem_finRange] at he
  obtain ⟨j, _, rfl⟩ := he
  intro h
  have hv := congrArg Fin.val h
  simp at hv

theorem interBlockBoundaryEdges_vertexDisjoint (r : Nat) :
    ∀ e ∈ interBlockBoundaryEdges r, ∀ f ∈ interBlockBoundaryEdges r,
      e ≠ f → e.1 ≠ f.1 ∧ e.1 ≠ f.2 ∧ e.2 ≠ f.1 ∧ e.2 ≠ f.2 := by
  intro e he f hf hne
  simp only [interBlockBoundaryEdges, List.mem_map, List.mem_finRange] at he hf
  obtain ⟨j, _, rfl⟩ := he
  obtain ⟨l, _, rfl⟩ := hf
  have hjl : j ≠ l := by
    intro h
    apply hne
    subst l
    rfl
  have hjlval : j.val ≠ l.val := by
    intro h
    apply hjl
    exact Fin.ext h
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    intro h <;> have hv := congrArg Fin.val h <;> simp at hv <;> omega

theorem interBlockBoundarySingletons_nodup (r : Nat) :
    (interBlockBoundarySingletons r).Nodup := by
  unfold interBlockBoundarySingletons
  apply List.Nodup.map_on
  · intro i hi j hj heq
    have hv := congrArg Fin.val heq
    have hlt := i.isLt
    have hlt' := j.isLt
    simp at hv
    apply Fin.ext
    omega
  · exact List.nodup_finRange (2 * r)

theorem interBlockBoundarySingletons_disjoint (r : Nat) :
    List.Pairwise (fun i j : Fin (2 * (2 * r)) => i ≠ j)
      (interBlockBoundarySingletons r) :=
  (List.nodup_iff_pairwise_ne).mp (interBlockBoundarySingletons_nodup r)

theorem interBlockBoundarySingletons_free (r : Nat) :
    ∀ i ∈ interBlockBoundarySingletons r, ∀ e ∈ interBlockBoundaryEdges r,
      e.1 ≠ i ∧ e.2 ≠ i := by
  intro i hi e he
  simp only [interBlockBoundarySingletons, List.mem_map, List.mem_finRange] at hi
  obtain ⟨t, _, rfl⟩ := hi
  simp only [interBlockBoundaryEdges, List.mem_map, List.mem_finRange] at he
  obtain ⟨j, _, rfl⟩ := he
  refine ⟨?_, ?_⟩ <;> intro h <;>
    have hv := congrArg Fin.val h <;> simp at hv <;> omega

theorem interBlockBoundaryMatching_covers (r : Nat) (i : Fin (2 * (2 * r))) :
    (∃ e ∈ interBlockBoundaryEdges r, e.1 = i ∨ e.2 = i) ∨
      i ∈ interBlockBoundarySingletons r := by
  have hi := i.isLt
  let j : Fin r := ⟨i.val / 4, by omega⟩
  let t : Fin (2 * r) := ⟨i.val / 2, by omega⟩
  by_cases h0 : i.val % 4 = 0
  · right
    simp only [interBlockBoundarySingletons, List.mem_map, List.mem_finRange]
    refine ⟨t, trivial, ?_⟩
    apply Fin.ext
    dsimp [t]
    have ht : (i.val / 2) % 2 = 0 := by omega
    omega
  · by_cases h1 : i.val % 4 = 1
    · left
      refine ⟨(⟨4 * j.val + 1, by omega⟩, ⟨4 * j.val + 2, by omega⟩), ?_, Or.inl ?_⟩
      · simp [interBlockBoundaryEdges]
      apply Fin.ext
      dsimp [j]
      omega
    · by_cases h2 : i.val % 4 = 2
      · left
        refine ⟨(⟨4 * j.val + 1, by omega⟩, ⟨4 * j.val + 2, by omega⟩), ?_, Or.inr ?_⟩
        · simp [interBlockBoundaryEdges]
        · apply Fin.ext
          dsimp [j]
          omega
      · right
        simp only [interBlockBoundarySingletons, List.mem_map, List.mem_finRange]
        refine ⟨t, trivial, ?_⟩
        apply Fin.ext
        dsimp [t]
        have ht : (i.val / 2) % 2 = 1 := by omega
        omega

theorem interBlockBoundaryMatching_count (r : Nat) :
    2 * (interBlockBoundaryEdges r).length +
      (interBlockBoundarySingletons r).length = 2 * (2 * r) := by
  simp [interBlockBoundaryEdges, interBlockBoundarySingletons]
  omega

/-- Concrete partial matching across the boundaries of ordered two-lane
blocks. Every block pair contributes one edge and its two outer singleton
lanes, so all packet IDs are accounted for exactly once. -/
def interBlockBoundaryMatching (r : Nat) : IndexedPacketMatching (2 * (2 * r)) where
  edges := interBlockBoundaryEdges r
  nodup := interBlockBoundaryEdges_nodup r
  noFixed := interBlockBoundaryEdges_noFixed r
  vertexDisjoint := interBlockBoundaryEdges_vertexDisjoint r
  singles := interBlockBoundarySingletons r
  singleDisjoint := interBlockBoundarySingletons_disjoint r
  free := interBlockBoundarySingletons_free r
  covers := interBlockBoundaryMatching_covers r
  count := interBlockBoundaryMatching_count r

/-- Match the last packet of each four-packet block to the first packet of the
next block. This records the candidate edge schedule; its partition into
singletons and matched vertices is still to be proved. -/
def fourLaneBoundaryEdges (s : Nat) :
    List (Prod (Fin (8 * s)) (Fin (8 * s))) :=
  (List.finRange s).map fun j =>
    (Fin.mk (8 * j.val + 3) (by have := j.isLt; omega),
      Fin.mk (8 * j.val + 4) (by have := j.isLt; omega))

theorem fourLaneBoundaryEdges_nodup (s : Nat) :
    (fourLaneBoundaryEdges s).Nodup := by
  unfold fourLaneBoundaryEdges
  exact List.Nodup.map_on (l := List.finRange s)
    (f := fun j => (Fin.mk (8 * j.val + 3) (by have := j.isLt; omega),
      Fin.mk (8 * j.val + 4) (by have := j.isLt; omega)))
    (fun j hj l hl heq => by
      have hv := congrArg (fun e : Prod (Fin (8 * s)) (Fin (8 * s)) => e.1.val) heq
      simp at hv
      apply Fin.ext
      omega)
    (List.nodup_finRange s)

theorem fourLaneBoundaryEdges_noFixed (s : Nat) :
    forall e, List.Mem e (fourLaneBoundaryEdges s) -> Not (e.1 = e.2) := by
  intro e he
  have heMap := List.mem_map.mp he
  cases heMap with
  | intro j hj =>
    cases hj with
    | intro hj heq =>
      cases e with
      | mk edgeLeft edgeRight =>
        simp only [Prod.mk.injEq] at heq
        cases heq.1
        cases heq.2
        intro h
        have hv := congrArg Fin.val h
        simp at hv
/-- The candidate four-lane boundary edges point from an earlier physical
four-packet block to a later one. -/
theorem fourLaneBoundaryEdges_ordered {s N : Nat}
    (packets : Fin (8 * s) -> Function.Embedding (Fin 64) (Fin N))
    (hblockOrdered : forall i j, i.val / 4 < j.val / 4 -> forall x y,
      packets i x < packets j y) :
    forall e, List.Mem e (fourLaneBoundaryEdges s) -> forall x y,
      packets e.1 x < packets e.2 y := by
  intro e he x y
  have heMap := List.mem_map.mp he
  cases heMap with
  | intro j hj =>
    cases hj with
    | intro hj heq =>
      cases e with
      | mk edgeLeft edgeRight =>
        simp only [Prod.mk.injEq] at heq
        cases heq.1
        cases heq.2
        apply hblockOrdered
        change (8 * j.val + 3) / 4 < (8 * j.val + 4) / 4
        omega
/-- Index the six untouched lanes in each eight-packet pair. -/
def fourLaneBoundarySingletonIndex {s : Nat} (k : Fin (6 * s)) : Fin (8 * s) :=
  Fin.mk (8 * (k.val / 6) + k.val % 6 + if k.val % 6 < 3 then 0 else 2) (by
    have hk := k.isLt
    by_cases h : k.val % 6 < 3 <;> simp [h] <;> omega)

def fourLaneBoundarySingletons (s : Nat) : List (Fin (8 * s)) :=
  (List.finRange (6 * s)).map fourLaneBoundarySingletonIndex

theorem fourLaneBoundarySingletonIndex_mod8 (s : Nat) (k : Fin (6 * s)) :
    And (Not ((fourLaneBoundarySingletonIndex k).val % 8 = 3))
      (Not ((fourLaneBoundarySingletonIndex k).val % 8 = 4)) := by
  have hrLt : k.val % 6 < 6 := Nat.mod_lt _ (by omega)
  by_cases hr : k.val % 6 < 3
  <;> constructor
  <;> intro h
  <;> simp [fourLaneBoundarySingletonIndex, hr] at h
  <;> omega

theorem fourLaneBoundarySingletons_nodup (s : Nat) :
    (fourLaneBoundarySingletons s).Nodup := by
  unfold fourLaneBoundarySingletons
  exact List.Nodup.map_on (l := List.finRange (6 * s)) (f := fourLaneBoundarySingletonIndex)
    (fun (i : Fin (6 * s)) hi (j : Fin (6 * s)) hj heq => by
      have hv := congrArg Fin.val heq
      have hiLt := i.isLt
      have hjLt := j.isLt
      by_cases hiR : i.val % 6 < 3 <;> by_cases hjR : j.val % 6 < 3
      <;> simp [fourLaneBoundarySingletonIndex, hiR, hjR] at hv
      <;> apply Fin.ext
      <;> omega)
    (List.nodup_finRange (6 * s))

theorem fourLaneBoundaryEdge_mem_repr {s : Nat} {e : Prod (Fin (8 * s)) (Fin (8 * s))}
    (he : List.Mem e (fourLaneBoundaryEdges s)) :
    Exists (fun j : Fin s => And (e.1.val = 8 * j.val + 3) (e.2.val = 8 * j.val + 4)) := by
  have heMap := List.mem_map.mp he
  cases heMap with
  | intro j hj =>
    cases hj with
    | intro hj heq =>
      cases e with
      | mk edgeLeft edgeRight =>
        simp only [Prod.mk.injEq] at heq
        cases heq.1
        cases heq.2
        exact Exists.intro j (And.intro rfl rfl)

theorem fourLaneBoundaryEdges_vertexDisjoint (s : Nat) :
    forall e, List.Mem e (fourLaneBoundaryEdges s) ->
      forall f, List.Mem f (fourLaneBoundaryEdges s) ->
        Not (e = f) ->
          And (Not (e.1 = f.1)) (And (Not (e.1 = f.2))
            (And (Not (e.2 = f.1)) (Not (e.2 = f.2)))) := by
  intro e he f hf hne
  have heR := fourLaneBoundaryEdge_mem_repr he
  have hfR := fourLaneBoundaryEdge_mem_repr hf
  cases heR with
  | intro j heEnds =>
    cases heEnds with
    | intro hLeft hRight =>
      cases hfR with
      | intro l hfEnds =>
        cases hfEnds with
        | intro hfLeft hfRight =>
          have hjl : Not (j.val = l.val) := by
            intro h
            apply hne
            apply Prod.ext <;> apply Fin.ext <;> omega
          have h11 : Not (e.1 = f.1) := by
            intro h
            have hv := congrArg Fin.val h
            rw [hLeft, hfLeft] at hv
            omega
          have h12 : Not (e.1 = f.2) := by
            intro h
            have hv := congrArg Fin.val h
            rw [hLeft, hfRight] at hv
            omega
          have h21 : Not (e.2 = f.1) := by
            intro h
            have hv := congrArg Fin.val h
            rw [hRight, hfLeft] at hv
            omega
          have h22 : Not (e.2 = f.2) := by
            intro h
            have hv := congrArg Fin.val h
            rw [hRight, hfRight] at hv
            omega
          exact And.intro h11 (And.intro h12 (And.intro h21 h22))

theorem fourLaneBoundarySingletons_free (s : Nat) :
    forall i, List.Mem i (fourLaneBoundarySingletons s) ->
      forall e, List.Mem e (fourLaneBoundaryEdges s) ->
        And (Not (e.1 = i)) (Not (e.2 = i)) := by
  intro i hi e he
  have hiMap := List.mem_map.mp hi
  cases hiMap with
  | intro k hk =>
    cases hk with
    | intro hk heq =>
      have edgeRepr := fourLaneBoundaryEdge_mem_repr he
      cases edgeRepr with
      | intro j hEnds =>
        cases hEnds with
        | intro hLeft hRight =>
          have hidx := congrArg (fun z : Fin (8 * s) => z.val % 8) heq
          have hnotLeft : Not (e.1 = i) := by
            intro hEq
            have hval := congrArg Fin.val hEq
            rw [hLeft] at hval
            have hmod : i.val % 8 = 3 := by omega
            exact (fourLaneBoundarySingletonIndex_mod8 s k).1 (hidx.trans hmod)
          have hnotRight : Not (e.2 = i) := by
            intro hEq
            have hval := congrArg Fin.val hEq
            rw [hRight] at hval
            have hmod : i.val % 8 = 4 := by omega
            exact (fourLaneBoundarySingletonIndex_mod8 s k).2 (hidx.trans hmod)
          exact And.intro hnotLeft hnotRight

theorem fourLaneBoundaryMatching_covers (s : Nat) (i : Fin (8 * s)) :
    Or (Exists (fun e : Prod (Fin (8 * s)) (Fin (8 * s)) =>
      And (List.Mem e (fourLaneBoundaryEdges s)) (Or (e.1 = i) (e.2 = i))))
      (List.Mem i (fourLaneBoundarySingletons s)) := by
  have hi := i.isLt
  let j : Fin s := Fin.mk (i.val / 8) (by omega)
  by_cases h3 : i.val % 8 = 3
  · let e : Prod (Fin (8 * s)) (Fin (8 * s)) :=
      (Fin.mk (8 * j.val + 3) (by omega), Fin.mk (8 * j.val + 4) (by omega))
    have he : List.Mem e (fourLaneBoundaryEdges s) := by
      apply List.mem_map.mpr
      exact Exists.intro j (And.intro ((by simp)) rfl)
    have hleft : e.1 = i := Fin.ext (by
      dsimp [e, j]
      omega)
    exact Or.inl (Exists.intro e (And.intro he (Or.inl hleft)))
  · by_cases h4 : i.val % 8 = 4
    · let e : Prod (Fin (8 * s)) (Fin (8 * s)) :=
        (Fin.mk (8 * j.val + 3) (by omega), Fin.mk (8 * j.val + 4) (by omega))
      have he : List.Mem e (fourLaneBoundaryEdges s) := by
        apply List.mem_map.mpr
        exact Exists.intro j (And.intro ((by simp)) rfl)
      have hright : e.2 = i := Fin.ext (by
        dsimp [e, j]
        omega)
      exact Or.inl (Exists.intro e (And.intro he (Or.inr hright)))
    · let q := i.val / 8
      let r := i.val % 8
      have hrLt : r < 8 := by dsimp [r]; omega
      have hdecomp8 : r + 8 * q = i.val := by
        dsimp [r, q]
        exact Nat.mod_add_div i.val 8
      have hnot3 : Not (r = 3) := by dsimp [r]; exact h3
      have hnot4 : Not (r = 4) := by dsimp [r]; exact h4
      let t := if r < 3 then r else r - 2
      have htLt : t < 6 := by
        by_cases hr : r < 3 <;> simp [t, hr] <;> omega
      let k : Fin (6 * s) := Fin.mk (6 * q + t) (by omega)
      have hqk : (6 * q + t) / 6 = q := by omega
      have hrk : (6 * q + t) % 6 = t := by omega
      have hkEq : fourLaneBoundarySingletonIndex k = i := Fin.ext (by
        dsimp [k, fourLaneBoundarySingletonIndex]
        rw [hqk, hrk]
        change 8 * q + t + (if t < 3 then 0 else 2) = i.val
        by_cases hr : r < 3
        · simp [t, hr]
          omega
        · have hrGe : 5 <= r := by
            dsimp [r] at hnot3 hnot4
            omega
          have htEq : t = r - 2 := by simp [t, hr]
          have htNot : Not (t < 3) := by rw [htEq]; omega
          simp [htNot]
          rw [htEq]
          omega)
      have hk : List.Mem i (fourLaneBoundarySingletons s) := by
        unfold fourLaneBoundarySingletons
        apply List.mem_map.mpr
        exact Exists.intro k (And.intro ((by simp)) hkEq)
      exact Or.inr hk

theorem fourLaneBoundarySingleton_mem_of_nonedge {s : Nat} (i : Fin (8 * s))
    (h3 : Not (i.val % 8 = 3)) (h4 : Not (i.val % 8 = 4)) :
    List.Mem i (fourLaneBoundarySingletons s) := by
  cases fourLaneBoundaryMatching_covers s i with
  | inr hsingle => exact hsingle
  | inl hincident =>
    cases hincident with
    | intro e he =>
      cases he with
      | intro hedge hside =>
        cases hside with
        | inl hleft =>
          have hrepr := fourLaneBoundaryEdge_mem_repr hedge
          cases hrepr with
          | intro j hvals =>
            cases hvals with
            | intro hv hright =>
              have hval := congrArg Fin.val hleft
              rw [hv] at hval
              have hmod : i.val % 8 = 3 := by omega
              exact False.elim (h3 hmod)
        | inr hright =>
          have hrepr := fourLaneBoundaryEdge_mem_repr hedge
          cases hrepr with
          | intro j hvals =>
            cases hvals with
            | intro hleft hv =>
              have hval := congrArg Fin.val hright
              rw [hv] at hval
              have hmod : i.val % 8 = 4 := by omega
              exact False.elim (h4 hmod)

theorem fourLaneBoundarySingletons_length (s : Nat) :
    (fourLaneBoundarySingletons s).length = 6 * s := by
  simp [fourLaneBoundarySingletons]
theorem fourLaneBoundaryEdges_length (s : Nat) :
    (fourLaneBoundaryEdges s).length = s := by
  simp [fourLaneBoundaryEdges]

theorem fourLaneBoundarySingletons_disjoint (s : Nat) :
    List.Pairwise (fun i j : Fin (8 * s) => Not (i = j)) (fourLaneBoundarySingletons s) := by
  exact (List.nodup_iff_pairwise_ne.mp (fourLaneBoundarySingletons_nodup s))

theorem fourLaneBoundaryMatching_count (s : Nat) :
    2 * (fourLaneBoundaryEdges s).length +
      (fourLaneBoundarySingletons s).length = 8 * s := by
  simp [fourLaneBoundaryEdges_length, fourLaneBoundarySingletons_length]
  omega

def fourLaneBoundaryMatching (s : Nat) : IndexedPacketMatching (8 * s) where
  edges := fourLaneBoundaryEdges s
  nodup := fourLaneBoundaryEdges_nodup s
  noFixed := fourLaneBoundaryEdges_noFixed s
  vertexDisjoint := fourLaneBoundaryEdges_vertexDisjoint s
  singles := fourLaneBoundarySingletons s
  singleDisjoint := fourLaneBoundarySingletons_disjoint s
  free := fourLaneBoundarySingletons_free s
  covers := fourLaneBoundaryMatching_covers s
  count := fourLaneBoundaryMatching_count s

/-- Pair the two packets straddling the midpoint between each adjacent pair
of eight-packet blocks. The resulting matching acts on sixteen-packet
cohorts and is the candidate next stage after `fourLaneBoundaryMatching`. -/
def eightLaneBoundaryEdges (s : Nat) :
    List (Fin (16 * s) × Fin (16 * s)) :=
  (List.finRange s).map fun j =>
    (⟨16 * j.val + 7, by have hj := j.isLt; omega⟩,
      ⟨16 * j.val + 8, by have hj := j.isLt; omega⟩)

theorem eightLaneBoundaryEdges_nodup (s : Nat) :
    (eightLaneBoundaryEdges s).Nodup := by
  unfold eightLaneBoundaryEdges
  apply List.Nodup.map_on
  · intro j hj k hk heq
    have hv := congrArg (fun e : Fin (16 * s) × Fin (16 * s) => e.1.val) heq
    simp at hv
    apply Fin.ext
    omega
  · exact List.nodup_finRange s

theorem eightLaneBoundaryEdges_noFixed (s : Nat) :
    ∀ e, e ∈ eightLaneBoundaryEdges s → e.1 ≠ e.2 := by
  intro e he
  simp only [eightLaneBoundaryEdges, List.mem_map, List.mem_finRange] at he
  obtain ⟨j, -, rfl⟩ := he
  intro h
  have hv := congrArg Fin.val h
  simp at hv

theorem eightLaneBoundaryEdge_mem_repr {s : Nat}
    {e : Fin (16 * s) × Fin (16 * s)}
    (he : e ∈ eightLaneBoundaryEdges s) :
    ∃ j : Fin s, e.1.val = 16 * j.val + 7 ∧ e.2.val = 16 * j.val + 8 := by
  simp only [eightLaneBoundaryEdges, List.mem_map, List.mem_finRange] at he
  obtain ⟨j, -, heq⟩ := he
  cases e with
  | mk left right =>
    simp only [Prod.mk.injEq] at heq
    cases heq.1
    cases heq.2
    exact ⟨j, rfl, rfl⟩

theorem eightLaneBoundaryEdges_vertexDisjoint (s : Nat) :
    ∀ e, e ∈ eightLaneBoundaryEdges s →
      ∀ f, f ∈ eightLaneBoundaryEdges s → e ≠ f →
        e.1 ≠ f.1 ∧ e.1 ≠ f.2 ∧ e.2 ≠ f.1 ∧ e.2 ≠ f.2 := by
  intro e he f hf hne
  obtain ⟨j, hj₁, hj₂⟩ := eightLaneBoundaryEdge_mem_repr he
  obtain ⟨k, hk₁, hk₂⟩ := eightLaneBoundaryEdge_mem_repr hf
  have hjk : j.val ≠ k.val := by
    intro h
    apply hne
    apply Prod.ext <;> apply Fin.ext <;> omega
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    intro h <;> have hv := congrArg Fin.val h <;>
    simp only [hj₁, hj₂, hk₁, hk₂] at hv <;> omega

/-- Index the fourteen unmatched packet IDs in each sixteen-ID cohort. -/
def eightLaneBoundarySingletonIndex {s : Nat} (k : Fin (14 * s)) :
    Fin (16 * s) :=
  ⟨16 * (k.val / 14) + k.val % 14 +
      if k.val % 14 < 7 then 0 else 2, by
    have hk := k.isLt
    by_cases h : k.val % 14 < 7 <;> simp [h] <;> omega⟩

def eightLaneBoundarySingletons (s : Nat) : List (Fin (16 * s)) :=
  (List.finRange (14 * s)).map eightLaneBoundarySingletonIndex

theorem eightLaneBoundarySingletonIndex_mod16 (s : Nat) (k : Fin (14 * s)) :
    (eightLaneBoundarySingletonIndex k).val % 16 ≠ 7 ∧
      (eightLaneBoundarySingletonIndex k).val % 16 ≠ 8 := by
  have hr : k.val % 14 < 14 := Nat.mod_lt _ (by omega)
  by_cases h : k.val % 14 < 7
  · constructor <;> intro hmod <;>
      simp [eightLaneBoundarySingletonIndex, h] at hmod <;> omega
  · constructor <;> intro hmod <;>
      simp [eightLaneBoundarySingletonIndex, h] at hmod <;> omega

theorem eightLaneBoundarySingletons_nodup (s : Nat) :
    (eightLaneBoundarySingletons s).Nodup := by
  unfold eightLaneBoundarySingletons
  apply List.Nodup.map_on
  · intro i hi j hj heq
    have hv := congrArg Fin.val heq
    have hiLt := i.isLt
    have hjLt := j.isLt
    by_cases hiR : i.val % 14 < 7 <;> by_cases hjR : j.val % 14 < 7
    · simp [eightLaneBoundarySingletonIndex, hiR, hjR] at hv
      apply Fin.ext
      omega
    · simp [eightLaneBoundarySingletonIndex, hiR, hjR] at hv
      apply Fin.ext
      omega
    · simp [eightLaneBoundarySingletonIndex, hiR, hjR] at hv
      apply Fin.ext
      omega
    · simp [eightLaneBoundarySingletonIndex, hiR, hjR] at hv
      apply Fin.ext
      omega
  · exact List.nodup_finRange (14 * s)

theorem eightLaneBoundarySingletons_free (s : Nat) :
    ∀ i, i ∈ eightLaneBoundarySingletons s →
      ∀ e, e ∈ eightLaneBoundaryEdges s → e.1 ≠ i ∧ e.2 ≠ i := by
  intro i hi e he
  simp only [eightLaneBoundarySingletons, List.mem_map, List.mem_finRange] at hi
  obtain ⟨k, -, rfl⟩ := hi
  obtain ⟨j, hleft, hright⟩ := eightLaneBoundaryEdge_mem_repr he
  constructor
  · intro hEq
    have hidx := congrArg (fun z : Fin (16 * s) => z.val % 16) hEq
    have hleftMod : e.1.val % 16 = 7 := by rw [hleft]; omega
    exact (eightLaneBoundarySingletonIndex_mod16 s k).1 (hidx.symm.trans hleftMod)
  · intro hEq
    have hidx := congrArg (fun z : Fin (16 * s) => z.val % 16) hEq
    have hrightMod : e.2.val % 16 = 8 := by rw [hright]; omega
    exact (eightLaneBoundarySingletonIndex_mod16 s k).2 (hidx.symm.trans hrightMod)

theorem eightLaneBoundaryMatching_covers (s : Nat) (i : Fin (16 * s)) :
    (∃ e ∈ eightLaneBoundaryEdges s, e.1 = i ∨ e.2 = i) ∨
      i ∈ eightLaneBoundarySingletons s := by
  have hi := i.isLt
  let q := i.val / 16
  let r := i.val % 16
  have hrLt : r < 16 := by dsimp [r]; omega
  have hdecomp : r + 16 * q = i.val := by
    dsimp [r, q]
    exact Nat.mod_add_div i.val 16
  let j : Fin s := ⟨q, by dsimp [q]; omega⟩
  by_cases h7 : r = 7
  · left
    let e : Fin (16 * s) × Fin (16 * s) :=
      (⟨16 * j.val + 7, by have := j.isLt; omega⟩,
       ⟨16 * j.val + 8, by have := j.isLt; omega⟩)
    have he : e ∈ eightLaneBoundaryEdges s := by
      unfold eightLaneBoundaryEdges
      apply List.mem_map.mpr
      exact ⟨j, List.mem_finRange j, by simp [e]⟩
    have hleft : e.1 = i := by
      apply Fin.ext
      dsimp [e, j, q, r]
      omega
    exact ⟨e, he, Or.inl hleft⟩
  · by_cases h8 : r = 8
    · left
      let e : Fin (16 * s) × Fin (16 * s) :=
        (⟨16 * j.val + 7, by have := j.isLt; omega⟩,
         ⟨16 * j.val + 8, by have := j.isLt; omega⟩)
      have he : e ∈ eightLaneBoundaryEdges s := by
        unfold eightLaneBoundaryEdges
        apply List.mem_map.mpr
        exact ⟨j, List.mem_finRange j, by simp [e]⟩
      have hright : e.2 = i := by
        apply Fin.ext
        dsimp [e, j, q, r]
        omega
      exact ⟨e, he, Or.inr hright⟩
    · right
      have hnot7 : r ≠ 7 := h7
      have hnot8 : r ≠ 8 := h8
      let t := if r < 7 then r else r - 2
      have htLt : t < 14 := by
        by_cases hr : r < 7 <;> simp [t, hr] <;> omega
      let k : Fin (14 * s) := ⟨14 * q + t, by
        have hq : q < s := by dsimp [q]; omega
        omega⟩
      have hqk : k.val / 14 = q := by
        dsimp [k]
        omega
      have hrk : k.val % 14 = t := by
        dsimp [k]
        omega
      have hkEq : eightLaneBoundarySingletonIndex k = i := by
        apply Fin.ext
        change 16 * (k.val / 14) + k.val % 14 +
          (if k.val % 14 < 7 then 0 else 2) = i.val
        rw [hqk, hrk]
        change 16 * q + t + (if t < 7 then 0 else 2) = i.val
        by_cases hr : r < 7
        · simp [t, hr]
          omega
        · have hrge : 9 ≤ r := by omega
          have htge : 7 ≤ t := by simp [t, hr]; omega
          have htNot : ¬ r - 2 < 7 := by omega
          simp [t, hr, htNot]
          omega
      unfold eightLaneBoundarySingletons
      apply List.mem_map.mpr
      exact ⟨k, List.mem_finRange k, hkEq⟩

theorem eightLaneBoundarySingletons_length (s : Nat) :
    (eightLaneBoundarySingletons s).length = 14 * s := by
  simp [eightLaneBoundarySingletons]

theorem eightLaneBoundaryEdges_length (s : Nat) :
    (eightLaneBoundaryEdges s).length = s := by
  simp [eightLaneBoundaryEdges]

theorem eightLaneBoundarySingletons_disjoint (s : Nat) :
    List.Pairwise (fun i j : Fin (16 * s) => i ≠ j)
      (eightLaneBoundarySingletons s) := by
  exact (List.nodup_iff_pairwise_ne.mp (eightLaneBoundarySingletons_nodup s))

theorem eightLaneBoundaryMatching_count (s : Nat) :
    2 * (eightLaneBoundaryEdges s).length +
      (eightLaneBoundarySingletons s).length = 16 * s := by
  simp [eightLaneBoundaryEdges_length, eightLaneBoundarySingletons_length]
  omega

def eightLaneBoundaryMatching (s : Nat) : IndexedPacketMatching (16 * s) where
  edges := eightLaneBoundaryEdges s
  nodup := eightLaneBoundaryEdges_nodup s
  noFixed := eightLaneBoundaryEdges_noFixed s
  vertexDisjoint := eightLaneBoundaryEdges_vertexDisjoint s
  singles := eightLaneBoundarySingletons s
  singleDisjoint := eightLaneBoundarySingletons_disjoint s
  free := eightLaneBoundarySingletons_free s
  covers := eightLaneBoundaryMatching_covers s
  count := eightLaneBoundaryMatching_count s

theorem eightLaneBoundaryMatching_ordered {s N : Nat}
    (packets : Fin (16 * s) → Function.Embedding (Fin 64) (Fin N))
    (hblockOrdered : ∀ i j, i.val / 8 < j.val / 8 → ∀ x y,
      packets i x < packets j y) :
    ∀ e ∈ (eightLaneBoundaryMatching s).edges, ∀ x y,
      packets e.1 x < packets e.2 y := by
  intro e he x y
  obtain ⟨j, hleft, hright⟩ := eightLaneBoundaryEdge_mem_repr he
  apply hblockOrdered
  rw [hleft, hright]
  change (16 * j.val + 7) / 8 < (16 * j.val + 8) / 8
  omega

theorem fourLaneBoundaryMatching_ordered {s N : Nat}
    (packets : Fin (8 * s) -> Function.Embedding (Fin 64) (Fin N))
    (hblockOrdered : forall i j, i.val / 4 < j.val / 4 -> forall x y,
      packets i x < packets j y) :
    forall e, List.Mem e (fourLaneBoundaryMatching s).edges -> forall x y,
      packets e.1 x < packets e.2 y := by
  intro e he x y
  change List.Mem e (fourLaneBoundaryEdges s) at he
  exact fourLaneBoundaryEdges_ordered packets hblockOrdered e he x y

/-- If packet IDs are laid out as two lanes per physically ordered block,
`interBlockBoundaryMatching` is oriented from lower to higher supports on
every edge. -/
theorem interBlockBoundaryMatching_ordered {r N : Nat}
    (packets : Fin (2 * (2 * r)) → Fin 64 ↪ Fin N)
    (hblockOrdered : ∀ i j, i.val / 2 < j.val / 2 → ∀ x y,
      packets i x < packets j y) :
    ∀ e ∈ (interBlockBoundaryMatching r).edges, ∀ x y,
      packets e.1 x < packets e.2 y := by
  intro e he x y
  change e ∈ interBlockBoundaryEdges r at he
  simp only [interBlockBoundaryEdges, List.mem_map, List.mem_finRange] at he
  obtain ⟨j, _, rfl⟩ := he
  exact hblockOrdered _ _ (by
    change (4 * j.val + 1) / 2 < (4 * j.val + 2) / 2
    omega) x y

/-- The two dealt outputs of a boundary edge are members of the actual
partial-matching round output family. -/
theorem genIndexedPacketRound_deal_mem {m N : Nat}
    (packets : Fin m -> Function.Embedding (Fin 64) (Fin N))
    (hdisjoint : forall i j, Not (i = j) -> forall x y, Not (packets i x = packets j y))
    (edges : List (Prod (Fin m) (Fin m)))
    (hnoFixed : forall e, List.Mem e edges -> Not (e.1 = e.2))
    (joined : Function.Embedding (Fin 128) (Fin N))
    (hjoined : List.Mem joined (genIndexedPairSupports packets hdisjoint edges hnoFixed))
    (lane : Bool) :
    List.Mem (if lane then dealOddEmbedding joined else dealEvenEmbedding joined)
      (genIndexedPacketRoundOutput packets hdisjoint edges hnoFixed) := by
  change List.Mem (if lane then dealOddEmbedding joined else dealEvenEmbedding joined)
    (genPacketRound_outputPackets
      (genIndexedPairSupports packets hdisjoint edges hnoFixed))
  rw [genPacketRound_outputPackets]
  exact List.mem_flatMap.mpr
    (Exists.intro joined (And.intro hjoined (by cases lane <;> simp)))

theorem fourLaneBoundaryMatching_dealt_mem_output {s N : Nat}
    (packets : Fin (8 * s) -> Function.Embedding (Fin 64) (Fin N))
    (hdisjoint : forall i j, Not (i = j) -> forall x y, Not (packets i x = packets j y))
    (j : Fin s) (lane : Bool) :
    List.Mem (if lane then dealOddEmbedding (joinPacketEmbedding
        (packets (Fin.mk (8 * j.val + 3) (by omega)))
        (packets (Fin.mk (8 * j.val + 4) (by omega))) (by
          intro x y h
          exact hdisjoint _ _ (by
            intro heq
            have hv := congrArg Fin.val heq
            simp at hv) x y h))
      else dealEvenEmbedding (joinPacketEmbedding
        (packets (Fin.mk (8 * j.val + 3) (by omega)))
        (packets (Fin.mk (8 * j.val + 4) (by omega))) (by
          intro x y h
          exact hdisjoint _ _ (by
            intro heq
            have hv := congrArg Fin.val heq
            simp at hv) x y h)))
      (genIndexedPacketRoundOutput packets hdisjoint
        (fourLaneBoundaryMatching s).edges (fourLaneBoundaryMatching s).noFixed) := by
  let left : Fin (8 * s) := Fin.mk (8 * j.val + 3) (by omega)
  let right : Fin (8 * s) := Fin.mk (8 * j.val + 4) (by omega)
  have hne : Not (left = right) := by
    intro heq
    have hv := congrArg Fin.val heq
    simp [left, right] at hv
  have hsep : forall x y, Not (packets left x = packets right y) := hdisjoint left right hne
  let joined := joinPacketEmbedding (packets left) (packets right) hsep
  let edge : Prod (Fin (8 * s)) (Fin (8 * s)) := (left, right)
  have hedge : List.Mem edge (fourLaneBoundaryMatching s).edges := by
    change List.Mem edge (fourLaneBoundaryEdges s)
    simp only [fourLaneBoundaryEdges, List.mem_map]
    exact List.mem_map.mpr (Exists.intro j (And.intro (List.mem_finRange j) rfl))
  have hjoined : List.Mem joined
      (genIndexedPairSupports packets hdisjoint
        (fourLaneBoundaryMatching s).edges (fourLaneBoundaryMatching s).noFixed) := by
    apply List.mem_map.mpr
    exact Exists.intro (Subtype.mk edge hedge)
      (And.intro (by simp) (by simp [joined, edge, left, right]))
  change List.Mem (if lane then dealOddEmbedding joined else dealEvenEmbedding joined)
    (genIndexedPacketRoundOutput packets hdisjoint
      (fourLaneBoundaryMatching s).edges (fourLaneBoundaryMatching s).noFixed)
  exact genIndexedPacketRound_deal_mem packets hdisjoint
    (fourLaneBoundaryMatching s).edges (fourLaneBoundaryMatching s).noFixed
    joined hjoined lane

theorem eightLaneBoundaryMatching_dealt_mem_output {s N : Nat}
    (packets : Fin (16 * s) → Function.Embedding (Fin 64) (Fin N))
    (hdisjoint : ∀ i j, i ≠ j → ∀ x y, packets i x ≠ packets j y)
    (j : Fin s) (odd : Bool) :
    (if odd then dealOddEmbedding else dealEvenEmbedding)
      (joinPacketEmbedding
        (packets ⟨16 * j.val + 7, by have := j.isLt; omega⟩)
        (packets ⟨16 * j.val + 8, by have := j.isLt; omega⟩)
        (by
          intro x y hxy
          apply hdisjoint _ _ (by
            intro heq
            have hv := congrArg Fin.val heq
            simp at hv) x y hxy)) ∈
      genIndexedPacketRoundOutput packets hdisjoint
        (eightLaneBoundaryMatching s).edges
        (eightLaneBoundaryMatching s).noFixed := by
  let left : Fin (16 * s) := ⟨16 * j.val + 7, by have := j.isLt; omega⟩
  let right : Fin (16 * s) := ⟨16 * j.val + 8, by have := j.isLt; omega⟩
  have hne : left ≠ right := by
    intro heq
    have hv := congrArg Fin.val heq
    simp [left, right] at hv
  have hsep : ∀ x y, packets left x ≠ packets right y :=
    hdisjoint left right hne
  let joined := joinPacketEmbedding (packets left) (packets right) hsep
  let edge : Fin (16 * s) × Fin (16 * s) := (left, right)
  have hedge : edge ∈ (eightLaneBoundaryMatching s).edges := by
    change edge ∈ eightLaneBoundaryEdges s
    unfold eightLaneBoundaryEdges
    apply List.mem_map.mpr
    exact ⟨j, List.mem_finRange j, by simp [edge, left, right]⟩
  have hjoined : joined ∈ genIndexedPairSupports packets hdisjoint
      (eightLaneBoundaryMatching s).edges
      (eightLaneBoundaryMatching s).noFixed := by
    apply List.mem_map.mpr
    exact ⟨⟨edge, hedge⟩, by simp [joined, edge, left, right]⟩
  cases odd with
  | false =>
      simpa [joined, left, right] using genIndexedPacketRound_deal_mem packets
        hdisjoint (eightLaneBoundaryMatching s).edges
        (eightLaneBoundaryMatching s).noFixed joined hjoined false
  | true =>
      simpa [joined, left, right] using genIndexedPacketRound_deal_mem packets
        hdisjoint (eightLaneBoundaryMatching s).edges
        (eightLaneBoundaryMatching s).noFixed joined hjoined true

theorem eightLaneBoundarySingleton_mem_of_nonedge {s : Nat}
    (i : Fin (16 * s)) (h7 : i.val % 16 ≠ 7) (h8 : i.val % 16 ≠ 8) :
    i ∈ eightLaneBoundarySingletons s := by
  rcases eightLaneBoundaryMatching_covers s i with hEdge | hSingle
  · obtain ⟨e, he, hincident⟩ := hEdge
    obtain ⟨j, hleft, hright⟩ := eightLaneBoundaryEdge_mem_repr he
    rcases hincident with hEq | hEq
    · have hv := congrArg Fin.val hEq
      have hmod : i.val % 16 = 7 := by rw [hleft] at hv; omega
      exact False.elim (h7 hmod)
    · have hv := congrArg Fin.val hEq
      have hmod : i.val % 16 = 8 := by rw [hright] at hv; omega
      exact False.elim (h8 hmod)
  · exact hSingle

/-- The sixteen outputs of one wide boundary cohort, in block-major order. -/
def eightLaneBoundaryOutputBlock {s N : Nat}
    (packets : Fin (16 * s) → Function.Embedding (Fin 64) (Fin N))
    (hdisjoint : ∀ i j, i ≠ j → ∀ x y, packets i x ≠ packets j y)
    (j : Fin s) (lane : Fin 16) : Function.Embedding (Fin 64) (Fin N) :=
  let left : Fin (16 * s) := ⟨16 * j.val + 7, by have := j.isLt; omega⟩
  let right : Fin (16 * s) := ⟨16 * j.val + 8, by have := j.isLt; omega⟩
  let joined := joinPacketEmbedding (packets left) (packets right) (hdisjoint left right (by
    intro heq
    have hv := congrArg Fin.val heq
    simp [left, right] at hv))
  if lane.val = 7 then dealEvenEmbedding joined
  else if lane.val = 8 then dealOddEmbedding joined
  else packets ⟨16 * j.val + lane.val, by have := lane.isLt; have := j.isLt; omega⟩

theorem eightLaneBoundaryOutputBlock_mem {s N : Nat}
    (packets : Fin (16 * s) → Function.Embedding (Fin 64) (Fin N))
    (hdisjoint : ∀ i j, i ≠ j → ∀ x y, packets i x ≠ packets j y)
    (j : Fin s) (lane : Fin 16) :
    eightLaneBoundaryOutputBlock packets hdisjoint j lane ∈
      genIndexedPacketRoundOutputWithSingletons packets hdisjoint
        (eightLaneBoundaryMatching s).edges
        (eightLaneBoundaryMatching s).noFixed
        (eightLaneBoundaryMatching s).singles := by
  let left : Fin (16 * s) := ⟨16 * j.val + 7, by have := j.isLt; omega⟩
  let right : Fin (16 * s) := ⟨16 * j.val + 8, by have := j.isLt; omega⟩
  let joined := joinPacketEmbedding (packets left) (packets right) (hdisjoint left right (by
    intro heq
    have hv := congrArg Fin.val heq
    simp [left, right] at hv))
  by_cases h7 : lane.val = 7
  · have hraw := eightLaneBoundaryMatching_dealt_mem_output packets hdisjoint j false
    have hdealt : dealEvenEmbedding joined ∈ genIndexedPacketRoundOutput packets hdisjoint
        (eightLaneBoundaryMatching s).edges (eightLaneBoundaryMatching s).noFixed := by
      simpa [joined, left, right] using hraw
    simp only [eightLaneBoundaryOutputBlock, h7]
    exact List.mem_append.mpr (Or.inl hdealt)
  · by_cases h8 : lane.val = 8
    · have hraw := eightLaneBoundaryMatching_dealt_mem_output packets hdisjoint j true
      have hdealt : dealOddEmbedding joined ∈ genIndexedPacketRoundOutput packets hdisjoint
          (eightLaneBoundaryMatching s).edges (eightLaneBoundaryMatching s).noFixed := by
        simpa [joined, left, right] using hraw
      simp only [eightLaneBoundaryOutputBlock, h7, h8]
      exact List.mem_append.mpr (Or.inl hdealt)
    · let i : Fin (16 * s) := ⟨16 * j.val + lane.val, by have := lane.isLt; have := j.isLt; omega⟩
      have hi7 : i.val % 16 ≠ 7 := by simp [i]; omega
      have hi8 : i.val % 16 ≠ 8 := by simp [i]; omega
      have hsingle := eightLaneBoundarySingleton_mem_of_nonedge i hi7 hi8
      have hmem : List.Mem (packets i)
          (genIndexedPacketRoundOutputWithSingletons packets hdisjoint
            (eightLaneBoundaryMatching s).edges
            (eightLaneBoundaryMatching s).noFixed
            (eightLaneBoundaryMatching s).singles) := by
        apply List.mem_append.mpr
        apply Or.inr
        apply List.mem_map.mpr
        exact ⟨i, hsingle, rfl⟩
      simp only [eightLaneBoundaryOutputBlock, h7, h8]
      simpa [i, left, right] using hmem

theorem eightLaneBoundaryDealtOutputBlock_range {s N : Nat}
    (packets : Fin (16 * s) → Function.Embedding (Fin 64) (Fin N))
    (hdisjoint : ∀ i j, i ≠ j → ∀ x y, packets i x ≠ packets j y)
    (j : Fin s) (odd : Bool) (x : Fin 64) :
    ∃ i : Fin (16 * s),
      (i.val = 16 * j.val + 7 ∨ i.val = 16 * j.val + 8) ∧
      Set.range (packets i)
        ((if odd then
            dealOddEmbedding (joinPacketEmbedding
              (packets ⟨16 * j.val + 7, by have := j.isLt; omega⟩)
              (packets ⟨16 * j.val + 8, by have := j.isLt; omega⟩)
              (by
                intro a b hab
                apply hdisjoint _ _ (by
                  intro h
                  have hv := congrArg Fin.val h
                  simp at hv) a b hab))
          else
            dealEvenEmbedding (joinPacketEmbedding
            (packets ⟨16 * j.val + 7, by have := j.isLt; omega⟩)
            (packets ⟨16 * j.val + 8, by have := j.isLt; omega⟩)
            (by
              intro a b hab
              apply hdisjoint _ _ (by
                intro h
                have hv := congrArg Fin.val h
                simp at hv) a b hab))) x) := by
  let left : Fin (16 * s) := ⟨16 * j.val + 7, by have := j.isLt; omega⟩
  let right : Fin (16 * s) := ⟨16 * j.val + 8, by have := j.isLt; omega⟩
  have hsep : ∀ a b, packets left a ≠ packets right b := hdisjoint left right (by
    intro h
    have hv := congrArg Fin.val h
    simp [left, right] at hv)
  let joined := joinPacketEmbedding (packets left) (packets right) hsep
  have hmem : Set.range joined
      ((if odd then dealOddEmbedding joined else dealEvenEmbedding joined) x) := by
    refine ⟨if odd then oddWire 64 x else evenWire 64 x, ?_⟩
    cases odd <;> rfl
  rw [joinPacketEmbedding_range _ _ hsep] at hmem
  rcases hmem with hleft | hright
  · simpa [joined, left, right] using
      (⟨left, Or.inl (by simp [left]), hleft⟩ :
        ∃ i : Fin (16 * s),
          (i.val = 16 * j.val + 7 ∨ i.val = 16 * j.val + 8) ∧
          Set.range (packets i)
            ((if odd then dealOddEmbedding joined else dealEvenEmbedding joined) x))
  · simpa [joined, left, right] using
      (⟨right, Or.inr (by simp [right]), hright⟩ :
        ∃ i : Fin (16 * s),
          (i.val = 16 * j.val + 7 ∨ i.val = 16 * j.val + 8) ∧
          Set.range (packets i)
            ((if odd then dealOddEmbedding joined else dealEvenEmbedding joined) x))

theorem eightLaneBoundaryOutputBlock_source {s N : Nat}
    (packets : Fin (16 * s) → Function.Embedding (Fin 64) (Fin N))
    (hdisjoint : ∀ i j, i ≠ j → ∀ x y, packets i x ≠ packets j y)
    (j : Fin s) (lane : Fin 16) (x : Fin 64) :
    ∃ i : Fin (16 * s),
      (i.val / 8 = 2 * j.val ∨ i.val / 8 = 2 * j.val + 1) ∧
      ∃ z : Fin 64, eightLaneBoundaryOutputBlock packets hdisjoint j lane x =
        packets i z := by
  by_cases h7 : lane.val = 7
  · obtain ⟨i, hi, ⟨z, hz⟩⟩ :=
      eightLaneBoundaryDealtOutputBlock_range packets hdisjoint j false x
    refine ⟨i, ?_, z, ?_⟩
    · rcases hi with hi | hi <;> rw [hi] <;> omega
    · simpa [eightLaneBoundaryOutputBlock, h7] using hz.symm
  · by_cases h8 : lane.val = 8
    · obtain ⟨i, hi, ⟨z, hz⟩⟩ :=
        eightLaneBoundaryDealtOutputBlock_range packets hdisjoint j true x
      refine ⟨i, ?_, z, ?_⟩
      · rcases hi with hi | hi <;> rw [hi] <;> omega
      · simpa [eightLaneBoundaryOutputBlock, h7, h8] using hz.symm
    · let i : Fin (16 * s) := ⟨16 * j.val + lane.val, by have := j.isLt; have := lane.isLt; omega⟩
      refine ⟨i, ?_, x, ?_⟩
      · simp [i]
        omega
      · simp [eightLaneBoundaryOutputBlock, h7, h8, i]

theorem eightLaneBoundaryOutputBlocks_ordered {s N : Nat}
    (packets : Fin (16 * s) → Function.Embedding (Fin 64) (Fin N))
    (hdisjoint : ∀ i j, i ≠ j → ∀ x y, packets i x ≠ packets j y)
    (hblockOrdered : ∀ i k, i.val / 8 < k.val / 8 → ∀ x y,
      packets i x < packets k y)
    (j k : Fin s) (hjk : j.val < k.val) (lane lane' : Fin 16)
    (x y : Fin 64) :
    eightLaneBoundaryOutputBlock packets hdisjoint j lane x <
      eightLaneBoundaryOutputBlock packets hdisjoint k lane' y := by
  obtain ⟨i, hi, z, hz⟩ :=
    eightLaneBoundaryOutputBlock_source packets hdisjoint j lane x
  obtain ⟨i', hi', z', hz'⟩ :=
    eightLaneBoundaryOutputBlock_source packets hdisjoint k lane' y
  rw [hz, hz']
  apply hblockOrdered i i'
  rcases hi with hi | hi <;> rcases hi' with hi' | hi' <;> rw [hi, hi'] <;> omega

def eightLaneBoundaryGroupedOutput {s N : Nat}
    (packets : Fin (16 * s) → Function.Embedding (Fin 64) (Fin N))
    (hdisjoint : ∀ i j, i ≠ j → ∀ x y, packets i x ≠ packets j y)
    (i : Fin (16 * s)) : Function.Embedding (Fin 64) (Fin N) :=
  let j : Fin s := ⟨i.val / 16, by have hi := i.isLt; omega⟩
  let lane : Fin 16 := ⟨i.val % 16, by omega⟩
  eightLaneBoundaryOutputBlock packets hdisjoint j lane

theorem eightLaneBoundaryGroupedOutput_ordered {s N : Nat}
    (packets : Fin (16 * s) → Function.Embedding (Fin 64) (Fin N))
    (hdisjoint : ∀ i j, i ≠ j → ∀ x y, packets i x ≠ packets j y)
    (hblockOrdered : ∀ i j, i.val / 8 < j.val / 8 → ∀ x y,
      packets i x < packets j y)
    (i k : Fin (16 * s)) (hblock : i.val / 16 < k.val / 16)
    (x y : Fin 64) :
    eightLaneBoundaryGroupedOutput packets hdisjoint i x <
      eightLaneBoundaryGroupedOutput packets hdisjoint k y := by
  let j : Fin s := ⟨i.val / 16, by have hi := i.isLt; omega⟩
  let l : Fin s := ⟨k.val / 16, by have hk := k.isLt; omega⟩
  let lane : Fin 16 := ⟨i.val % 16, by omega⟩
  let lane' : Fin 16 := ⟨k.val % 16, by omega⟩
  change eightLaneBoundaryOutputBlock packets hdisjoint j lane x <
    eightLaneBoundaryOutputBlock packets hdisjoint l lane' y
  exact eightLaneBoundaryOutputBlocks_ordered packets hdisjoint hblockOrdered
    j l hblock lane lane' x y

theorem eightLaneBoundaryGroupedOutput_at {s N : Nat}
    (packets : Fin (16 * s) → Function.Embedding (Fin 64) (Fin N))
    (hdisjoint : ∀ i j, i ≠ j → ∀ x y, packets i x ≠ packets j y)
    (j : Fin s) (lane : Fin 16) :
    eightLaneBoundaryGroupedOutput packets hdisjoint
      ⟨16 * j.val + lane.val, by have hj := j.isLt; have hl := lane.isLt; omega⟩ =
    eightLaneBoundaryOutputBlock packets hdisjoint j lane := by
  ext x
  simp only [eightLaneBoundaryGroupedOutput]
  have hj := j.isLt
  have hl := lane.isLt
  have hmod : (16 * j.val + lane.val) % 16 = lane.val := by
    simp [Nat.add_mod, Nat.mod_eq_of_lt hl]
  have hdiv : (16 * j.val + lane.val) / 16 = j.val := by
    have hidentity := Nat.mod_add_div (16 * j.val + lane.val) 16
    rw [hmod] at hidentity
    omega
  have hblock : (⟨(16 * j.val + lane.val) / 16, by rw [hdiv]; exact hj⟩ : Fin s) = j :=
    Fin.ext hdiv
  have hlane : (⟨(16 * j.val + lane.val) % 16, by rw [hmod]; exact hl⟩ : Fin 16) = lane :=
    Fin.ext hmod
  rw [hblock, hlane]

/-- The final lane of one sixteen-packet output block precedes the first lane
of the next, providing the orientation input for the next boundary scale. -/
theorem eightLaneBoundaryGroupedOutput_nextWideBoundaryEdge_ordered {s N : Nat}
    (packets : Fin (16 * (2 * s)) → Function.Embedding (Fin 64) (Fin N))
    (hdisjoint : ∀ i j, i ≠ j → ∀ x y, packets i x ≠ packets j y)
    (hblockOrdered : ∀ i j, i.val / 8 < j.val / 8 → ∀ x y,
      packets i x < packets j y)
    (j : Fin s) (x y : Fin 64) :
    eightLaneBoundaryGroupedOutput packets hdisjoint
        ⟨16 * (2 * j.val) + 15, by
          have hj : j.val < s := j.isLt
          have hmul := Nat.mul_lt_mul_of_pos_left hj (by decide : 0 < 2)
          have hmul' := Nat.mul_lt_mul_of_pos_left hmul (by decide : 0 < 16)
          omega⟩ x <
      eightLaneBoundaryGroupedOutput packets hdisjoint
        ⟨16 * (2 * j.val + 1), by
          have hj : j.val < s := j.isLt
          have hmul := Nat.mul_lt_mul_of_pos_left hj (by decide : 0 < 2)
          have hmul' := Nat.mul_lt_mul_of_pos_left hmul (by decide : 0 < 16)
          omega⟩ y := by
  let leftBlock : Fin (2 * s) := ⟨2 * j.val, by
    have hj : j.val < s := j.isLt
    have hmul : 2 * j.val < 2 * s := Nat.mul_lt_mul_of_pos_left hj (by decide : 0 < 2)
    omega⟩
  let rightBlock : Fin (2 * s) := ⟨2 * j.val + 1, by
    have hj : j.val < s := j.isLt
    have hmul : 2 * j.val < 2 * s := Nat.mul_lt_mul_of_pos_left hj (by decide : 0 < 2)
    omega⟩
  have hlt : leftBlock.val < rightBlock.val := by simp [leftBlock, rightBlock]
  have h := eightLaneBoundaryOutputBlocks_ordered packets hdisjoint
    hblockOrdered leftBlock rightBlock hlt (15 : Fin 16) (0 : Fin 16) x y
  have hleft' := eightLaneBoundaryGroupedOutput_at packets hdisjoint
    leftBlock (15 : Fin 16)
  have hright' := eightLaneBoundaryGroupedOutput_at packets hdisjoint
    rightBlock (0 : Fin 16)
  have hleft : eightLaneBoundaryGroupedOutput packets hdisjoint
      ⟨16 * (2 * j.val) + 15, by
        have hj : j.val < s := j.isLt
        have hmul := Nat.mul_lt_mul_of_pos_left hj (by decide : 0 < 2)
        have hmul' := Nat.mul_lt_mul_of_pos_left hmul (by decide : 0 < 16)
        omega⟩ = eightLaneBoundaryOutputBlock packets hdisjoint leftBlock 15 := by
    simpa [leftBlock] using hleft'
  have hright : eightLaneBoundaryGroupedOutput packets hdisjoint
      ⟨16 * (2 * j.val + 1), by
        have hj : j.val < s := j.isLt
        have hmul := Nat.mul_lt_mul_of_pos_left hj (by decide : 0 < 2)
        have hmul' := Nat.mul_lt_mul_of_pos_left hmul (by decide : 0 < 16)
        omega⟩ = eightLaneBoundaryOutputBlock packets hdisjoint rightBlock 0 := by
    simpa [rightBlock] using hright'
  rw [hleft, hright]
  exact h

theorem eightLaneBoundaryOutputBlock_lane_contract {s N : Nat} {α : Type}
    [LinearOrder α]
    (packets : Fin (16 * s) → Function.Embedding (Fin 64) (Fin N))
    (hdisjoint : ∀ i j, i ≠ j → ∀ x y, packets i x ≠ packets j y)
    (hpacketMono : ∀ i, StrictMono (packets i))
    (hblockOrdered : ∀ i j, i.val / 8 < j.val / 8 → ∀ x y,
      packets i x < packets j y)
    (v : Fin N → α)
    (hsorted : ∀ i, Monotone (fun x => v (packets i x)))
    (j : Fin s) (lane : Fin 16) :
    Monotone (fun x =>
      (genIndexedPacketRound packets hdisjoint
        (eightLaneBoundaryMatching s).edges
        (eightLaneBoundaryMatching s).noFixed).exec v
        (eightLaneBoundaryOutputBlock packets hdisjoint j lane x)) ∧
    StrictMono (eightLaneBoundaryOutputBlock packets hdisjoint j lane) := by
  let matching := eightLaneBoundaryMatching s
  have hsingleDisjoint : List.Pairwise
      (fun i k => ∀ x y, packets i x ≠ packets k y) matching.singles := by
    have haux : ∀ ids : List (Fin (16 * s)),
        List.Pairwise (fun i k => i ≠ k) ids →
        List.Pairwise (fun i k => ∀ x y, packets i x ≠ packets k y) ids := by
      intro ids hids
      induction ids with
      | nil => simp
      | cons i ids ih =>
          rcases List.pairwise_cons.mp hids with ⟨hhead, htail⟩
          apply List.pairwise_cons.mpr
          constructor
          · intro k hk x y
            exact hdisjoint i k (hhead k hk) x y
          · exact ih htail
    exact haux matching.singles matching.singleDisjoint
  have hcontract := genIndexedPacketRound_withSingletons_contract
    packets hdisjoint matching.edges matching.nodup matching.noFixed
    matching.vertexDisjoint matching.singles hsingleDisjoint matching.free
    matching.covers v hsorted
  have hmem := eightLaneBoundaryOutputBlock_mem packets hdisjoint j lane
  have hsortedLane := hcontract.1 _ hmem
  have hmonoOutputs := genIndexedPacketRound_withSingletons_output_strictMono
    packets hdisjoint matching.edges matching.noFixed matching.singles
    hpacketMono (eightLaneBoundaryMatching_ordered packets hblockOrdered)
  exact ⟨hsortedLane, hmonoOutputs _ hmem⟩

/-- A dealt lane is disjoint from any untouched lane of the same
sixteen-packet block. -/
theorem eightLaneBoundaryDealtOutputBlock_disjoint_singleton {s N : Nat}
    (packets : Fin (16 * s) → Function.Embedding (Fin 64) (Fin N))
    (hdisjoint : ∀ i j, i ≠ j → ∀ x y, packets i x ≠ packets j y)
    (j : Fin s) (odd : Bool) (lane : Fin 16)
    (h7 : lane.val ≠ 7) (h8 : lane.val ≠ 8) (x y : Fin 64) :
    (if odd then
      dealOddEmbedding (joinPacketEmbedding
        (packets ⟨16 * j.val + 7, by have := j.isLt; omega⟩)
        (packets ⟨16 * j.val + 8, by have := j.isLt; omega⟩) (by
          intro a b h
          exact hdisjoint _ _ (by intro heq; have hv := congrArg Fin.val heq; simp at hv) a b h))
    else
      dealEvenEmbedding (joinPacketEmbedding
        (packets ⟨16 * j.val + 7, by have := j.isLt; omega⟩)
        (packets ⟨16 * j.val + 8, by have := j.isLt; omega⟩) (by
          intro a b h
          exact hdisjoint _ _ (by intro heq; have hv := congrArg Fin.val heq; simp at hv) a b h))) x ≠
      packets ⟨16 * j.val + lane.val, by have := j.isLt; have := lane.isLt; omega⟩ y := by
  obtain ⟨i, hi, ⟨z, hz⟩⟩ := eightLaneBoundaryDealtOutputBlock_range
    packets hdisjoint j odd x
  let singleton : Fin (16 * s) := ⟨16 * j.val + lane.val, by have := j.isLt; have := lane.isLt; omega⟩
  have hne : i ≠ singleton := by
    intro heq
    have hv := congrArg Fin.val heq
    rcases hi with hi | hi <;> simp [singleton] at hv <;> omega
  have hsrc := hdisjoint i singleton hne z y
  intro heq
  apply hsrc
  rw [hz, heq]

/-- Distinct output lanes in one sixteen-packet block have disjoint supports. -/
theorem eightLaneBoundaryOutputBlock_pairwise_disjoint {s N : Nat}
    (packets : Fin (16 * s) → Function.Embedding (Fin 64) (Fin N))
    (hdisjoint : ∀ i j, i ≠ j → ∀ x y, packets i x ≠ packets j y)
    (j : Fin s) (lane lane' : Fin 16) (hlane : lane ≠ lane') (x y : Fin 64) :
    eightLaneBoundaryOutputBlock packets hdisjoint j lane x ≠
      eightLaneBoundaryOutputBlock packets hdisjoint j lane' y := by
  by_cases hl7 : lane.val = 7
  · by_cases hr7 : lane'.val = 7
    · exact False.elim (hlane (Fin.ext (hl7.trans hr7.symm)))
    · by_cases hr8 : lane'.val = 8
      · let left : Fin (16 * s) := ⟨16 * j.val + 7, by have := j.isLt; omega⟩
        let right : Fin (16 * s) := ⟨16 * j.val + 8, by have := j.isLt; omega⟩
        have hsep : ∀ a b, packets left a ≠ packets right b := hdisjoint left right (by
          intro heq; have hv := congrArg Fin.val heq; simp [left, right] at hv)
        simpa [eightLaneBoundaryOutputBlock, hl7, hr7, hr8, left, right] using
          dealEmbeddings_disjoint (joinPacketEmbedding (packets left) (packets right) hsep) x y
      · have hr8' : lane'.val ≠ 8 := hr8
        have h := eightLaneBoundaryDealtOutputBlock_disjoint_singleton
          packets hdisjoint j false lane' hr7 hr8' x y
        simpa [eightLaneBoundaryOutputBlock, hl7, hr7, hr8, bne_iff_ne] using h
  · by_cases hl8 : lane.val = 8
    · by_cases hr7 : lane'.val = 7
      · let left : Fin (16 * s) := ⟨16 * j.val + 7, by have := j.isLt; omega⟩
        let right : Fin (16 * s) := ⟨16 * j.val + 8, by have := j.isLt; omega⟩
        have hsep : ∀ a b, packets left a ≠ packets right b := hdisjoint left right (by
          intro heq; have hv := congrArg Fin.val heq; simp [left, right] at hv)
        intro h
        exact dealEmbeddings_disjoint (joinPacketEmbedding (packets left) (packets right) hsep) y x
          (by simpa [eightLaneBoundaryOutputBlock, hl7, hl8, hr7, left, right] using h.symm)
      · by_cases hr8 : lane'.val = 8
        · exact False.elim (hlane (Fin.ext (hl8.trans hr8.symm)))
        · have h := eightLaneBoundaryDealtOutputBlock_disjoint_singleton
            packets hdisjoint j true lane' hr7 hr8 x y
          simpa [eightLaneBoundaryOutputBlock, hl7, hl8, hr7, hr8, bne_iff_ne] using h
    · by_cases hr7 : lane'.val = 7
      · have hr8 : lane'.val ≠ 8 := by intro h; omega
        have h := eightLaneBoundaryDealtOutputBlock_disjoint_singleton
          packets hdisjoint j false lane hl7 hl8 y x
        simpa [eightLaneBoundaryOutputBlock, hl7, hl8, hr7, bne_iff_ne] using h.symm
      · by_cases hr8 : lane'.val = 8
        · have h := eightLaneBoundaryDealtOutputBlock_disjoint_singleton
            packets hdisjoint j true lane hl7 hl8 y x
          simpa [eightLaneBoundaryOutputBlock, hl7, hl8, hr7, hr8, bne_iff_ne] using h.symm
        · let i : Fin (16 * s) := ⟨16 * j.val + lane.val, by have := j.isLt; have := lane.isLt; omega⟩
          let k : Fin (16 * s) := ⟨16 * j.val + lane'.val, by have := j.isLt; have := lane'.isLt; omega⟩
          have hne : i ≠ k := by
            intro heq
            have hv := congrArg Fin.val heq
            exact hlane (Fin.ext (by dsimp [i, k] at hv; omega))
          simpa [eightLaneBoundaryOutputBlock, hl7, hl8, hr7, hr8, i, k] using
            hdisjoint i k hne x y

theorem eightLaneBoundaryGroupedOutput_disjoint {s N : Nat}
    (packets : Fin (16 * s) → Function.Embedding (Fin 64) (Fin N))
    (hdisjoint : ∀ i j, i ≠ j → ∀ x y, packets i x ≠ packets j y)
    (hblockOrdered : ∀ i k, i.val / 8 < k.val / 8 → ∀ x y,
      packets i x < packets k y)
    (i k : Fin (16 * s)) (hik : i ≠ k) (x y : Fin 64) :
    eightLaneBoundaryGroupedOutput packets hdisjoint i x ≠
      eightLaneBoundaryGroupedOutput packets hdisjoint k y := by
  let j : Fin s := ⟨i.val / 16, by have := i.isLt; omega⟩
  let l : Fin s := ⟨k.val / 16, by have := k.isLt; omega⟩
  let lane : Fin 16 := ⟨i.val % 16, by omega⟩
  let lane' : Fin 16 := ⟨k.val % 16, by omega⟩
  have hj : j.val = i.val / 16 := rfl
  have hl : l.val = k.val / 16 := rfl
  have hLane : lane.val = i.val % 16 := rfl
  have hLane' : lane'.val = k.val % 16 := rfl
  change eightLaneBoundaryOutputBlock packets hdisjoint j lane x ≠
    eightLaneBoundaryOutputBlock packets hdisjoint l lane' y
  by_cases hsame : j.val = l.val
  · have hneLane : lane ≠ lane' := by
      intro heq
      apply hik
      apply Fin.ext
      have hi := Nat.mod_add_div i.val 16
      have hk := Nat.mod_add_div k.val 16
      have hEq := congrArg Fin.val heq
      rw [← hLane, ← hj] at hi
      rw [← hLane', ← hl, ← hsame, ← hEq] at hk
      omega
    have hjl : j = l := Fin.ext hsame
    rw [hjl]
    exact eightLaneBoundaryOutputBlock_pairwise_disjoint packets hdisjoint
      l lane lane' hneLane x y
  · rcases Nat.lt_or_gt_of_ne hsame with hlt | hgt
    · intro heq
      have hordered := eightLaneBoundaryOutputBlocks_ordered packets hdisjoint
        hblockOrdered j l hlt lane lane' x y
      exact (ne_of_lt hordered) heq
    · intro heq
      have hordered := eightLaneBoundaryOutputBlocks_ordered packets hdisjoint
        hblockOrdered l j hgt lane' lane y x
      exact (ne_of_lt hordered).symm heq

theorem eightLaneBoundaryGroupedOutput_nodup {s N : Nat}
    (packets : Fin (16 * s) → Function.Embedding (Fin 64) (Fin N))
    (hdisjoint : ∀ i j, i ≠ j → ∀ x y, packets i x ≠ packets j y)
    (hblockOrdered : ∀ i k, i.val / 8 < k.val / 8 → ∀ x y,
      packets i x < packets k y) :
    (List.ofFn (eightLaneBoundaryGroupedOutput packets hdisjoint)).Nodup := by
  apply List.nodup_ofFn_ofInjective
  intro i k heq
  by_contra hik
  have hne : i ≠ k := by simpa only [bne_iff_ne] using hik
  have hsep := eightLaneBoundaryGroupedOutput_disjoint packets hdisjoint
    hblockOrdered i k hne (0 : Fin 64) 0
  exact hsep (congrArg (fun f : Fin 64 ↪ Fin N => f 0) heq)

theorem eightLaneBoundaryGroupedOutput_perm_output {s N : Nat}
    (packets : Fin (16 * s) → Function.Embedding (Fin 64) (Fin N))
    (hdisjoint : ∀ i j, i ≠ j → ∀ x y, packets i x ≠ packets j y)
    (hblockOrdered : ∀ i k, i.val / 8 < k.val / 8 → ∀ x y,
      packets i x < packets k y) :
    List.Perm (List.ofFn (eightLaneBoundaryGroupedOutput packets hdisjoint))
      (genIndexedPacketRoundOutputWithSingletons packets hdisjoint
        (eightLaneBoundaryMatching s).edges (eightLaneBoundaryMatching s).noFixed
        (eightLaneBoundaryMatching s).singles) := by
  let grouped := List.ofFn (eightLaneBoundaryGroupedOutput packets hdisjoint)
  let matching := eightLaneBoundaryMatching s
  let output := genIndexedPacketRoundOutputWithSingletons packets hdisjoint
    matching.edges matching.noFixed matching.singles
  have hnodup : grouped.Nodup := by
    simpa [grouped] using eightLaneBoundaryGroupedOutput_nodup
      packets hdisjoint hblockOrdered
  have hsub : grouped ⊆ output := by
    intro p hp
    simp only [grouped, List.mem_ofFn] at hp
    obtain ⟨i, rfl⟩ := hp
    change eightLaneBoundaryOutputBlock packets hdisjoint
      ⟨i.val / 16, by have := i.isLt; omega⟩
      ⟨i.val % 16, by omega⟩ ∈ output
    simpa [output, matching] using eightLaneBoundaryOutputBlock_mem packets hdisjoint
      ⟨i.val / 16, by have := i.isLt; omega⟩
      ⟨i.val % 16, by omega⟩
  have hmatchedLen :
      (genIndexedPacketRoundOutput packets hdisjoint matching.edges matching.noFixed).length =
        2 * matching.edges.length := by
    have hsum : ∀ xs : List {e // e ∈ matching.edges},
        (xs.map fun _ => 2).sum = 2 * xs.length := by
      intro xs
      induction xs with
      | nil => simp
      | cons e xs ih => simp only [List.map_cons, List.sum_cons, List.length_cons]; rw [ih]; omega
    simpa [genIndexedPacketRoundOutput, genPacketRound_outputPackets,
      genIndexedPairSupports, List.length_flatMap, Function.comp_def] using
      hsum matching.edges.attach
  have hlen : output.length = 16 * s := by
    calc
      output.length = 2 * matching.edges.length + matching.singles.length := by
        simp [output, genIndexedPacketRoundOutputWithSingletons,
          List.length_append, List.length_map, hmatchedLen]
      _ = 16 * s := matching.count
  have hpermSub := hnodup.subperm hsub
  have hgroupedLen : grouped.length = 16 * s := by simp [grouped]
  exact List.Subperm.perm_of_length_le hpermSub (by rw [hlen, hgroupedLen])

theorem eightLaneBoundaryGroupedOutput_support_eq {s N : Nat} {α : Type}
    [LinearOrder α]
    (packets : Fin (16 * s) → Function.Embedding (Fin 64) (Fin N))
    (hdisjoint : ∀ i j, i ≠ j → ∀ x y, packets i x ≠ packets j y)
    (hblockOrdered : ∀ i k, i.val / 8 < k.val / 8 → ∀ x y,
      packets i x < packets k y)
    (v : Fin N → α)
    (hsorted : ∀ i, Monotone (fun x => v (packets i x))) :
    Finset.univ.biUnion (fun i => packetEmbeddingSupport
      (eightLaneBoundaryGroupedOutput packets hdisjoint i)) =
    Finset.univ.biUnion (fun i => packetEmbeddingSupport (packets i)) := by
  let matching := eightLaneBoundaryMatching s
  have hsingleDisjoint : List.Pairwise
      (fun i k => ∀ x y, packets i x ≠ packets k y) matching.singles := by
    have haux : ∀ ids : List (Fin (16 * s)),
        List.Pairwise (fun i k => i ≠ k) ids →
        List.Pairwise (fun i k => ∀ x y, packets i x ≠ packets k y) ids := by
      intro ids hids
      induction ids with
      | nil => simp
      | cons i ids ih =>
          rcases List.pairwise_cons.mp hids with ⟨hhead, htail⟩
          apply List.pairwise_cons.mpr
          constructor
          · intro k hk x y
            exact hdisjoint i k (hhead k hk) x y
          · exact ih htail
    exact haux matching.singles matching.singleDisjoint
  have hcontract := genIndexedPacketRound_withSingletons_contract
    packets hdisjoint matching.edges matching.nodup matching.noFixed
    matching.vertexDisjoint matching.singles hsingleDisjoint matching.free
    matching.covers v hsorted
  have hperm := eightLaneBoundaryGroupedOutput_perm_output packets hdisjoint hblockOrdered
  ext w
  simp only [Finset.mem_biUnion, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨i, hi⟩
    have hm : eightLaneBoundaryGroupedOutput packets hdisjoint i ∈
        List.ofFn (eightLaneBoundaryGroupedOutput packets hdisjoint) :=
      List.mem_ofFn.mpr ⟨i, rfl⟩
    have hm' : eightLaneBoundaryGroupedOutput packets hdisjoint i ∈
        genIndexedPacketRoundOutputWithSingletons packets hdisjoint
          matching.edges matching.noFixed matching.singles := hperm.mem_iff.mp hm
    obtain ⟨k, hk⟩ := (hcontract.2.2 w).mp
      ⟨_, hm', (packetEmbeddingSupport_mem_iff _ _).mp hi⟩
    exact ⟨k, (packetEmbeddingSupport_mem_iff _ _).mpr hk⟩
  · intro hi
    obtain ⟨k, hk⟩ := hi
    obtain ⟨p, hp, hw⟩ := (hcontract.2.2 w).mpr
      ⟨k, (packetEmbeddingSupport_mem_iff _ _).mp hk⟩
    have hm : p ∈ List.ofFn (eightLaneBoundaryGroupedOutput packets hdisjoint) :=
      hperm.mem_iff.mpr hp
    obtain ⟨i, hpi⟩ := List.mem_ofFn.mp hm
    exact ⟨i, (packetEmbeddingSupport_mem_iff _ _).mpr (hpi ▸ hw)⟩

/-- The two untouched outer packets are members of the singleton-augmented
output family of the same round. -/
theorem genIndexedPacketRound_singleton_mem_output {m N : Nat}
    (packets : Fin m -> Function.Embedding (Fin 64) (Fin N))
    (hdisjoint : forall i j, Not (i = j) -> forall x y, Not (packets i x = packets j y))
    (edges : List (Prod (Fin m) (Fin m)))
    (hnoFixed : forall e, List.Mem e edges -> Not (e.1 = e.2))
    (singles : List (Fin m)) (i : Fin m) (hi : List.Mem i singles) :
    List.Mem (packets i)
      (genIndexedPacketRoundOutputWithSingletons packets hdisjoint edges hnoFixed singles) := by
  apply List.mem_append.mpr
  apply Or.inr
  apply List.mem_map.mpr
  exact Exists.intro i (And.intro hi rfl)

def fourLaneBoundaryOutputBlock {s N : Nat}
    (packets : Fin (8 * s) -> Function.Embedding (Fin 64) (Fin N))
    (hdisjoint : forall i j, Not (i = j) -> forall x y, Not (packets i x = packets j y))
    (j : Fin s) (lane : Fin 8) : Function.Embedding (Fin 64) (Fin N) :=
  let left : Fin (8 * s) := Fin.mk (8 * j.val + 3) (by omega)
  let right : Fin (8 * s) := Fin.mk (8 * j.val + 4) (by omega)
  let joined := joinPacketEmbedding (packets left) (packets right) (hdisjoint left right (by
    intro heq
    have hv := congrArg Fin.val heq
    simp [left, right] at hv))
  if lane.val = 3 then dealEvenEmbedding joined
  else if lane.val = 4 then dealOddEmbedding joined
  else packets (Fin.mk (8 * j.val + lane.val) (by omega))

theorem fourLaneBoundaryOutputBlock_mem {s N : Nat}
    (packets : Fin (8 * s) -> Function.Embedding (Fin 64) (Fin N))
    (hdisjoint : forall i j, Not (i = j) -> forall x y, Not (packets i x = packets j y))
    (j : Fin s) (lane : Fin 8) :
    List.Mem (fourLaneBoundaryOutputBlock packets hdisjoint j lane)
      (genIndexedPacketRoundOutputWithSingletons packets hdisjoint
        (fourLaneBoundaryMatching s).edges (fourLaneBoundaryMatching s).noFixed
        (fourLaneBoundaryMatching s).singles) := by
  let left : Fin (8 * s) := Fin.mk (8 * j.val + 3) (by omega)
  let right : Fin (8 * s) := Fin.mk (8 * j.val + 4) (by omega)
  let joined := joinPacketEmbedding (packets left) (packets right) (hdisjoint left right (by
    intro heq
    have hv := congrArg Fin.val heq
    simp [left, right] at hv))
  by_cases h3 : lane.val = 3
  case pos =>
    have hraw := fourLaneBoundaryMatching_dealt_mem_output packets hdisjoint j false
    have hdealt : List.Mem (dealEvenEmbedding joined)
        (genIndexedPacketRoundOutput packets hdisjoint
          (fourLaneBoundaryMatching s).edges (fourLaneBoundaryMatching s).noFixed) := by
      simpa [joined, left, right] using hraw
    simp only [fourLaneBoundaryOutputBlock, h3]
    exact List.mem_append.mpr (Or.inl hdealt)
  case neg =>
    by_cases h4 : lane.val = 4
    case pos =>
      have hraw := fourLaneBoundaryMatching_dealt_mem_output packets hdisjoint j true
      have hdealt : List.Mem (dealOddEmbedding joined)
          (genIndexedPacketRoundOutput packets hdisjoint
            (fourLaneBoundaryMatching s).edges (fourLaneBoundaryMatching s).noFixed) := by
        simpa [joined, left, right] using hraw
      simp only [fourLaneBoundaryOutputBlock, h3, h4]
      exact List.mem_append.mpr (Or.inl hdealt)
    case neg =>
      let i : Fin (8 * s) := Fin.mk (8 * j.val + lane.val) (by omega)
      have h3i : Not (i.val % 8 = 3) := by simp [i]; omega
      have h4i : Not (i.val % 8 = 4) := by simp [i]; omega
      have his := fourLaneBoundarySingleton_mem_of_nonedge i h3i h4i
      have hsingle := genIndexedPacketRound_singleton_mem_output packets hdisjoint
        (fourLaneBoundaryMatching s).edges (fourLaneBoundaryMatching s).noFixed
        (fourLaneBoundaryMatching s).singles i his
      simpa [fourLaneBoundaryOutputBlock, h3, h4, i] using hsingle

/-- The eight output lanes draw only from their corresponding eight-packet
input block. This is the support bridge needed to compose repeated stages. -/
theorem fourLaneBoundaryOutputBlock_range {s N : Nat}
    (packets : Fin (8 * s) -> Function.Embedding (Fin 64) (Fin N))
    (hdisjoint : forall i j, Not (i = j) -> forall x y, Not (packets i x = packets j y))
    (j : Fin s) (lane : Fin 8) (x : Fin 64) :
    Exists fun i : Fin (8 * s) => i.val / 8 = j.val /\
      Set.range (packets i) (fourLaneBoundaryOutputBlock packets hdisjoint j lane x) := by
  let left : Fin (8 * s) := Fin.mk (8 * j.val + 3) (by omega)
  let right : Fin (8 * s) := Fin.mk (8 * j.val + 4) (by omega)
  have hsep : forall a b, Not (packets left a = packets right b) := hdisjoint left right (by
    intro h
    have hv := congrArg Fin.val h
    simp [left, right] at hv)
  have hjoined : forall w, Set.range (joinPacketEmbedding (packets left) (packets right) hsep) w ->
      Set.range (packets left) w \/ Set.range (packets right) w := by
    intro w hw
    rw [joinPacketEmbedding_range _ _ hsep] at hw
    exact hw
  by_cases h3 : lane.val = 3
  · have hw : Set.range (joinPacketEmbedding (packets left) (packets right) hsep)
        (dealEvenEmbedding (joinPacketEmbedding (packets left) (packets right) hsep) x) :=
      Exists.intro (evenWire 64 x) rfl
    obtain hw | hw := hjoined _ hw
    · obtain ⟨z, hz⟩ := hw
      exact Exists.intro left ⟨by simp [left]; omega, Exists.intro z (by simpa [fourLaneBoundaryOutputBlock, h3, left, right] using hz)⟩
    · obtain ⟨z, hz⟩ := hw
      exact Exists.intro right ⟨by simp [right]; omega, Exists.intro z (by simpa [fourLaneBoundaryOutputBlock, h3, left, right] using hz)⟩
  · by_cases h4 : lane.val = 4
    · have hw : Set.range (joinPacketEmbedding (packets left) (packets right) hsep)
          (dealOddEmbedding (joinPacketEmbedding (packets left) (packets right) hsep) x) :=
        Exists.intro (oddWire 64 x) rfl
      obtain hw | hw := hjoined _ hw
      · obtain ⟨z, hz⟩ := hw
        exact Exists.intro left ⟨by simp [left]; omega, Exists.intro z (by simpa [fourLaneBoundaryOutputBlock, h3, h4, left, right] using hz)⟩
      · obtain ⟨z, hz⟩ := hw
        exact Exists.intro right ⟨by simp [right]; omega, Exists.intro z (by simpa [fourLaneBoundaryOutputBlock, h3, h4, left, right] using hz)⟩
    · let i : Fin (8 * s) := Fin.mk (8 * j.val + lane.val) (by omega)
      refine Exists.intro i ⟨?_, ?_⟩
      · simp [i]
        omega
      · have hv : Not (i.val % 8 = 3) /\ Not (i.val % 8 = 4) := by
          simp [i]
          omega
        have hsingle := fourLaneBoundarySingleton_mem_of_nonedge i hv.1 hv.2
        have houtput := genIndexedPacketRound_singleton_mem_output packets hdisjoint
          (fourLaneBoundaryMatching s).edges (fourLaneBoundaryMatching s).noFixed
          (fourLaneBoundaryMatching s).singles i hsingle
        exact Exists.intro x (by simpa [fourLaneBoundaryOutputBlock, h3, h4, i] using rfl)

/-- Distinct eight-packet blocks remain strictly ordered after the boundary
round, assuming the previous four-packet blocks were strictly ordered. -/
theorem fourLaneBoundaryDealtOutputBlock_range {s N : Nat}
    (packets : Fin (8 * s) -> Function.Embedding (Fin 64) (Fin N))
    (hdisjoint : forall i j, Not (i = j) -> forall x y, Not (packets i x = packets j y))
    (j : Fin s) (odd : Bool) (x : Fin 64) :
    Exists fun i : Fin (8 * s) =>
      (i.val = 8 * j.val + 3 \/ i.val = 8 * j.val + 4) /\
      Set.range (packets i) ((if odd then
        dealOddEmbedding (joinPacketEmbedding
          (packets (Fin.mk (8 * j.val + 3) (by omega)))
          (packets (Fin.mk (8 * j.val + 4) (by omega))) (by
            intro a b h
            exact hdisjoint _ _ (by
              intro hne
              have hv := congrArg Fin.val hne
              simp at hv) a b h))
      else
        dealEvenEmbedding (joinPacketEmbedding
          (packets (Fin.mk (8 * j.val + 3) (by omega)))
          (packets (Fin.mk (8 * j.val + 4) (by omega))) (by
            intro a b h
            exact hdisjoint _ _ (by
              intro hne
              have hv := congrArg Fin.val hne
              simp at hv) a b h))) x) := by
  let left : Fin (8 * s) := Fin.mk (8 * j.val + 3) (by omega)
  let right : Fin (8 * s) := Fin.mk (8 * j.val + 4) (by omega)
  have hsep : forall a b, Not (packets left a = packets right b) := hdisjoint left right (by
    intro h
    have hv := congrArg Fin.val h
    simp [left, right] at hv)
  let joined := joinPacketEmbedding (packets left) (packets right) hsep
  change Exists fun i : Fin (8 * s) =>
    (i.val = 8 * j.val + 3 \/ i.val = 8 * j.val + 4) /\
      Set.range (packets i) ((if odd then dealOddEmbedding joined else dealEvenEmbedding joined) x)
  have hmem : Set.range joined ((if odd then dealOddEmbedding joined else dealEvenEmbedding joined) x) := by
    refine Exists.intro (if odd then oddWire 64 x else evenWire 64 x) ?_
    cases odd <;> rfl
  rw [joinPacketEmbedding_range _ _ hsep] at hmem
  rcases hmem with hmem | hmem
  · exact Exists.intro left (And.intro (Or.inl (by simp [left])) hmem)
  · exact Exists.intro right (And.intro (Or.inr (by simp [right])) hmem)

theorem fourLaneBoundaryDealtOutputBlock_disjoint_singleton {s N : Nat}
    (packets : Fin (8 * s) -> Function.Embedding (Fin 64) (Fin N))
    (hdisjoint : forall i j, Not (i = j) -> forall x y, Not (packets i x = packets j y))
    (j : Fin s) (odd : Bool) (lane : Fin 8)
    (h3 : Not (lane.val = 3)) (h4 : Not (lane.val = 4)) (x y : Fin 64) :
    (if odd then
      dealOddEmbedding (joinPacketEmbedding
        (packets (Fin.mk (8 * j.val + 3) (by omega)))
        (packets (Fin.mk (8 * j.val + 4) (by omega))) (by
          intro a b h
          exact hdisjoint _ _ (by
            intro hne
            have hv := congrArg Fin.val hne
            simp at hv) a b h))
    else
      dealEvenEmbedding (joinPacketEmbedding
        (packets (Fin.mk (8 * j.val + 3) (by omega)))
        (packets (Fin.mk (8 * j.val + 4) (by omega))) (by
          intro a b h
          exact hdisjoint _ _ (by
            intro hne
            have hv := congrArg Fin.val hne
            simp at hv) a b h))) x !=
      packets (Fin.mk (8 * j.val + lane.val) (by omega)) y := by
  simp only [bne_iff_ne]
  obtain ⟨i, hi, hmem⟩ := fourLaneBoundaryDealtOutputBlock_range
    packets hdisjoint j odd x
  obtain ⟨z, hz⟩ := hmem
  let singleton : Fin (8 * s) := Fin.mk (8 * j.val + lane.val) (by omega)
  have hne : Not (i = singleton) := by
    intro heq
    have hv := congrArg Fin.val heq
    rcases hi with hi | hi <;> simp [singleton] at hv <;> omega
  have hsource := hdisjoint i singleton hne z y
  intro h
  apply hsource
  rw [hz, h]

theorem fourLaneBoundaryOutputBlock_pairwise_disjoint {s N : Nat}
    (packets : Fin (8 * s) -> Function.Embedding (Fin 64) (Fin N))
    (hdisjoint : forall i j, Not (i = j) -> forall x y, Not (packets i x = packets j y))
    (j : Fin s) (lane lane' : Fin 8) (hlane : lane != lane') (x y : Fin 64) :
    fourLaneBoundaryOutputBlock packets hdisjoint j lane x !=
      fourLaneBoundaryOutputBlock packets hdisjoint j lane' y := by
  simp only [bne_iff_ne] at hlane ⊢
  by_cases hl3 : lane.val = 3
  · by_cases hr3 : lane'.val = 3
    · have heq : lane = lane' := Fin.ext (hl3.trans hr3.symm)
      exact False.elim (hlane heq)
    · by_cases hr4 : lane'.val = 4
      · let left : Fin (8 * s) := Fin.mk (8 * j.val + 3) (by omega)
        let right : Fin (8 * s) := Fin.mk (8 * j.val + 4) (by omega)
        have hsep : forall a b, Not (packets left a = packets right b) := hdisjoint left right (by
          intro h
          have hv := congrArg Fin.val h
          simp [left, right] at hv)
        simpa [fourLaneBoundaryOutputBlock, hl3, hr3, hr4, left, right] using
          dealEmbeddings_disjoint (joinPacketEmbedding (packets left) (packets right) hsep) x y
      · have hl4 : Not (lane.val = 4) := by intro h; omega
        simpa [fourLaneBoundaryOutputBlock, hl3, hr3, hr4, bne_iff_ne] using
          fourLaneBoundaryDealtOutputBlock_disjoint_singleton
            packets hdisjoint j false lane' hr3 hr4 x y
  · by_cases hl4 : lane.val = 4
    · by_cases hr3 : lane'.val = 3
      · let left : Fin (8 * s) := Fin.mk (8 * j.val + 3) (by omega)
        let right : Fin (8 * s) := Fin.mk (8 * j.val + 4) (by omega)
        have hsep : forall a b, Not (packets left a = packets right b) := hdisjoint left right (by
          intro h
          have hv := congrArg Fin.val h
          simp [left, right] at hv)
        intro h
        apply (dealEmbeddings_disjoint
          (joinPacketEmbedding (packets left) (packets right) hsep) y x)
        simpa [fourLaneBoundaryOutputBlock, hl3, hl4, hr3, left, right] using h.symm
      · by_cases hr4 : lane'.val = 4
        · have heq : lane = lane' := Fin.ext (hl4.trans hr4.symm)
          exact False.elim (hlane heq)
        · simpa [fourLaneBoundaryOutputBlock, hl3, hl4, hr3, hr4, bne_iff_ne] using
            fourLaneBoundaryDealtOutputBlock_disjoint_singleton
              packets hdisjoint j true lane' hr3 hr4 x y
    · by_cases hr3 : lane'.val = 3
      · intro h
        have hcross : Not (dealEvenEmbedding (joinPacketEmbedding
            (packets (Fin.mk (8 * j.val + 3) (by omega)))
            (packets (Fin.mk (8 * j.val + 4) (by omega))) (by
              intro a b hab
              exact hdisjoint _ _ (by
                intro hn
                have hv := congrArg Fin.val hn
                simp at hv) a b hab)) y =
            packets (Fin.mk (8 * j.val + lane.val) (by omega)) x) := by
          simpa only [bne_iff_ne] using
            fourLaneBoundaryDealtOutputBlock_disjoint_singleton
              packets hdisjoint j false lane hl3 hl4 y x
        exact hcross (by simpa [fourLaneBoundaryOutputBlock, hl3, hl4, hr3] using h.symm)
      · by_cases hr4 : lane'.val = 4
        · intro h
          have hcross : Not (dealOddEmbedding (joinPacketEmbedding
              (packets (Fin.mk (8 * j.val + 3) (by omega)))
              (packets (Fin.mk (8 * j.val + 4) (by omega))) (by
                intro a b hab
                exact hdisjoint _ _ (by
                  intro hn
                  have hv := congrArg Fin.val hn
                  simp at hv) a b hab)) y =
              packets (Fin.mk (8 * j.val + lane.val) (by omega)) x) := by
            simpa only [bne_iff_ne] using
              fourLaneBoundaryDealtOutputBlock_disjoint_singleton
                packets hdisjoint j true lane hl3 hl4 y x
          exact hcross (by simpa [fourLaneBoundaryOutputBlock, hl3, hl4, hr3, hr4] using h.symm)
        · let i : Fin (8 * s) := Fin.mk (8 * j.val + lane.val) (by omega)
          let k : Fin (8 * s) := Fin.mk (8 * j.val + lane'.val) (by omega)
          have hindex : Not (i = k) := by
            intro h
            have hv := congrArg Fin.val h
            exact hlane (Fin.ext (by dsimp [i, k] at hv ⊢; omega))
          simpa [fourLaneBoundaryOutputBlock, hl3, hl4, hr3, hr4, i, k] using
            hdisjoint i k hindex x y

theorem fourLaneBoundaryOutputBlocks_ordered {s N : Nat}
    (packets : Fin (8 * s) -> Function.Embedding (Fin 64) (Fin N))
    (hdisjoint : forall i j, Not (i = j) -> forall x y, Not (packets i x = packets j y))
    (hblockOrdered : forall i k, i.val / 4 < k.val / 4 -> forall x y,
      packets i x < packets k y)
    (j l : Fin s) (hjl : j.val < l.val) (lane lane' : Fin 8) (x y : Fin 64) :
    fourLaneBoundaryOutputBlock packets hdisjoint j lane x <
      fourLaneBoundaryOutputBlock packets hdisjoint l lane' y := by
  obtain ⟨i, ⟨hi, hix⟩⟩ := fourLaneBoundaryOutputBlock_range
    packets hdisjoint j lane x
  obtain ⟨k, ⟨hk, hky⟩⟩ := fourLaneBoundaryOutputBlock_range
    packets hdisjoint l lane' y
  obtain ⟨u, hu⟩ := hix
  obtain ⟨v, hv⟩ := hky
  calc
    _ = packets i u := hu.symm
    _ < packets k v := hblockOrdered i k (by
      have hi' := i.isLt
      have hk' := k.isLt
      omega) u v
    _ = _ := hv

/-- Each lane is sorted by the round and remains increasing in physical wire
order. This is the local invariant required before the next merge stage. -/
theorem fourLaneBoundaryOutputBlock_lane_contract {s N : Nat} {alpha : Type}
    [LinearOrder alpha]
    (packets : Fin (8 * s) -> Function.Embedding (Fin 64) (Fin N))
    (hdisjoint : forall i j, Not (i = j) -> forall x y, Not (packets i x = packets j y))
    (hpacketMono : forall i, StrictMono (packets i))
    (hblockOrdered : forall i k, i.val / 4 < k.val / 4 -> forall x y,
      packets i x < packets k y)
    (v : Fin N -> alpha)
    (hsorted : forall i, Monotone (fun x => v (packets i x)))
    (j : Fin s) (lane : Fin 8) :
    Monotone (fun x =>
      (genIndexedPacketRound packets hdisjoint
        (fourLaneBoundaryMatching s).edges
        (fourLaneBoundaryMatching s).noFixed).exec v
        (fourLaneBoundaryOutputBlock packets hdisjoint j lane x)) /\
    StrictMono (fourLaneBoundaryOutputBlock packets hdisjoint j lane) := by
  let matching := fourLaneBoundaryMatching s
  have hsingleDisjoint : List.Pairwise
      (fun i k : Fin (8 * s) => forall x y, Not (packets i x = packets k y))
      matching.singles := by
    have haux : forall ids : List (Fin (8 * s)),
        List.Pairwise (fun i k => Not (i = k)) ids ->
        List.Pairwise (fun i k => forall x y, Not (packets i x = packets k y)) ids := by
      intro ids hids
      induction ids with
      | nil => simp
      | cons i ids ih =>
          rcases List.pairwise_cons.mp hids with ⟨hhead, htail⟩
          apply List.pairwise_cons.mpr
          constructor
          · intro k hk x y
            exact hdisjoint i k (hhead k hk) x y
          · exact ih htail
    exact haux matching.singles matching.singleDisjoint
  have hsortedOut := genIndexedPacketRound_withSingletons_contract
    packets hdisjoint matching.edges matching.nodup matching.noFixed
    matching.vertexDisjoint matching.singles hsingleDisjoint matching.free
    matching.covers v hsorted
  have hmonoOut := genIndexedPacketRound_withSingletons_output_strictMono
    packets hdisjoint matching.edges matching.noFixed matching.singles
    hpacketMono (fourLaneBoundaryMatching_ordered packets hblockOrdered)
  have hmem := fourLaneBoundaryOutputBlock_mem packets hdisjoint j lane
  exact ⟨hsortedOut.1 _ hmem, hmonoOut _ hmem⟩

/-- The eight output lanes partition exactly the support of the eight input
packets in their macroblock. -/
theorem fourLaneBoundaryOutputBlock_support_eq {s N : Nat}
    (packets : Fin (8 * s) -> Function.Embedding (Fin 64) (Fin N))
    (hdisjoint : forall i j, Not (i = j) -> forall x y, Not (packets i x = packets j y))
    (j : Fin s) :
    ((Set.range (fourLaneBoundaryOutputBlock packets hdisjoint j 0) ∪
      Set.range (fourLaneBoundaryOutputBlock packets hdisjoint j 1) ∪
      Set.range (fourLaneBoundaryOutputBlock packets hdisjoint j 2)) ∪
      (Set.range (fourLaneBoundaryOutputBlock packets hdisjoint j 3) ∪
        Set.range (fourLaneBoundaryOutputBlock packets hdisjoint j 4)) ∪
      (Set.range (fourLaneBoundaryOutputBlock packets hdisjoint j 5) ∪
        Set.range (fourLaneBoundaryOutputBlock packets hdisjoint j 6) ∪
        Set.range (fourLaneBoundaryOutputBlock packets hdisjoint j 7))) =
    ((Set.range (packets (Fin.mk (8 * j.val) (by omega))) ∪
      Set.range (packets (Fin.mk (8 * j.val + 1) (by omega))) ∪
      Set.range (packets (Fin.mk (8 * j.val + 2) (by omega)))) ∪
      (Set.range (packets (Fin.mk (8 * j.val + 3) (by omega))) ∪
        Set.range (packets (Fin.mk (8 * j.val + 4) (by omega)))) ∪
      (Set.range (packets (Fin.mk (8 * j.val + 5) (by omega))) ∪
        Set.range (packets (Fin.mk (8 * j.val + 6) (by omega))) ∪
        Set.range (packets (Fin.mk (8 * j.val + 7) (by omega))))) := by
  let left : Fin (8 * s) := Fin.mk (8 * j.val + 3) (by omega)
  let right : Fin (8 * s) := Fin.mk (8 * j.val + 4) (by omega)
  have hsep : forall x y, Not (packets left x = packets right y) := hdisjoint left right (by
    intro h
    have hv := congrArg Fin.val h
    simp [left, right] at hv)
  let joined := joinPacketEmbedding (packets left) (packets right) hsep
  change ((Set.range (packets (Fin.mk (8 * j.val) (by omega))) ∪
      Set.range (packets (Fin.mk (8 * j.val + 1) (by omega))) ∪
      Set.range (packets (Fin.mk (8 * j.val + 2) (by omega)))) ∪
      (Set.range (dealEvenEmbedding joined) ∪ Set.range (dealOddEmbedding joined)) ∪
      (Set.range (packets (Fin.mk (8 * j.val + 5) (by omega))) ∪
        Set.range (packets (Fin.mk (8 * j.val + 6) (by omega))) ∪
        Set.range (packets (Fin.mk (8 * j.val + 7) (by omega))))) = _
  rw [dealEmbeddings_partition joined, joinPacketEmbedding_range _ _ hsep]

/-- Flatten the proposed eight-lane macroblocks in block-major order. -/
def fourLaneBoundaryGroupedOutput {s N : Nat}
    (packets : Fin (8 * s) -> Function.Embedding (Fin 64) (Fin N))
    (hdisjoint : forall i j, Not (i = j) -> forall x y, Not (packets i x = packets j y))
    (i : Fin (8 * s)) : Function.Embedding (Fin 64) (Fin N) :=
  let j : Fin s := Fin.mk (i.val / 8) (by have := i.isLt; omega)
  let lane : Fin 8 := Fin.mk (i.val % 8) (by omega)
  fourLaneBoundaryOutputBlock packets hdisjoint j lane

/-- Decoding the flat block-major index recovers the advertised block/lane. -/
theorem fourLaneBoundaryGroupedOutput_at {s N : Nat}
    (packets : Fin (8 * s) -> Function.Embedding (Fin 64) (Fin N))
    (hdisjoint : forall i j, Not (i = j) -> forall x y, Not (packets i x = packets j y))
    (j : Fin s) (lane : Fin 8) :
    fourLaneBoundaryGroupedOutput packets hdisjoint
      (Fin.mk (8 * j.val + lane.val) (by omega)) =
      fourLaneBoundaryOutputBlock packets hdisjoint j lane := by
  apply Function.Embedding.ext
  intro x
  simp only [fourLaneBoundaryGroupedOutput]
  have hlane := lane.isLt
  let n := 8 * j.val + lane.val
  have hmod : n % 8 = lane.val := by simp [n, Nat.add_mod, Nat.mod_eq_of_lt hlane]
  have hdiv : n / 8 = j.val := by
    have hid := Nat.mod_add_div n 8
    rw [hmod] at hid
    dsimp [n] at hid
    omega
  have hj : (Fin.mk (n / 8) (by rw [hdiv]; exact j.isLt) : Fin s) = j := Fin.ext hdiv
  have hl : (Fin.mk (n % 8) (by rw [hmod]; exact hlane) : Fin 8) = lane := Fin.ext hmod
  rw [hj, hl]

theorem fourLaneBoundaryGroupedOutput_mem {s N : Nat}
    (packets : Fin (8 * s) -> Function.Embedding (Fin 64) (Fin N))
    (hdisjoint : forall i j, Not (i = j) -> forall x y, Not (packets i x = packets j y))
    (i : Fin (8 * s)) :
    List.Mem (fourLaneBoundaryGroupedOutput packets hdisjoint i)
      (genIndexedPacketRoundOutputWithSingletons packets hdisjoint
        (fourLaneBoundaryMatching s).edges (fourLaneBoundaryMatching s).noFixed
        (fourLaneBoundaryMatching s).singles) := by
  let j : Fin s := Fin.mk (i.val / 8) (by have := i.isLt; omega)
  let lane : Fin 8 := Fin.mk (i.val % 8) (by omega)
  change List.Mem (fourLaneBoundaryOutputBlock packets hdisjoint j lane) _
  exact fourLaneBoundaryOutputBlock_mem packets hdisjoint j lane

theorem fourLaneBoundaryGroupedOutput_lane_contract {s N : Nat} {alpha : Type}
    [LinearOrder alpha]
    (packets : Fin (8 * s) -> Function.Embedding (Fin 64) (Fin N))
    (hdisjoint : forall i j, Not (i = j) -> forall x y, Not (packets i x = packets j y))
    (hpacketMono : forall i, StrictMono (packets i))
    (hblockOrdered : forall i k, i.val / 4 < k.val / 4 -> forall x y,
      packets i x < packets k y)
    (v : Fin N -> alpha)
    (hsorted : forall i, Monotone (fun x => v (packets i x)))
    (i : Fin (8 * s)) :
    Monotone (fun x =>
      (genIndexedPacketRound packets hdisjoint
        (fourLaneBoundaryMatching s).edges
        (fourLaneBoundaryMatching s).noFixed).exec v
        (fourLaneBoundaryGroupedOutput packets hdisjoint i x)) /\
    StrictMono (fourLaneBoundaryGroupedOutput packets hdisjoint i) := by
  let j : Fin s := Fin.mk (i.val / 8) (by have := i.isLt; omega)
  let lane : Fin 8 := Fin.mk (i.val % 8) (by omega)
  change Monotone (fun x =>
      (genIndexedPacketRound packets hdisjoint
        (fourLaneBoundaryMatching s).edges
        (fourLaneBoundaryMatching s).noFixed).exec v
        (fourLaneBoundaryOutputBlock packets hdisjoint j lane x)) /\
    StrictMono (fourLaneBoundaryOutputBlock packets hdisjoint j lane)
  exact fourLaneBoundaryOutputBlock_lane_contract packets hdisjoint hpacketMono
    hblockOrdered v hsorted j lane

/-- The flattened output array is strictly physically ordered across distinct
eight-packet macroblocks. -/
theorem fourLaneBoundaryGroupedOutput_ordered {s N : Nat}
    (packets : Fin (8 * s) -> Function.Embedding (Fin 64) (Fin N))
    (hdisjoint : forall i j, Not (i = j) -> forall x y, Not (packets i x = packets j y))
    (hblockOrdered : forall i k, i.val / 4 < k.val / 4 -> forall x y,
      packets i x < packets k y)
    (i k : Fin (8 * s)) (hblock : i.val / 8 < k.val / 8)
    (x y : Fin 64) :
    fourLaneBoundaryGroupedOutput packets hdisjoint i x <
      fourLaneBoundaryGroupedOutput packets hdisjoint k y := by
  let j : Fin s := Fin.mk (i.val / 8) (by have := i.isLt; omega)
  let l : Fin s := Fin.mk (k.val / 8) (by have := k.isLt; omega)
  let lane : Fin 8 := Fin.mk (i.val % 8) (by omega)
  let lane' : Fin 8 := Fin.mk (k.val % 8) (by omega)
  have hjl : j.val < l.val := hblock
  change fourLaneBoundaryOutputBlock packets hdisjoint j lane x <
    fourLaneBoundaryOutputBlock packets hdisjoint l lane' y
  exact fourLaneBoundaryOutputBlocks_ordered packets hdisjoint hblockOrdered
    j l hjl lane lane' x y

/-- Outputs from distinct macroblocks have disjoint physical supports. -/
theorem fourLaneBoundaryGroupedOutput_disjoint_of_block_ne {s N : Nat}
    (packets : Fin (8 * s) -> Function.Embedding (Fin 64) (Fin N))
    (hdisjoint : forall i j, Not (i = j) -> forall x y, Not (packets i x = packets j y))
    (hblockOrdered : forall i k, i.val / 4 < k.val / 4 -> forall x y,
      packets i x < packets k y)
    (i k : Fin (8 * s)) (hblock : Not (i.val / 8 = k.val / 8))
    (x y : Fin 64) :
    fourLaneBoundaryGroupedOutput packets hdisjoint i x ≠
      fourLaneBoundaryGroupedOutput packets hdisjoint k y := by
  rcases Nat.lt_or_gt_of_ne hblock with hlt | hgt
  · exact ne_of_lt (fourLaneBoundaryGroupedOutput_ordered packets hdisjoint
      hblockOrdered i k hlt x y)
  · exact (ne_of_lt (fourLaneBoundaryGroupedOutput_ordered packets hdisjoint
      hblockOrdered k i hgt y x)).symm

theorem fourLaneBoundaryGroupedOutput_disjoint {s N : Nat}
    (packets : Fin (8 * s) -> Function.Embedding (Fin 64) (Fin N))
    (hdisjoint : forall i j, Not (i = j) -> forall x y, Not (packets i x = packets j y))
    (hblockOrdered : forall i k, i.val / 4 < k.val / 4 -> forall x y,
      packets i x < packets k y)
    (i k : Fin (8 * s)) (hik : i != k) (x y : Fin 64) :
    fourLaneBoundaryGroupedOutput packets hdisjoint i x !=
      fourLaneBoundaryGroupedOutput packets hdisjoint k y := by
  simp only [bne_iff_ne] at hik ⊢
  by_cases hlt : i.val / 8 < k.val / 8
  · exact ne_of_lt (fourLaneBoundaryGroupedOutput_ordered packets hdisjoint
      hblockOrdered i k hlt x y)
  · by_cases hgt : k.val / 8 < i.val / 8
    · exact (ne_of_lt (fourLaneBoundaryGroupedOutput_ordered packets hdisjoint
        hblockOrdered k i hgt y x)).symm
    · have hblock : i.val / 8 = k.val / 8 := by omega
      let j : Fin s := Fin.mk (i.val / 8) (by have := i.isLt; omega)
      let l : Fin s := Fin.mk (k.val / 8) (by have := k.isLt; omega)
      let lane : Fin 8 := Fin.mk (i.val % 8) (by omega)
      let lane' : Fin 8 := Fin.mk (k.val % 8) (by omega)
      have hjl : l = j := Fin.ext hblock.symm
      have hiVal : i.val = 8 * j.val + lane.val := by
        dsimp [j, lane]
        have hd := Nat.mod_add_div i.val 8
        omega
      have hkVal : k.val = 8 * j.val + lane'.val := by
        dsimp [j, l, lane']
        have hd := Nat.mod_add_div k.val 8
        omega
      have hlane : lane != lane' := by
        apply bne_iff_ne.mpr
        intro heq
        have hv := congrArg Fin.val heq
        apply hik
        apply Fin.ext
        omega
      change fourLaneBoundaryOutputBlock packets hdisjoint j lane x ≠
        fourLaneBoundaryOutputBlock packets hdisjoint l lane' y
      rw [hjl]
      have hlocal := fourLaneBoundaryOutputBlock_pairwise_disjoint
        packets hdisjoint j lane lane' hlane x y
      simpa only [bne_iff_ne] using hlocal

theorem fourLaneBoundaryGroupedOutput_nodup {s N : Nat}
    (packets : Fin (8 * s) -> Function.Embedding (Fin 64) (Fin N))
    (hdisjoint : forall i j, Not (i = j) -> forall x y, Not (packets i x = packets j y))
    (hblockOrdered : forall i k, i.val / 4 < k.val / 4 -> forall x y,
      packets i x < packets k y) :
    (List.ofFn (fourLaneBoundaryGroupedOutput packets hdisjoint)).Nodup := by
  apply List.nodup_ofFn_ofInjective
  intro i k heq
  by_contra hik
  have hne : i != k := by simpa only [bne_iff_ne] using hik
  have hseparate := fourLaneBoundaryGroupedOutput_disjoint packets hdisjoint
    hblockOrdered i k hne (0 : Fin 64) 0
  have hneWire :
      fourLaneBoundaryGroupedOutput packets hdisjoint i 0 !=
        fourLaneBoundaryGroupedOutput packets hdisjoint k 0 := hseparate
  have hneProp :
      fourLaneBoundaryGroupedOutput packets hdisjoint i 0 ≠
        fourLaneBoundaryGroupedOutput packets hdisjoint k 0 := by
    simpa only [bne_iff_ne] using hneWire
  exact hneProp (congrArg (fun f : Fin 64 ↪ Fin N => f 0) heq)

theorem fourLaneBoundaryGroupedOutput_perm_output {s N : Nat}
    (packets : Fin (8 * s) -> Function.Embedding (Fin 64) (Fin N))
    (hdisjoint : forall i j, Not (i = j) -> forall x y, Not (packets i x = packets j y))
    (hblockOrdered : forall i k, i.val / 4 < k.val / 4 -> forall x y,
      packets i x < packets k y) :
    List.Perm (List.ofFn (fourLaneBoundaryGroupedOutput packets hdisjoint))
      (genIndexedPacketRoundOutputWithSingletons packets hdisjoint
        (fourLaneBoundaryMatching s).edges (fourLaneBoundaryMatching s).noFixed
        (fourLaneBoundaryMatching s).singles) := by
  let grouped := List.ofFn (fourLaneBoundaryGroupedOutput packets hdisjoint)
  let output := genIndexedPacketRoundOutputWithSingletons packets hdisjoint
    (fourLaneBoundaryMatching s).edges (fourLaneBoundaryMatching s).noFixed
    (fourLaneBoundaryMatching s).singles
  have hnodup : grouped.Nodup := by
    simpa [grouped] using fourLaneBoundaryGroupedOutput_nodup packets hdisjoint hblockOrdered
  have hsub : grouped ⊆ output := by
    intro p hp
    simp only [grouped, List.mem_ofFn] at hp
    obtain ⟨i, rfl⟩ := hp
    exact fourLaneBoundaryGroupedOutput_mem packets hdisjoint i
  have hmatchedLen :
      (genIndexedPacketRoundOutput packets hdisjoint
        (fourLaneBoundaryMatching s).edges (fourLaneBoundaryMatching s).noFixed).length =
        2 * (fourLaneBoundaryMatching s).edges.length := by
    have hsum : forall xs : List {e // e ∈ (fourLaneBoundaryMatching s).edges},
        (xs.map fun _ => 2).sum = 2 * xs.length := by
      intro xs
      induction xs with
      | nil => simp
      | cons e xs ih =>
          simp only [List.map_cons, List.sum_cons, List.length_cons]
          rw [ih]
          omega
    simpa [genIndexedPacketRoundOutput, genPacketRound_outputPackets,
      genIndexedPairSupports, List.length_flatMap, Function.comp_def] using
      hsum ((fourLaneBoundaryMatching s).edges.attach)
  have hlen : output.length = 8 * s := by
    calc
      output.length = 2 * (fourLaneBoundaryMatching s).edges.length +
          (fourLaneBoundaryMatching s).singles.length := by
        simp [output, genIndexedPacketRoundOutputWithSingletons,
          List.length_append, List.length_map, hmatchedLen]
      _ = 8 * s := fourLaneBoundaryMatching_count s
  have hpermSub : List.Subperm grouped output := hnodup.subperm hsub
  have hgroupedLen : grouped.length = 8 * s := by simp [grouped]
  exact List.Subperm.perm_of_length_le hpermSub (by rw [hlen, hgroupedLen])

theorem interBlockBoundaryMatching_dealt_mem_output {r N : Nat}
    (packets : Fin (2 * (2 * r)) -> Function.Embedding (Fin 64) (Fin N))
    (hdisjoint : forall i j, Not (i = j) -> forall x y, Not (packets i x = packets j y))
    (j : Fin r) (lane : Bool) :
    List.Mem (if lane then dealOddEmbedding (joinPacketEmbedding
        (packets (Fin.mk (4 * j.val + 1) (by omega)))
        (packets (Fin.mk (4 * j.val + 2) (by omega))) (by
          intro x y h
          exact hdisjoint _ _ (by
            intro heq
            have hv := congrArg Fin.val heq
            simp at hv) x y h))
      else dealEvenEmbedding (joinPacketEmbedding
        (packets (Fin.mk (4 * j.val + 1) (by omega)))
        (packets (Fin.mk (4 * j.val + 2) (by omega))) (by
          intro x y h
          exact hdisjoint _ _ (by
            intro heq
            have hv := congrArg Fin.val heq
            simp at hv) x y h)))
      (genIndexedPacketRoundOutput packets hdisjoint
        (interBlockBoundaryMatching r).edges (interBlockBoundaryMatching r).noFixed) := by
  let left : Fin (2 * (2 * r)) := Fin.mk (4 * j.val + 1) (by omega)
  let right : Fin (2 * (2 * r)) := Fin.mk (4 * j.val + 2) (by omega)
  have hne : Not (left = right) := by
    intro heq
    have hv := congrArg Fin.val heq
    simp [left, right] at hv
  have hsep : forall x y, Not (packets left x = packets right y) := hdisjoint left right hne
  let joined := joinPacketEmbedding (packets left) (packets right) hsep
  let edge : Prod (Fin (2 * (2 * r))) (Fin (2 * (2 * r))) := (left, right)
  have hedge : List.Mem edge (interBlockBoundaryMatching r).edges := by
    change List.Mem edge (interBlockBoundaryEdges r)
    simp only [interBlockBoundaryEdges, List.mem_map]
    exact List.mem_map.mpr (Exists.intro j (And.intro (List.mem_finRange j) rfl))
  have hjoined : List.Mem joined
      (genIndexedPairSupports packets hdisjoint
        (interBlockBoundaryMatching r).edges (interBlockBoundaryMatching r).noFixed) := by
    apply List.mem_map.mpr
    exact Exists.intro (Subtype.mk edge hedge)
      (And.intro (by simp) (by simp [joined, edge, left, right]))
  change List.Mem (if lane then dealOddEmbedding joined else dealEvenEmbedding joined)
    (genIndexedPacketRoundOutput packets hdisjoint
      (interBlockBoundaryMatching r).edges (interBlockBoundaryMatching r).noFixed)
  exact genIndexedPacketRound_deal_mem packets hdisjoint
    (interBlockBoundaryMatching r).edges (interBlockBoundaryMatching r).noFixed
    joined hjoined lane

theorem interBlockBoundaryMatching_singleton_mem_output {r N : Nat}
    (packets : Fin (2 * (2 * r)) → Fin 64 ↪ Fin N)
    (hdisjoint : ∀ i j, i ≠ j → ∀ x y, packets i x ≠ packets j y)
    (j : Fin r) (leftSide : Bool) :
    packets (if leftSide then ⟨4 * j.val, by omega⟩
      else ⟨4 * j.val + 3, by omega⟩) ∈
      genIndexedPacketRoundOutputWithSingletons packets hdisjoint
        (interBlockBoundaryMatching r).edges
        (interBlockBoundaryMatching r).noFixed
        (interBlockBoundaryMatching r).singles := by
  cases leftSide with
  | false =>
      simp only [Bool.false_eq_true, ↓reduceIte,
        genIndexedPacketRoundOutputWithSingletons, List.mem_append]
      right
      simp only [List.mem_map]
      refine ⟨⟨4 * j.val + 3, by omega⟩, ?_, rfl⟩
      simp only [interBlockBoundaryMatching, interBlockBoundarySingletons,
        List.mem_map, List.mem_finRange]
      refine ⟨⟨2 * j.val + 1, by omega⟩, by simp, ?_⟩
      apply Fin.ext
      simp
      omega
  | true =>
      simp only [Bool.true_eq, ↓reduceIte,
        genIndexedPacketRoundOutputWithSingletons, List.mem_append]
      right
      simp only [List.mem_map]
      refine ⟨⟨4 * j.val, by omega⟩, ?_, rfl⟩
      simp only [interBlockBoundaryMatching, interBlockBoundarySingletons,
        List.mem_map, List.mem_finRange]
      refine ⟨⟨2 * j.val, by omega⟩, by simp, ?_⟩
      apply Fin.ext
      simp
      omega

/-- Four-lane output block: two dealt lanes from the boundary edge, plus the
two untouched outer lanes from its pair of parent blocks. -/
def interBlockBoundaryOutputBlock {r N : Nat}
    (packets : Fin (2 * (2 * r)) → Fin 64 ↪ Fin N)
    (hdisjoint : ∀ i j, i ≠ j → ∀ x y, packets i x ≠ packets j y)
    (j : Fin r) (lane : Fin 4) : Fin 64 ↪ Fin N :=
  let left : Fin (2 * (2 * r)) := ⟨4 * j.val + 1, by omega⟩
  let right : Fin (2 * (2 * r)) := ⟨4 * j.val + 2, by omega⟩
  let joined := joinPacketEmbedding (packets left) (packets right)
    (hdisjoint left right (by
      intro h
      have hv := congrArg Fin.val h
      simp [left, right] at hv))
  if lane.val = 0 then dealEvenEmbedding joined
  else if lane.val = 1 then dealOddEmbedding joined
  else if lane.val = 2 then packets ⟨4 * j.val, by omega⟩
  else packets ⟨4 * j.val + 3, by omega⟩

/-- Every one of the four proposed macroblock lanes is present in the actual
output family: the middle pair are dealt outputs and the outer pair are
retained singleton packets. -/
theorem interBlockBoundaryOutputBlock_mem {r N : Nat}
    (packets : Fin (2 * (2 * r)) → Fin 64 ↪ Fin N)
    (hdisjoint : ∀ i j, i ≠ j → ∀ x y, packets i x ≠ packets j y)
    (j : Fin r) (lane : Fin 4) :
    interBlockBoundaryOutputBlock packets hdisjoint j lane ∈
      genIndexedPacketRoundOutputWithSingletons packets hdisjoint
        (interBlockBoundaryMatching r).edges
        (interBlockBoundaryMatching r).noFixed
        (interBlockBoundaryMatching r).singles := by
  fin_cases lane
  · change dealEvenEmbedding _ ∈ _
    simp only [genIndexedPacketRoundOutputWithSingletons, List.mem_append]
    exact Or.inl (interBlockBoundaryMatching_dealt_mem_output
      packets hdisjoint j false)
  · change dealOddEmbedding _ ∈ _
    simp only [genIndexedPacketRoundOutputWithSingletons, List.mem_append]
    exact Or.inl (interBlockBoundaryMatching_dealt_mem_output
      packets hdisjoint j true)
  · change packets ⟨4 * j.val, by omega⟩ ∈ _
    exact interBlockBoundaryMatching_singleton_mem_output
      packets hdisjoint j true
  · change packets ⟨4 * j.val + 3, by omega⟩ ∈ _
    exact interBlockBoundaryMatching_singleton_mem_output
      packets hdisjoint j false

/-- Every wire in a four-lane output block belongs to one of the four packet
supports in the corresponding pair of parent blocks. -/
theorem interBlockBoundaryOutputBlock_range {r N : Nat}
    (packets : Fin (2 * (2 * r)) → Fin 64 ↪ Fin N)
    (hdisjoint : ∀ i j, i ≠ j → ∀ x y, packets i x ≠ packets j y)
    (j : Fin r) (lane : Fin 4) (x : Fin 64) :
    ∃ i, i.val / 4 = j.val ∧
      interBlockBoundaryOutputBlock packets hdisjoint j lane x ∈ Set.range (packets i) := by
  let left : Fin (2 * (2 * r)) := ⟨4 * j.val + 1, by omega⟩
  let right : Fin (2 * (2 * r)) := ⟨4 * j.val + 2, by omega⟩
  have hsep : ∀ a b, packets left a ≠ packets right b := by
    exact hdisjoint left right (by
      intro h
      have hv := congrArg Fin.val h
      simp [left, right] at hv
      )
  have hjoined : ∀ w ∈ Set.range (joinPacketEmbedding (packets left)
      (packets right) hsep),
      w ∈ Set.range (packets left) ∨ w ∈ Set.range (packets right) := by
    intro w hw
    rw [joinPacketEmbedding_range _ _ hsep] at hw
    exact hw
  rcases lane with ⟨lane, hlane⟩
  interval_cases lane
  · have hw : dealEvenEmbedding (joinPacketEmbedding (packets left)
        (packets right) hsep) x ∈
        Set.range (joinPacketEmbedding (packets left) (packets right) hsep) := by
      exact ⟨evenWire 64 x, rfl⟩
    rcases hjoined _ hw with hw | hw
    · exact ⟨left, by simp [left]; omega, hw⟩
    · exact ⟨right, by simp [right]; omega, hw⟩
  · have hw : dealOddEmbedding (joinPacketEmbedding (packets left)
        (packets right) hsep) x ∈
        Set.range (joinPacketEmbedding (packets left) (packets right) hsep) := by
      exact ⟨oddWire 64 x, rfl⟩
    rcases hjoined _ hw with hw | hw
    · exact ⟨left, by simp [left]; omega, hw⟩
    · exact ⟨right, by simp [right]; omega, hw⟩
  · exact ⟨⟨4 * j.val, by omega⟩, by simp, ⟨x, rfl⟩⟩
  · exact ⟨⟨4 * j.val + 3, by omega⟩,
      by change (4 * j.val + 3) / 4 = j.val; omega, ⟨x, rfl⟩⟩

/-- A dealt middle lane draws only from the two endpoint packets of its
boundary edge. -/
theorem interBlockBoundaryDealtOutputBlock_range {r N : Nat}
    (packets : Fin (2 * (2 * r)) → Fin 64 ↪ Fin N)
    (hdisjoint : ∀ i j, i ≠ j → ∀ x y, packets i x ≠ packets j y)
    (j : Fin r) (odd : Bool) (x : Fin 64) :
    ∃ i, (i.val = 4 * j.val + 1 ∨ i.val = 4 * j.val + 2) ∧
      (if odd then
        dealOddEmbedding (joinPacketEmbedding
          (packets ⟨4 * j.val + 1, by omega⟩)
          (packets ⟨4 * j.val + 2, by omega⟩) (by
            intro a b h
            exact hdisjoint _ _ (by
              intro hne
              have hv := congrArg Fin.val hne
              simp at hv) a b h))
      else
        dealEvenEmbedding (joinPacketEmbedding
          (packets ⟨4 * j.val + 1, by omega⟩)
          (packets ⟨4 * j.val + 2, by omega⟩) (by
            intro a b h
            exact hdisjoint _ _ (by
              intro hne
              have hv := congrArg Fin.val hne
              simp at hv) a b h))) x ∈ Set.range (packets i) := by
  let left : Fin (2 * (2 * r)) := ⟨4 * j.val + 1, by omega⟩
  let right : Fin (2 * (2 * r)) := ⟨4 * j.val + 2, by omega⟩
  have hsep : ∀ a b, packets left a ≠ packets right b := by
    exact hdisjoint left right (by
      intro h
      have hv := congrArg Fin.val h
      simp [left, right] at hv)
  let joined := joinPacketEmbedding (packets left) (packets right) hsep
  change ∃ i, (i.val = 4 * j.val + 1 ∨ i.val = 4 * j.val + 2) ∧
    (if odd then dealOddEmbedding joined else dealEvenEmbedding joined) x ∈
      Set.range (packets i)
  have hmem : (if odd then dealOddEmbedding joined else dealEvenEmbedding joined) x ∈
      Set.range joined := by
    refine ⟨(if odd then oddWire 64 x else evenWire 64 x), ?_⟩
    cases odd <;> rfl
  rw [joinPacketEmbedding_range _ _ hsep] at hmem
  rcases hmem with hmem | hmem
  · exact ⟨left, Or.inl (by simp [left]), hmem⟩
  · exact ⟨right, Or.inr (by simp [right]), hmem⟩

/-- The dealt middle output is disjoint from either untouched outer packet in
its own four-lane macroblock. -/
theorem interBlockBoundaryDealtOutputBlock_disjoint_singleton {r N : Nat}
    (packets : Fin (2 * (2 * r)) → Fin 64 ↪ Fin N)
    (hdisjoint : ∀ i j, i ≠ j → ∀ x y, packets i x ≠ packets j y)
    (j : Fin r) (odd leftSide : Bool) (x y : Fin 64) :
    (if odd then
      dealOddEmbedding (joinPacketEmbedding
        (packets ⟨4 * j.val + 1, by omega⟩)
        (packets ⟨4 * j.val + 2, by omega⟩) (by
          intro a b h
          exact hdisjoint _ _ (by
            intro hne
            have hv := congrArg Fin.val hne
            simp at hv) a b h))
    else
      dealEvenEmbedding (joinPacketEmbedding
        (packets ⟨4 * j.val + 1, by omega⟩)
        (packets ⟨4 * j.val + 2, by omega⟩) (by
          intro a b h
          exact hdisjoint _ _ (by
            intro hne
            have hv := congrArg Fin.val hne
            simp at hv) a b h))) x ≠
      packets (if leftSide then ⟨4 * j.val, by omega⟩
        else ⟨4 * j.val + 3, by omega⟩) y := by
  obtain ⟨i, hi, hmem⟩ := interBlockBoundaryDealtOutputBlock_range
    packets hdisjoint j odd x
  obtain ⟨z, hz⟩ := hmem
  let singleton : Fin (2 * (2 * r)) :=
    if leftSide then ⟨4 * j.val, by omega⟩ else ⟨4 * j.val + 3, by omega⟩
  have hne : i ≠ singleton := by
    intro heq
    have hv := congrArg Fin.val heq
    cases leftSide <;> simp [singleton] at hv
    all_goals rcases hi with hi | hi <;> omega
  have hsource := hdisjoint i singleton hne z y
  intro h
  apply hsource
  rw [hz, h]

/-- The two dealt lanes of one boundary edge have disjoint supports. -/
theorem interBlockBoundaryDealtOutputBlock_disjoint {r N : Nat}
    (packets : Fin (2 * (2 * r)) → Fin 64 ↪ Fin N)
    (hdisjoint : ∀ i j, i ≠ j → ∀ x y, packets i x ≠ packets j y)
    (j : Fin r) (x y : Fin 64) :
    dealEvenEmbedding (joinPacketEmbedding
        (packets ⟨4 * j.val + 1, by omega⟩)
        (packets ⟨4 * j.val + 2, by omega⟩) (by
          intro a b h
          exact hdisjoint _ _ (by
            intro hne
            have hv := congrArg Fin.val hne
            simp at hv) a b h)) x ≠
    dealOddEmbedding (joinPacketEmbedding
        (packets ⟨4 * j.val + 1, by omega⟩)
        (packets ⟨4 * j.val + 2, by omega⟩) (by
          intro a b h
          exact hdisjoint _ _ (by
            intro hne
            have hv := congrArg Fin.val hne
            simp at hv) a b h)) y := by
  exact dealEmbeddings_disjoint _ x y

/-- The four lanes inside one proposed macroblock are pairwise support
disjoint. -/
theorem interBlockBoundaryOutputBlock_pairwise_disjoint {r N : Nat}
    (packets : Fin (2 * (2 * r)) → Fin 64 ↪ Fin N)
    (hdisjoint : ∀ i j, i ≠ j → ∀ x y, packets i x ≠ packets j y)
    (j : Fin r) (lane lane' : Fin 4) (hlane : lane ≠ lane')
    (x y : Fin 64) :
    interBlockBoundaryOutputBlock packets hdisjoint j lane x ≠
      interBlockBoundaryOutputBlock packets hdisjoint j lane' y := by
  fin_cases lane <;> fin_cases lane' <;>
    simp_all [interBlockBoundaryOutputBlock]
  all_goals
    first
    | exact interBlockBoundaryDealtOutputBlock_disjoint packets hdisjoint j x y
    | exact fun h => (interBlockBoundaryDealtOutputBlock_disjoint
        packets hdisjoint j y x) h.symm
    | exact interBlockBoundaryDealtOutputBlock_disjoint_singleton
        packets hdisjoint j false true x y
    | exact interBlockBoundaryDealtOutputBlock_disjoint_singleton
        packets hdisjoint j false false x y
    | exact interBlockBoundaryDealtOutputBlock_disjoint_singleton
        packets hdisjoint j true true x y
    | exact interBlockBoundaryDealtOutputBlock_disjoint_singleton
        packets hdisjoint j true false x y
    | exact fun h => (interBlockBoundaryDealtOutputBlock_disjoint_singleton
        packets hdisjoint j false true y x) h.symm
    | exact fun h => (interBlockBoundaryDealtOutputBlock_disjoint_singleton
        packets hdisjoint j false false y x) h.symm
    | exact fun h => (interBlockBoundaryDealtOutputBlock_disjoint_singleton
        packets hdisjoint j true true y x) h.symm
    | exact fun h => (interBlockBoundaryDealtOutputBlock_disjoint_singleton
        packets hdisjoint j true false y x) h.symm
    | exact hdisjoint _ _ (by
        intro h
        have hv := congrArg Fin.val h
        simp at hv
        omega) x y
    | exact fun h => hdisjoint _ _ (by
        intro hne
        have hv := congrArg Fin.val hne
        simp at hv
        omega) y x h.symm

/-- The four regrouped lanes preserve exactly the support of the four parent
lanes in their macroblock. -/
theorem interBlockBoundaryOutputBlock_support_eq {r N : Nat}
    (packets : Fin (2 * (2 * r)) → Fin 64 ↪ Fin N)
    (hdisjoint : ∀ i j, i ≠ j → ∀ x y, packets i x ≠ packets j y)
    (j : Fin r) :
    (Set.range (interBlockBoundaryOutputBlock packets hdisjoint j 0) ∪
      Set.range (interBlockBoundaryOutputBlock packets hdisjoint j 1) ∪
      Set.range (interBlockBoundaryOutputBlock packets hdisjoint j 2) ∪
      Set.range (interBlockBoundaryOutputBlock packets hdisjoint j 3)) =
    (Set.range (packets ⟨4 * j.val, by omega⟩) ∪
      Set.range (packets ⟨4 * j.val + 1, by omega⟩) ∪
      Set.range (packets ⟨4 * j.val + 2, by omega⟩) ∪
      Set.range (packets ⟨4 * j.val + 3, by omega⟩)) := by
  let left : Fin (2 * (2 * r)) := ⟨4 * j.val + 1, by omega⟩
  let right : Fin (2 * (2 * r)) := ⟨4 * j.val + 2, by omega⟩
  have hsep : ∀ a b, packets left a ≠ packets right b := by
    exact hdisjoint left right (by
      intro h
      have hv := congrArg Fin.val h
      simp [left, right] at hv)
  let joined := joinPacketEmbedding (packets left) (packets right) hsep
  change (Set.range (dealEvenEmbedding joined) ∪
      Set.range (dealOddEmbedding joined) ∪
      Set.range (packets ⟨4 * j.val, by omega⟩) ∪
      Set.range (packets ⟨4 * j.val + 3, by omega⟩)) = _
  rw [dealEmbeddings_partition joined, joinPacketEmbedding_range _ _ hsep]
  ext w
  simp only [Set.mem_union]
  tauto

/-- Complete local contract for regrouping one boundary round into a
four-packet macroblock. -/
theorem interBlockBoundaryOutputBlock_contract {r N : Nat} {α : Type}
    [LinearOrder α]
    (packets : Fin (2 * (2 * r)) → Fin 64 ↪ Fin N)
    (hdisjoint : ∀ i j, i ≠ j → ∀ x y, packets i x ≠ packets j y)
    (hpacketMono : ∀ i, StrictMono (packets i))
    (hblockOrdered : ∀ i j, i.val / 2 < j.val / 2 → ∀ x y,
      packets i x < packets j y)
    (v : Fin N → α) (hsorted : ∀ i, Monotone (fun k => v (packets i k)))
    (j : Fin r) :
    (∀ lane, Monotone (fun x =>
      (genIndexedPacketRound packets hdisjoint
        (interBlockBoundaryMatching r).edges
        (interBlockBoundaryMatching r).noFixed).exec v
        (interBlockBoundaryOutputBlock packets hdisjoint j lane x))) ∧
    (∀ lane, StrictMono (interBlockBoundaryOutputBlock packets hdisjoint j lane)) ∧
    (∀ lane lane', lane ≠ lane' → ∀ x y,
      interBlockBoundaryOutputBlock packets hdisjoint j lane x ≠
        interBlockBoundaryOutputBlock packets hdisjoint j lane' y) ∧
    (Set.range (interBlockBoundaryOutputBlock packets hdisjoint j 0) ∪
      Set.range (interBlockBoundaryOutputBlock packets hdisjoint j 1) ∪
      Set.range (interBlockBoundaryOutputBlock packets hdisjoint j 2) ∪
      Set.range (interBlockBoundaryOutputBlock packets hdisjoint j 3)) =
    (Set.range (packets ⟨4 * j.val, by omega⟩) ∪
      Set.range (packets ⟨4 * j.val + 1, by omega⟩) ∪
      Set.range (packets ⟨4 * j.val + 2, by omega⟩) ∪
      Set.range (packets ⟨4 * j.val + 3, by omega⟩)) ∧
    (∀ lane, interBlockBoundaryOutputBlock packets hdisjoint j lane ∈
      genIndexedPacketRoundOutputWithSingletons packets hdisjoint
        (interBlockBoundaryMatching r).edges
        (interBlockBoundaryMatching r).noFixed
        (interBlockBoundaryMatching r).singles) := by
  let matching := interBlockBoundaryMatching r
  have hsingleDisjoint : List.Pairwise
      (fun i k : Fin (2 * (2 * r)) => ∀ x y,
        packets i x ≠ packets k y) matching.singles := by
    have haux : ∀ ids : List (Fin (2 * (2 * r))),
        List.Pairwise (fun i k => i ≠ k) ids →
        List.Pairwise (fun i k => ∀ x y, packets i x ≠ packets k y) ids := by
      intro ids hids
      induction ids with
      | nil => simp
      | cons i ids ih =>
          rcases List.pairwise_cons.mp hids with ⟨hhead, htail⟩
          apply List.pairwise_cons.mpr
          constructor
          · intro k hk x y
            exact hdisjoint i k (hhead k hk) x y
          · exact ih htail
    exact haux matching.singles matching.singleDisjoint
  have hroundContract := genIndexedPacketRound_withSingletons_contract
    packets hdisjoint matching.edges matching.nodup matching.noFixed
    matching.vertexDisjoint matching.singles hsingleDisjoint matching.free
    matching.covers v hsorted
  have hmonoOutputs := genIndexedPacketRound_withSingletons_output_strictMono
    packets hdisjoint matching.edges matching.noFixed matching.singles
    hpacketMono (interBlockBoundaryMatching_ordered packets hblockOrdered)
  refine ⟨?_, ?_, ?_, interBlockBoundaryOutputBlock_support_eq
    packets hdisjoint j, ?_⟩
  · intro lane
    exact hroundContract.1 _ (interBlockBoundaryOutputBlock_mem
      packets hdisjoint j lane)
  · intro lane
    exact hmonoOutputs _ (interBlockBoundaryOutputBlock_mem
      packets hdisjoint j lane)
  · intro lane lane' hne x y
    exact interBlockBoundaryOutputBlock_pairwise_disjoint packets hdisjoint
      j lane lane' hne x y
  · intro lane
    exact interBlockBoundaryOutputBlock_mem packets hdisjoint j lane

/-- Regrouped output blocks inherit strict physical separation from the parent
blocks whenever the parent blocks were strictly ordered. -/
theorem interBlockBoundaryOutputBlocks_ordered {r N : Nat}
    (packets : Fin (2 * (2 * r)) → Fin 64 ↪ Fin N)
    (hdisjoint : ∀ i j, i ≠ j → ∀ x y, packets i x ≠ packets j y)
    (hblockOrdered : ∀ i j, i.val / 2 < j.val / 2 → ∀ x y,
      packets i x < packets j y)
    (j l : Fin r) (hjl : j.val < l.val) (lane lane' : Fin 4)
    (x y : Fin 64) :
    interBlockBoundaryOutputBlock packets hdisjoint j lane x <
      interBlockBoundaryOutputBlock packets hdisjoint l lane' y := by
  obtain ⟨i, hi, hix⟩ := interBlockBoundaryOutputBlock_range
    packets hdisjoint j lane x
  obtain ⟨i', hi', hiy⟩ := interBlockBoundaryOutputBlock_range
    packets hdisjoint l lane' y
  obtain ⟨z, hz⟩ := hix
  obtain ⟨z', hz'⟩ := hiy
  rw [← hz, ← hz']
  have hi'lt := i'.isLt
  have hilt := i.isLt
  apply hblockOrdered i i' (by omega) z z'

/-- In particular, different regrouped blocks have disjoint physical supports. -/
theorem interBlockBoundaryOutputBlocks_disjoint {r N : Nat}
    (packets : Fin (2 * (2 * r)) → Fin 64 ↪ Fin N)
    (hdisjoint : ∀ i j, i ≠ j → ∀ x y, packets i x ≠ packets j y)
    (hblockOrdered : ∀ i j, i.val / 2 < j.val / 2 → ∀ x y,
      packets i x < packets j y)
    (j l : Fin r) (hjl : j.val < l.val) (lane lane' : Fin 4)
    (x y : Fin 64) :
    interBlockBoundaryOutputBlock packets hdisjoint j lane x ≠
      interBlockBoundaryOutputBlock packets hdisjoint l lane' y := by
  exact ne_of_lt (interBlockBoundaryOutputBlocks_ordered packets hdisjoint
    hblockOrdered j l hjl lane lane' x y)

/-- Every lane in a regrouped boundary output block is sorted after execution
and is increasing in physical wire order. -/
theorem interBlockBoundaryOutputBlock_lane_contract {r N : Nat} {α : Type}
    [LinearOrder α]
    (packets : Fin (2 * (2 * r)) → Fin 64 ↪ Fin N)
    (hdisjoint : ∀ i j, i ≠ j → ∀ x y, packets i x ≠ packets j y)
    (hpacketMono : ∀ i, StrictMono (packets i))
    (hblockOrdered : ∀ i j, i.val / 2 < j.val / 2 → ∀ x y,
      packets i x < packets j y)
    (v : Fin N → α) (hsorted : ∀ i, Monotone (fun k => v (packets i k)))
    (j : Fin r) (lane : Fin 4) :
    Monotone (fun x =>
      (genIndexedPacketRound packets hdisjoint
        (interBlockBoundaryMatching r).edges
        (interBlockBoundaryMatching r).noFixed).exec v
        (interBlockBoundaryOutputBlock packets hdisjoint j lane x)) ∧
    StrictMono (interBlockBoundaryOutputBlock packets hdisjoint j lane) := by
  let matching := interBlockBoundaryMatching r
  have hsingleDisjoint : List.Pairwise
      (fun i k : Fin (2 * (2 * r)) => ∀ x y,
        packets i x ≠ packets k y) matching.singles := by
    have haux : ∀ ids : List (Fin (2 * (2 * r))),
        List.Pairwise (fun i k => i ≠ k) ids →
        List.Pairwise (fun i k => ∀ x y, packets i x ≠ packets k y) ids := by
      intro ids hids
      induction ids with
      | nil => simp
      | cons i ids ih =>
          rcases List.pairwise_cons.mp hids with ⟨hhead, htail⟩
          apply List.pairwise_cons.mpr
          constructor
          · intro k hk x y
            exact hdisjoint i k (hhead k hk) x y
          · exact ih htail
    exact haux matching.singles matching.singleDisjoint
  have hcontract := genIndexedPacketRound_withSingletons_contract
    packets hdisjoint matching.edges matching.nodup matching.noFixed
    matching.vertexDisjoint matching.singles hsingleDisjoint matching.free
    matching.covers v hsorted
  have hmem := interBlockBoundaryOutputBlock_mem packets hdisjoint j lane
  have hsortedLane := hcontract.1 _ hmem
  have hmonoOutputs := genIndexedPacketRound_withSingletons_output_strictMono
    packets hdisjoint matching.edges matching.noFixed matching.singles
    hpacketMono (interBlockBoundaryMatching_ordered packets hblockOrdered)
  exact ⟨hsortedLane, hmonoOutputs _ hmem⟩

/-- Reindex all four-lane macroblocks as one flat packet array in
block-major, lane-minor order. -/
def interBlockBoundaryGroupedOutput {r N : Nat}
    (packets : Fin (2 * (2 * r)) → Fin 64 ↪ Fin N)
    (hdisjoint : ∀ i j, i ≠ j → ∀ x y, packets i x ≠ packets j y)
    (i : Fin (2 * (2 * r))) : Fin 64 ↪ Fin N :=
  let j : Fin r := ⟨i.val / 4, by have := i.isLt; omega⟩
  let lane : Fin 4 := ⟨i.val % 4, by omega⟩
  interBlockBoundaryOutputBlock packets hdisjoint j lane

/-- The flat grouped-output index `4*j+lane` decodes to the specified block
and lane. -/
theorem interBlockBoundaryGroupedOutput_at {r N : Nat}
    (packets : Fin (2 * (2 * r)) → Fin 64 ↪ Fin N)
    (hdisjoint : ∀ i j, i ≠ j → ∀ x y, packets i x ≠ packets j y)
    (j : Fin r) (lane : Fin 4) :
    interBlockBoundaryGroupedOutput packets hdisjoint
      ⟨4 * j.val + lane.val, by omega⟩ =
    interBlockBoundaryOutputBlock packets hdisjoint j lane := by
  ext x
  simp only [interBlockBoundaryGroupedOutput]
  have hjlt := j.isLt
  have hll := lane.isLt
  let n := 4 * j.val + lane.val
  have hmod : n % 4 = lane.val := by
    simp [n, Nat.add_mod, Nat.mod_eq_of_lt hll]
  have hdiv : n / 4 = j.val := by
    have hidentity := Nat.mod_add_div n 4
    rw [hmod] at hidentity
    dsimp [n] at hidentity
    omega
  have hblock : (⟨n / 4, by rw [hdiv]; exact hjlt⟩ : Fin r) = j :=
    Fin.ext hdiv
  have hlane : (⟨n % 4, by rw [hmod]; exact hll⟩ : Fin 4) = lane :=
    Fin.ext hmod
  rw [hblock, hlane]

/-- The flat regrouped outputs remain pairwise support-disjoint. -/
theorem interBlockBoundaryGroupedOutput_disjoint {r N : Nat}
    (packets : Fin (2 * (2 * r)) → Fin 64 ↪ Fin N)
    (hdisjoint : ∀ i j, i ≠ j → ∀ x y, packets i x ≠ packets j y)
    (hblockOrdered : ∀ i j, i.val / 2 < j.val / 2 → ∀ x y,
      packets i x < packets j y)
    (i k : Fin (2 * (2 * r))) (hik : i ≠ k) (x y : Fin 64) :
    interBlockBoundaryGroupedOutput packets hdisjoint i x ≠
      interBlockBoundaryGroupedOutput packets hdisjoint k y := by
  let j : Fin r := ⟨i.val / 4, by have := i.isLt; omega⟩
  let l : Fin r := ⟨k.val / 4, by have := k.isLt; omega⟩
  let lane : Fin 4 := ⟨i.val % 4, by omega⟩
  let lane' : Fin 4 := ⟨k.val % 4, by omega⟩
  have hiBlock : j.val = i.val / 4 := rfl
  have hkBlock : l.val = k.val / 4 := rfl
  have hiLane : lane.val = i.val % 4 := rfl
  have hkLane : lane'.val = k.val % 4 := rfl
  change interBlockBoundaryOutputBlock packets hdisjoint j lane x ≠
    interBlockBoundaryOutputBlock packets hdisjoint l lane' y
  by_cases hsame : j.val = l.val
  · have hneLane : lane ≠ lane' := by
      intro heq
      apply hik
      apply Fin.ext
      have hleft := Nat.mod_add_div i.val 4
      have hright := Nat.mod_add_div k.val 4
      have hLaneEq := congrArg Fin.val heq
      rw [← hiLane, ← hiBlock] at hleft
      rw [← hkLane, ← hkBlock, ← hsame, ← hLaneEq] at hright
      omega
    have hsameFin : j = l := Fin.ext hsame
    rw [← hsameFin]
    exact interBlockBoundaryOutputBlock_pairwise_disjoint
      packets hdisjoint j lane lane' hneLane x y
  · rcases Nat.lt_or_gt_of_ne hsame with hlt | hgt
    · exact ne_of_lt (interBlockBoundaryOutputBlocks_ordered
        packets hdisjoint hblockOrdered j l hlt lane lane' x y)
    · exact (ne_of_lt (interBlockBoundaryOutputBlocks_ordered
        packets hdisjoint hblockOrdered l j hgt lane' lane y x)).symm

/-- The flat block-major regrouping preserves the full finite union of packet
supports, not only each individual four-packet block. -/
theorem interBlockBoundaryGroupedOutput_support_eq {r N : Nat}
    (packets : Fin (2 * (2 * r)) → Fin 64 ↪ Fin N)
    (hdisjoint : ∀ i j, i ≠ j → ∀ x y, packets i x ≠ packets j y)
    (hblockOrdered : ∀ i j, i.val / 2 < j.val / 2 → ∀ x y,
      packets i x < packets j y) :
    Finset.univ.biUnion (fun i => packetEmbeddingSupport
      (interBlockBoundaryGroupedOutput packets hdisjoint i)) =
    Finset.univ.biUnion (fun i => packetEmbeddingSupport (packets i)) := by
  have hOutDisjoint : ∀ i ∈ Finset.univ, ∀ k ∈ Finset.univ, i ≠ k →
      Disjoint (packetEmbeddingSupport
        (interBlockBoundaryGroupedOutput packets hdisjoint i))
        (packetEmbeddingSupport
          (interBlockBoundaryGroupedOutput packets hdisjoint k)) := by
    intro i _ k _ hik
    apply Finset.disjoint_left.mpr
    intro w hw hw'
    obtain ⟨x, hx⟩ := (packetEmbeddingSupport_mem_iff _ _).mp hw
    obtain ⟨y, hy⟩ := (packetEmbeddingSupport_mem_iff _ _).mp hw'
    apply (interBlockBoundaryGroupedOutput_disjoint packets hdisjoint
      hblockOrdered i k hik x y)
    rw [hx, hy]
  have hInDisjoint : ∀ i ∈ Finset.univ, ∀ k ∈ Finset.univ, i ≠ k →
      Disjoint (packetEmbeddingSupport (packets i))
        (packetEmbeddingSupport (packets k)) := by
    intro i _ k _ hik
    apply Finset.disjoint_left.mpr
    intro w hw hw'
    obtain ⟨x, hx⟩ := (packetEmbeddingSupport_mem_iff _ _).mp hw
    obtain ⟨y, hy⟩ := (packetEmbeddingSupport_mem_iff _ _).mp hw'
    exact hdisjoint i k hik x y (by rw [hx, hy])
  have hsubset :
      Finset.univ.biUnion (fun i => packetEmbeddingSupport
        (interBlockBoundaryGroupedOutput packets hdisjoint i)) ⊆
      Finset.univ.biUnion (fun i => packetEmbeddingSupport (packets i)) := by
    intro w hw
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and] at hw ⊢
    obtain ⟨i, hi⟩ := hw
    obtain ⟨x, hx⟩ := (packetEmbeddingSupport_mem_iff _ _).mp hi
    let j : Fin r := ⟨i.val / 4, by have := i.isLt; omega⟩
    let lane : Fin 4 := ⟨i.val % 4, by omega⟩
    change interBlockBoundaryOutputBlock packets hdisjoint j lane x = w at hx
    obtain ⟨k, _, hk⟩ := interBlockBoundaryOutputBlock_range
      packets hdisjoint j lane x
    obtain ⟨y, hy⟩ := hk
    refine ⟨k, (packetEmbeddingSupport_mem_iff _ _).mpr ⟨y, ?_⟩⟩
    rw [hy, hx]
  have hcardOut := Finset.card_biUnion hOutDisjoint
  have hcardIn := Finset.card_biUnion hInDisjoint
  have hcardOut' : (Finset.univ.biUnion (fun i => packetEmbeddingSupport
      (interBlockBoundaryGroupedOutput packets hdisjoint i))).card =
      (2 * (2 * r)) * 64 := by
    rw [hcardOut]
    simp [packetEmbeddingSupport_card]
  have hcardIn' : (Finset.univ.biUnion (fun i => packetEmbeddingSupport
      (packets i))).card = (2 * (2 * r)) * 64 := by
    rw [hcardIn]
    simp [packetEmbeddingSupport_card]
  apply Finset.eq_of_subset_of_card_le hsubset
  rw [hcardOut', hcardIn']

/-- Every packet in the flat regrouped array is sorted after the round and is
strictly increasing on physical wire indices. -/
theorem interBlockBoundaryGroupedOutput_lane_contract {r N : Nat} {α : Type}
    [LinearOrder α]
    (packets : Fin (2 * (2 * r)) → Fin 64 ↪ Fin N)
    (hdisjoint : ∀ i j, i ≠ j → ∀ x y, packets i x ≠ packets j y)
    (hpacketMono : ∀ i, StrictMono (packets i))
    (hblockOrdered : ∀ i j, i.val / 2 < j.val / 2 → ∀ x y,
      packets i x < packets j y)
    (v : Fin N → α) (hsorted : ∀ i, Monotone (fun k => v (packets i k)))
    (i : Fin (2 * (2 * r))) :
    Monotone (fun x =>
      (genIndexedPacketRound packets hdisjoint
        (interBlockBoundaryMatching r).edges
        (interBlockBoundaryMatching r).noFixed).exec v
        (interBlockBoundaryGroupedOutput packets hdisjoint i x)) ∧
    StrictMono (interBlockBoundaryGroupedOutput packets hdisjoint i) := by
  let j : Fin r := ⟨i.val / 4, by have := i.isLt; omega⟩
  let lane : Fin 4 := ⟨i.val % 4, by omega⟩
  have h := interBlockBoundaryOutputBlock_lane_contract packets hdisjoint
    hpacketMono hblockOrdered v hsorted j lane
  simpa [interBlockBoundaryGroupedOutput, j, lane] using h

/-- Distinct flat four-lane macroblocks remain strictly ordered on physical
wires after the boundary round. -/
theorem interBlockBoundaryGroupedOutput_blocks_ordered {r N : Nat}
    (packets : Fin (2 * (2 * r)) → Fin 64 ↪ Fin N)
    (hdisjoint : ∀ i j, i ≠ j → ∀ x y, packets i x ≠ packets j y)
    (hblockOrdered : ∀ i j, i.val / 2 < j.val / 2 → ∀ x y,
      packets i x < packets j y)
    (j l : Fin r) (hjl : j.val < l.val) (lane lane' : Fin 4)
    (x y : Fin 64) :
    interBlockBoundaryGroupedOutput packets hdisjoint
        ⟨4 * j.val + lane.val, by omega⟩ x <
      interBlockBoundaryGroupedOutput packets hdisjoint
        ⟨4 * l.val + lane'.val, by omega⟩ y := by
  rw [interBlockBoundaryGroupedOutput_at, interBlockBoundaryGroupedOutput_at]
  exact interBlockBoundaryOutputBlocks_ordered packets hdisjoint
    hblockOrdered j l hjl lane lane' x y

/-- After the first 2-lane boundary transition, the last lane of one
four-packet block is strictly before the first lane of the next. This is the
orientation condition for a new, width-four boundary matching. -/
theorem interBlockBoundaryGroupedOutput_nextBoundaryEdge_ordered {s N : Nat}
    (packets : Fin (2 * (2 * (2 * s))) → Fin 64 ↪ Fin N)
    (hdisjoint : ∀ i j, i ≠ j → ∀ x y, packets i x ≠ packets j y)
    (hblockOrdered : ∀ i j, i.val / 2 < j.val / 2 → ∀ x y,
      packets i x < packets j y)
    (j : Fin s) (x y : Fin 64) :
    interBlockBoundaryGroupedOutput packets hdisjoint
        ⟨8 * j.val + 3, by omega⟩ x <
      interBlockBoundaryGroupedOutput packets hdisjoint
        ⟨8 * j.val + 4, by omega⟩ y := by
  let leftBlock : Fin (2 * s) := ⟨2 * j.val, by omega⟩
  let rightBlock : Fin (2 * s) := ⟨2 * j.val + 1, by omega⟩
  have hlt : leftBlock.val < rightBlock.val := by simp [leftBlock, rightBlock]
  have h := interBlockBoundaryGroupedOutput_blocks_ordered packets hdisjoint
    hblockOrdered leftBlock rightBlock hlt (3 : Fin 4) (0 : Fin 4) x y
  have hleft : (⟨4 * leftBlock.val + 3, by omega⟩ :
      Fin (2 * (2 * (2 * s)))) = ⟨8 * j.val + 3, by omega⟩ := by
    apply Fin.ext
    simp [leftBlock]
    omega
  have hright : (⟨4 * rightBlock.val, by omega⟩ :
      Fin (2 * (2 * (2 * s)))) = ⟨8 * j.val + 4, by omega⟩ := by
    apply Fin.ext
    simp [rightBlock]
    omega
  rw [← hleft, ← hright]
  exact h

/-- State invariant for iterating logical matching rounds. Values are recorded
with their current wire labels; packet supports remain a fixed partition. -/
structure IndexedPacketRoundState (m N : Nat) (α : Type)
    [LinearOrder α] (support : Finset (Fin N)) where
  packets : Fin m → Fin 64 ↪ Fin N
  values : Fin N → α
  disjoint : ∀ i j, i ≠ j → ∀ x y, packets i x ≠ packets j y
  sorted : ∀ i, Monotone (fun k : Fin 64 => values (packets i k))
  support_eq : Finset.univ.biUnion (fun i => packetEmbeddingSupport (packets i)) =
    support

/-- Strengthened logical state whose packet embeddings also agree with the
physical rank order on each support. -/
structure IndexedPacketPhysicalRoundState (m N : Nat) (α : Type)
    [LinearOrder α] (support : Finset (Fin N))
    extends IndexedPacketRoundState m N α support where
  packetStrictMono : ∀ i, StrictMono (packets i)

/-- One sixteen-packet boundary round preserves the physical packet state
when its outputs are reindexed in block-major order. -/
theorem eightLaneBoundaryMatching_preservesGroupedPhysicalState
    {s N : Nat} {α : Type} [LinearOrder α] {support : Finset (Fin N)}
    (state : IndexedPacketPhysicalRoundState (16 * s) N α support)
    (hblockOrdered : ∀ i j, i.val / 8 < j.val / 8 → ∀ x y,
      state.packets i x < state.packets j y) :
    ∃ next : IndexedPacketPhysicalRoundState (16 * s) N α support,
      next.values = (genIndexedPacketRound state.packets state.disjoint
        (eightLaneBoundaryMatching s).edges
        (eightLaneBoundaryMatching s).noFixed).exec state.values ∧
      (genIndexedPacketRound state.packets state.disjoint
        (eightLaneBoundaryMatching s).edges
        (eightLaneBoundaryMatching s).noFixed).depth ≤ 7 := by
  let matching := eightLaneBoundaryMatching s
  let round := genIndexedPacketRound state.packets state.disjoint
    matching.edges matching.noFixed
  have hdepth := genIndexedPacketRound_depth_le state.packets state.disjoint
    matching.edges matching.nodup matching.noFixed matching.vertexDisjoint
  refine ⟨{
    toIndexedPacketRoundState := {
      packets := eightLaneBoundaryGroupedOutput state.packets state.disjoint
      values := round.exec state.values
      disjoint := ?_
      sorted := ?_
      support_eq := ?_ }
    packetStrictMono := ?_ }, rfl, ?_⟩
  · exact eightLaneBoundaryGroupedOutput_disjoint state.packets state.disjoint
      hblockOrdered
  · intro i
    let j : Fin s := ⟨i.val / 16, by have := i.isLt; omega⟩
    let lane : Fin 16 := ⟨i.val % 16, by omega⟩
    have h := eightLaneBoundaryOutputBlock_lane_contract state.packets
      state.disjoint state.packetStrictMono hblockOrdered state.values state.sorted j lane
    simpa [eightLaneBoundaryGroupedOutput, round, j, lane] using h.1
  · calc
      Finset.univ.biUnion (fun i => packetEmbeddingSupport
          (eightLaneBoundaryGroupedOutput state.packets state.disjoint i)) =
        Finset.univ.biUnion (fun i => packetEmbeddingSupport (state.packets i)) :=
          eightLaneBoundaryGroupedOutput_support_eq state.packets state.disjoint
            hblockOrdered state.values state.sorted
      _ = support := state.support_eq
  · intro i
    let j : Fin s := ⟨i.val / 16, by have := i.isLt; omega⟩
    let lane : Fin 16 := ⟨i.val % 16, by omega⟩
    have h := eightLaneBoundaryOutputBlock_lane_contract state.packets
      state.disjoint state.packetStrictMono hblockOrdered state.values state.sorted j lane
    simpa [eightLaneBoundaryGroupedOutput, j, lane] using h.2
  · exact hdepth

/-- One boundary matching step preserves the full physical packet state when
the four-lane macroblocks are reindexed in block-major order. -/
theorem interBlockBoundaryMatching_preservesGroupedPhysicalState
    {r N : Nat} {α : Type} [LinearOrder α] {support : Finset (Fin N)}
    (state : IndexedPacketPhysicalRoundState (2 * (2 * r)) N α support)
    (hblockOrdered : ∀ i j, i.val / 2 < j.val / 2 → ∀ x y,
      state.packets i x < state.packets j y) :
    ∃ next : IndexedPacketPhysicalRoundState (2 * (2 * r)) N α support,
      next.values = (genIndexedPacketRound state.packets state.disjoint
        (interBlockBoundaryMatching r).edges
        (interBlockBoundaryMatching r).noFixed).exec state.values ∧
      (genIndexedPacketRound state.packets state.disjoint
        (interBlockBoundaryMatching r).edges
        (interBlockBoundaryMatching r).noFixed).depth ≤ 7 := by
  let matching := interBlockBoundaryMatching r
  let round := genIndexedPacketRound state.packets state.disjoint
    matching.edges matching.noFixed
  have hdepth := genIndexedPacketRound_depth_le state.packets state.disjoint
    matching.edges matching.nodup matching.noFixed matching.vertexDisjoint
  refine ⟨{
    toIndexedPacketRoundState := {
      packets := interBlockBoundaryGroupedOutput state.packets state.disjoint
      values := round.exec state.values
      disjoint := interBlockBoundaryGroupedOutput_disjoint state.packets
        state.disjoint hblockOrdered
      sorted := ?_
      support_eq := ?_ }
    packetStrictMono := ?_ }, rfl, ?_⟩
  · intro i
    exact (interBlockBoundaryGroupedOutput_lane_contract state.packets
      state.disjoint state.packetStrictMono hblockOrdered state.values
      state.sorted i).1
  · calc
      Finset.univ.biUnion (fun i => packetEmbeddingSupport
          (interBlockBoundaryGroupedOutput state.packets state.disjoint i)) =
        Finset.univ.biUnion (fun i => packetEmbeddingSupport (state.packets i)) :=
          interBlockBoundaryGroupedOutput_support_eq state.packets state.disjoint
            hblockOrdered
      _ = support := state.support_eq
  · intro i
    exact (interBlockBoundaryGroupedOutput_lane_contract state.packets
      state.disjoint state.packetStrictMono hblockOrdered state.values
      state.sorted i).2
  · exact hdepth

/-- One eight-packet boundary step preserves a physical state when its actual
round output is reindexed by the proved block-major permutation. -/
theorem fourLaneBoundaryMatching_preservesGroupedPhysicalState
    {s N : Nat} {α : Type} [LinearOrder α] {support : Finset (Fin N)}
    (state : IndexedPacketPhysicalRoundState (8 * s) N α support)
    (hblockOrdered : ∀ i j, i.val / 4 < j.val / 4 → ∀ x y,
      state.packets i x < state.packets j y) :
    ∃ next : IndexedPacketPhysicalRoundState (8 * s) N α support,
      next.packets = fourLaneBoundaryGroupedOutput state.packets state.disjoint ∧
      next.values = (genIndexedPacketRound state.packets state.disjoint
        (fourLaneBoundaryMatching s).edges
        (fourLaneBoundaryMatching s).noFixed).exec state.values ∧
      (genIndexedPacketRound state.packets state.disjoint
        (fourLaneBoundaryMatching s).edges
        (fourLaneBoundaryMatching s).noFixed).depth ≤ 7 := by
  let matching := fourLaneBoundaryMatching s
  let round := genIndexedPacketRound state.packets state.disjoint
    matching.edges matching.noFixed
  let grouped := fourLaneBoundaryGroupedOutput state.packets state.disjoint
  let output := genIndexedPacketRoundOutputWithSingletons state.packets
    state.disjoint matching.edges matching.noFixed matching.singles
  have hsingleDisjoint : List.Pairwise
      (fun i j => ∀ x y, state.packets i x ≠ state.packets j y) matching.singles := by
    have haux : ∀ ids : List (Fin (8 * s)), List.Pairwise (fun i j => i ≠ j) ids →
        List.Pairwise
          (fun i j => ∀ x y, state.packets i x ≠ state.packets j y) ids := by
      intro ids hids
      induction ids with
      | nil => simp
      | cons i ids ih =>
          rcases List.pairwise_cons.mp hids with ⟨hhead, htail⟩
          apply List.pairwise_cons.mpr
          constructor
          · intro j hj x y
            exact state.disjoint i j (hhead j hj) x y
          · exact ih htail
    exact haux matching.singles matching.singleDisjoint
  have hcontract := genIndexedPacketRound_withSingletons_contract
    state.packets state.disjoint matching.edges matching.nodup matching.noFixed
    matching.vertexDisjoint matching.singles hsingleDisjoint matching.free
    matching.covers state.values state.sorted
  have hperm := fourLaneBoundaryGroupedOutput_perm_output state.packets
    state.disjoint hblockOrdered
  have hdepth := genIndexedPacketRound_depth_le state.packets state.disjoint
    matching.edges matching.nodup matching.noFixed matching.vertexDisjoint
  have hgroupDisjoint : ∀ i k, i ≠ k → ∀ x y, grouped i x ≠ grouped k y := by
    intro i k hik x y
    have hne : i != k := by simpa only [bne_iff_ne] using hik
    have hneBool := fourLaneBoundaryGroupedOutput_disjoint state.packets
      state.disjoint hblockOrdered i k hne x y
    simpa only [bne_iff_ne] using hneBool
  have hsorted : ∀ i, Monotone (fun x => round.exec state.values (grouped i x)) := by
    intro i
    exact (fourLaneBoundaryGroupedOutput_lane_contract state.packets
      state.disjoint state.packetStrictMono hblockOrdered state.values
      state.sorted i).1
  have hmono : ∀ i, StrictMono (grouped i) := by
    intro i
    exact (fourLaneBoundaryGroupedOutput_lane_contract state.packets
      state.disjoint state.packetStrictMono hblockOrdered state.values
      state.sorted i).2
  have hsupp : Finset.univ.biUnion (fun i => packetEmbeddingSupport (grouped i)) = support := by
    ext w
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨i, hi⟩
      obtain ⟨x, hx⟩ := (packetEmbeddingSupport_mem_iff _ _).mp hi
      have hmemGrouped : List.Mem (grouped i)
          (List.ofFn (fourLaneBoundaryGroupedOutput state.packets state.disjoint)) := by
        apply List.mem_ofFn.mpr
        exact ⟨i, rfl⟩
      have hmemOutput : List.Mem (grouped i) output := by
        simpa [output, matching] using hperm.mem_iff.mp hmemGrouped
      have hin := (hcontract.2.2 w).mp ⟨grouped i, hmemOutput, ⟨x, hx⟩⟩
      have hinSupport : ∃ j, w ∈ packetEmbeddingSupport (state.packets j) := by
        obtain ⟨j, hj⟩ := hin
        exact ⟨j, (packetEmbeddingSupport_mem_iff _ _).mpr hj⟩
      have hwSupport : w ∈ Finset.univ.biUnion
          (fun j => packetEmbeddingSupport (state.packets j)) := by
        simpa only [Finset.mem_biUnion, Finset.mem_univ, true_and] using hinSupport
      rw [state.support_eq] at hwSupport
      exact hwSupport
    · intro hw
      rw [← state.support_eq] at hw
      simp only [Finset.mem_biUnion, Finset.mem_univ, true_and] at hw
      have hwRange : ∃ j, w ∈ Set.range (state.packets j) := by
        obtain ⟨j, hj⟩ := hw
        exact ⟨j, (packetEmbeddingSupport_mem_iff _ _).mp hj⟩
      obtain ⟨p, hp, hpw⟩ := (hcontract.2.2 w).mpr hwRange
      have hmemGrouped : List.Mem p
          (List.ofFn (fourLaneBoundaryGroupedOutput state.packets state.disjoint)) :=
        hperm.mem_iff.mpr hp
      have hi : ∃ i, fourLaneBoundaryGroupedOutput state.packets state.disjoint i = p :=
        List.mem_ofFn.mp hmemGrouped
      obtain ⟨i, hi⟩ := hi
      cases hi
      obtain ⟨x, hx⟩ := hpw
      exact ⟨i, (packetEmbeddingSupport_mem_iff _ _).mpr ⟨x, hx⟩⟩
  refine ⟨{
    toIndexedPacketRoundState := {
      packets := grouped
      values := round.exec state.values
      disjoint := hgroupDisjoint
      sorted := hsorted
      support_eq := hsupp }
    packetStrictMono := hmono }, rfl, rfl, hdepth⟩

/-- After a four-lane boundary round on sixteen-packet cohorts, the newly
grouped output has the correct orientation for pairing across each boundary
between consecutive eight-packet blocks. This is the geometric input needed
by a wider next-stage matching. -/
theorem fourLaneBoundaryGroupedOutput_nextWideBoundaryEdge_ordered
    {s N : Nat}
    (packets : Fin (8 * (2 * s)) → Function.Embedding (Fin 64) (Fin N))
    (hdisjoint : ∀ i j, i ≠ j → ∀ x y, packets i x ≠ packets j y)
    (hblockOrdered : ∀ i j, i.val / 4 < j.val / 4 → ∀ x y,
      packets i x < packets j y)
    (j : Fin s) (x y : Fin 64) :
    fourLaneBoundaryGroupedOutput packets hdisjoint
        ⟨16 * j.val + 7, by have := j.isLt; omega⟩ x <
      fourLaneBoundaryGroupedOutput packets hdisjoint
        ⟨16 * j.val + 8, by have := j.isLt; omega⟩ y := by
  apply fourLaneBoundaryGroupedOutput_ordered packets hdisjoint hblockOrdered
  change (16 * j.val + 7) / 8 < (16 * j.val + 8) / 8
  omega

theorem indexedPacketPerfectMatching_preservesState {m N : Nat} {α : Type}
    [LinearOrder α] {support : Finset (Fin N)}
    (matching : IndexedPacketPerfectMatching m)
    (state : IndexedPacketRoundState m N α support) :
    ∃ next : IndexedPacketRoundState m N α support,
      next.values = (genIndexedPacketRound state.packets state.disjoint
        matching.edges matching.noFixed).exec state.values ∧
      (genIndexedPacketRound state.packets state.disjoint matching.edges
        matching.noFixed).depth ≤ 7 := by
  obtain ⟨packets, hsorted, hdisjoint, hsupp, hdepth⟩ :=
    genIndexedPacketRound_canonicalOutput_fixedCount state.packets
      state.disjoint matching.edges matching.nodup matching.noFixed
      matching.vertexDisjoint matching.covers matching.edgeCount state.values
      state.sorted
  refine ⟨⟨packets,
      (genIndexedPacketRound state.packets state.disjoint matching.edges
        matching.noFixed).exec state.values,
      hdisjoint, ?_, ?_⟩, rfl, hdepth⟩
  · simpa using hsorted
  · calc
      Finset.univ.biUnion (fun i => packetEmbeddingSupport (packets i)) =
          Finset.univ.biUnion (fun i => packetEmbeddingSupport (state.packets i)) := hsupp
      _ = support := state.support_eq

/-- A singleton-aware partial matching also preserves the packet state. -/
theorem indexedPacketMatching_preservesState {m N : Nat} {α : Type}
    [LinearOrder α] {support : Finset (Fin N)}
    (matching : IndexedPacketMatching m)
    (state : IndexedPacketRoundState m N α support) :
    ∃ next : IndexedPacketRoundState m N α support,
      next.values = (genIndexedPacketRound state.packets state.disjoint
        matching.edges matching.noFixed).exec state.values ∧
      (genIndexedPacketRound state.packets state.disjoint matching.edges
        matching.noFixed).depth ≤ 7 := by
  obtain ⟨packets, hsorted, hdisjoint, hsupp, hdepth⟩ :=
    genIndexedPacketRound_withSingletons_canonicalOutput_fixedCount
      state.packets state.disjoint matching.edges matching.nodup
      matching.noFixed matching.vertexDisjoint matching.singles
      (by
        have haux : ∀ ids : List (Fin m), List.Pairwise (fun i j => i ≠ j) ids →
            List.Pairwise
              (fun i j => ∀ x y, state.packets i x ≠ state.packets j y) ids := by
          intro ids hids
          induction ids with
          | nil => simp
          | cons i ids ih =>
              rcases List.pairwise_cons.mp hids with ⟨hhead, htail⟩
              apply List.pairwise_cons.mpr
              constructor
              · intro j hj x y
                exact state.disjoint i j (hhead j hj) x y
              · exact ih htail
        exact haux matching.singles matching.singleDisjoint)
      matching.free matching.covers matching.count state.values state.sorted
  refine ⟨⟨packets,
      (genIndexedPacketRound state.packets state.disjoint matching.edges
        matching.noFixed).exec state.values,
      hdisjoint, ?_, ?_⟩, rfl, hdepth⟩
  · simpa using hsorted
  · calc
      Finset.univ.biUnion (fun i => packetEmbeddingSupport (packets i)) =
          Finset.univ.biUnion (fun i => packetEmbeddingSupport (state.packets i)) := hsupp
      _ = support := state.support_eq

/-- A physically ordered partial matching preserves the stronger state
invariant that every logical packet embedding is the physical rank ordering
of its support. The hypothesis that each edge joins two separated supports is
the exact extra condition needed for this conclusion. -/
theorem indexedPacketMatching_preservesPhysicalState {m N : Nat} {α : Type}
    [LinearOrder α] {support : Finset (Fin N)}
    (matching : IndexedPacketMatching m)
    (state : IndexedPacketPhysicalRoundState m N α support)
    (hordered : ∀ e ∈ matching.edges, ∀ x y,
      state.packets e.1 x < state.packets e.2 y) :
    ∃ next : IndexedPacketPhysicalRoundState m N α support,
      next.values = (genIndexedPacketRound state.packets state.disjoint
        matching.edges matching.noFixed).exec state.values ∧
      (genIndexedPacketRound state.packets state.disjoint matching.edges
        matching.noFixed).depth ≤ 7 := by
  have hsingleDisjoint : List.Pairwise
      (fun i j => ∀ x y, state.packets i x ≠ state.packets j y) matching.singles := by
    have haux : ∀ ids : List (Fin m), List.Pairwise (fun i j => i ≠ j) ids →
        List.Pairwise
          (fun i j => ∀ x y, state.packets i x ≠ state.packets j y) ids := by
      intro ids hids
      induction ids with
      | nil => simp
      | cons i ids ih =>
          rcases List.pairwise_cons.mp hids with ⟨hhead, htail⟩
          apply List.pairwise_cons.mpr
          constructor
          · intro j hj x y
            exact state.disjoint i j (hhead j hj) x y
          · exact ih htail
    exact haux matching.singles matching.singleDisjoint
  let output := genIndexedPacketRoundOutputWithSingletons state.packets
    state.disjoint matching.edges matching.noFixed matching.singles
  have hcontract := genIndexedPacketRound_withSingletons_contract
    state.packets state.disjoint matching.edges matching.nodup matching.noFixed
    matching.vertexDisjoint matching.singles hsingleDisjoint matching.free
    matching.covers state.values state.sorted
  have hsortedList : ∀ p ∈ output,
      Monotone (fun k => (genIndexedPacketRound state.packets state.disjoint
        matching.edges matching.noFixed).exec state.values (p k)) := by
    simpa [output, genIndexedPacketRoundOutputWithSingletons] using hcontract.1
  have hdisjointList : List.Pairwise
      (fun p q : Fin 64 ↪ Fin N => ∀ x y, p x ≠ q y) output := by
    simpa [output, genIndexedPacketRoundOutputWithSingletons] using hcontract.2.1
  have hsupportList : ∀ w,
      (∃ p ∈ output, w ∈ Set.range p) ↔
        ∃ i, w ∈ Set.range (state.packets i) := by
    intro w
    simpa [output, genIndexedPacketRoundOutputWithSingletons] using hcontract.2.2 w
  have hdepth : (genIndexedPacketRound state.packets state.disjoint
      matching.edges matching.noFixed).depth ≤ 7 :=
    genIndexedPacketRound_depth_le state.packets state.disjoint matching.edges
      matching.nodup matching.noFixed matching.vertexDisjoint
  have hmonoList := genIndexedPacketRound_withSingletons_output_strictMono
    state.packets state.disjoint matching.edges matching.noFixed matching.singles
    state.packetStrictMono hordered
  have houtputLen : output.length = m := by
    have hmatchedLen :
        (genIndexedPacketRoundOutput state.packets state.disjoint
          matching.edges matching.noFixed).length = 2 * matching.edges.length := by
      have hsum : ∀ xs : List {e // e ∈ matching.edges},
          (xs.map fun _ => 2).sum = 2 * xs.length := by
        intro xs
        induction xs with
        | nil => simp
        | cons e xs ih =>
            simp only [List.map_cons, List.sum_cons, List.length_cons]
            rw [ih]
            omega
      simpa [genIndexedPacketRoundOutput, genPacketRound_outputPackets,
        genIndexedPairSupports, List.length_flatMap, Function.comp_def] using
        hsum matching.edges.attach
    simp [output, genIndexedPacketRoundOutputWithSingletons,
      List.length_append, List.length_map, hmatchedLen]
    have hcount := matching.count
    omega
  let next : Fin m → Fin 64 ↪ Fin N := fun i =>
    output.get (Fin.cast houtputLen.symm i)
  have hmonoNext : ∀ i, StrictMono (next i) := by
    intro i
    exact hmonoList _ (List.get_mem output (Fin.cast houtputLen.symm i))
  have hsortedNext : ∀ i, Monotone (fun k =>
      (genIndexedPacketRound state.packets state.disjoint matching.edges
        matching.noFixed).exec state.values (next i k)) := by
    intro i
    exact hsortedList _ (List.get_mem output (Fin.cast houtputLen.symm i))
  have hdisjointNext : ∀ i j, i ≠ j → ∀ x y, next i x ≠ next j y := by
    intro i j hij x y
    have hne : Fin.cast houtputLen.symm i ≠ Fin.cast houtputLen.symm j := by
      intro h
      apply hij
      apply Fin.ext
      have hv := congrArg Fin.val h
      simpa using hv
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact hdisjointList.rel_get_of_lt hlt x y
    · exact (hdisjointList.rel_get_of_lt hgt y x).symm
  have hsupportNext : Finset.univ.biUnion
      (fun i => packetEmbeddingSupport (next i)) =
      Finset.univ.biUnion (fun i => packetEmbeddingSupport (state.packets i)) := by
    ext w
    have hout : w ∈ Finset.univ.biUnion
        (fun i => packetEmbeddingSupport (next i)) ↔
        ∃ p ∈ output, w ∈ Set.range p := by
      simp only [Finset.mem_biUnion, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨i, hi⟩
        exact ⟨output.get (Fin.cast houtputLen.symm i),
          List.get_mem output (Fin.cast houtputLen.symm i),
          (packetEmbeddingSupport_mem_iff _ _).mp hi⟩
      · rintro ⟨p, hp, hw⟩
        obtain ⟨i, hi⟩ :=
          (List.exists_mem_iff_get (l := output) (p := fun z => z = p)).mp
            ⟨p, hp, rfl⟩
        refine ⟨Fin.cast houtputLen i, ?_⟩
        change w ∈ packetEmbeddingSupport (output.get (Fin.cast houtputLen.symm
          (Fin.cast houtputLen i)))
        rw [Fin.cast_trans, Fin.cast_eq_self, hi]
        exact (packetEmbeddingSupport_mem_iff _ _).mpr hw
    have hin : w ∈ Finset.univ.biUnion
        (fun i => packetEmbeddingSupport (state.packets i)) ↔
        ∃ i, w ∈ Set.range (state.packets i) := by
      simp only [Finset.mem_biUnion, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨i, hi⟩
        exact ⟨i, (packetEmbeddingSupport_mem_iff _ _).mp hi⟩
      · rintro ⟨i, hi⟩
        exact ⟨i, (packetEmbeddingSupport_mem_iff _ _).mpr hi⟩
    rw [hout, hsupportList w, hin]
  refine ⟨{
    toIndexedPacketRoundState := {
      packets := next
      values := (genIndexedPacketRound state.packets state.disjoint
        matching.edges matching.noFixed).exec state.values
      disjoint := hdisjointNext
      sorted := hsortedNext
      support_eq := hsupportNext.trans state.support_eq
    }
    packetStrictMono := hmonoNext
  }, rfl, hdepth⟩

/-- The boundary matching gives a genuine next round for a family of
two-lane blocks. It preserves packet sortedness, disjointness, exact support,
and strict physical order, with the checked seven-layer depth. -/
theorem interBlockBoundaryMatching_preservesPhysicalState {r N : Nat} {α : Type}
    [LinearOrder α]
    (packets : Fin (2 * (2 * r)) → Fin 64 ↪ Fin N)
    (v : Fin N → α)
    (hdisjoint : ∀ i j, i ≠ j → ∀ x y, packets i x ≠ packets j y)
    (hsorted : ∀ i, Monotone (fun x => v (packets i x)))
    (hmono : ∀ i, StrictMono (packets i))
    (hblockOrdered : ∀ i j, i.val / 2 < j.val / 2 → ∀ x y,
      packets i x < packets j y) :
    let support := Finset.univ.biUnion (fun i => packetEmbeddingSupport (packets i))
    ∃ next : IndexedPacketPhysicalRoundState (2 * (2 * r)) N α support,
      next.values = (genIndexedPacketRound packets hdisjoint
        (interBlockBoundaryMatching r).edges
        (interBlockBoundaryMatching r).noFixed).exec v ∧
      (genIndexedPacketRound packets hdisjoint (interBlockBoundaryMatching r).edges
        (interBlockBoundaryMatching r).noFixed).depth ≤ 7 := by
  let support := Finset.univ.biUnion
    (fun i => packetEmbeddingSupport (packets i))
  let state : IndexedPacketPhysicalRoundState (2 * (2 * r)) N α support := {
    toIndexedPacketRoundState := {
      packets := packets
      values := v
      disjoint := hdisjoint
      sorted := hsorted
      support_eq := rfl
    }
    packetStrictMono := hmono
  }
  have hordered := interBlockBoundaryMatching_ordered packets hblockOrdered
  simpa [interBlockBoundaryMatching, state, support] using
    (indexedPacketMatching_preservesPhysicalState
      (interBlockBoundaryMatching r) state hordered)

/-- Flatten the grouped output blocks in block-major, lane-minor order. -/
def adjacentPacketMatchingFlattenedOutput {k N : Nat}
    (packets : Fin (2 * k) → Fin 64 ↪ Fin N)
    (hordered : ∀ p q, p.val < q.val → ∀ i j, packets p i < packets q j)
    (i : Fin (2 * k)) : Fin 64 ↪ Fin N :=
  adjacentPacketMatchingOutputBlock packets hordered
    ⟨i.val / 2, by have := i.isLt; omega⟩ (decide (i.val % 2 = 1))

/-- The flattened two-lane output blocks of an adjacent perfect matching form
the exact input interface needed by `interBlockBoundaryMatching`: every
packet remains sorted and physically increasing, different packets are
disjoint, and all packets in an earlier block precede those in a later block. -/
theorem adjacentPacketMatchingFlattenedOutput_contract {k N : Nat} {α : Type}
    [LinearOrder α]
    (packets : Fin (2 * k) → Fin 64 ↪ Fin N)
    (hpacketDisjoint : ∀ i j, i ≠ j → ∀ x y, packets i x ≠ packets j y)
    (hordered : ∀ p q, p.val < q.val → ∀ i j, packets p i < packets q j)
    (v : Fin N → α)
    (hsorted : ∀ p, Monotone (fun i => v (packets p i)))
    (hmono : ∀ p, StrictMono (packets p)) :
    (∀ i, Monotone (fun x =>
      (genIndexedPacketRound packets hpacketDisjoint (adjacentPacketMatching k)
        (adjacentPacketMatching_noFixed k)).exec v
        (adjacentPacketMatchingFlattenedOutput packets hordered i x))) ∧
    (∀ i, StrictMono (adjacentPacketMatchingFlattenedOutput packets hordered i)) ∧
    (∀ i j, i ≠ j → ∀ x y,
      adjacentPacketMatchingFlattenedOutput packets hordered i x ≠
        adjacentPacketMatchingFlattenedOutput packets hordered j y) ∧
    (∀ i j, i.val / 2 < j.val / 2 → ∀ x y,
      adjacentPacketMatchingFlattenedOutput packets hordered i x <
        adjacentPacketMatchingFlattenedOutput packets hordered j y) := by
  let block (i : Fin (2 * k)) : Fin k :=
    ⟨i.val / 2, by have := i.isLt; omega⟩
  let lane (i : Fin (2 * k)) : Bool := decide (i.val % 2 = 1)
  have hcontract (i : Fin (2 * k)) :=
    adjacentPacketMatchingOutputBlock_contract packets hpacketDisjoint hordered
      v hsorted hmono (block i) (lane i)
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i
    simpa [adjacentPacketMatchingFlattenedOutput, block, lane] using (hcontract i).2.1
  · intro i
    simpa [adjacentPacketMatchingFlattenedOutput, block, lane] using
      (hcontract i).2.2.1
  · intro i j hij x y
    by_cases hblock : block i = block j
    · have hlane : lane i ≠ lane j := by
        intro h
        apply hij
        apply Fin.ext
        have hb := congrArg Fin.val hblock
        have hl := congrArg id h
        simp [block, lane] at hb hl
        omega
      simpa [adjacentPacketMatchingFlattenedOutput, block, lane, hblock.symm] using
        (hcontract i).2.2.2.2.1 (lane j) x y hlane
    · by_cases hlt : (block i).val < (block j).val
      · have hsep := (hcontract i).2.2.2.1 (block j) hlt (lane j) x y
        simpa [adjacentPacketMatchingFlattenedOutput, block, lane] using ne_of_lt hsep
      · have hgt : (block j).val < (block i).val := by
          have hne : (block i).val ≠ (block j).val := by
            intro h
            apply hblock
            exact Fin.ext h
          omega
        have hsep := (hcontract j).2.2.2.1 (block i) hgt (lane i) y x
        simpa [adjacentPacketMatchingFlattenedOutput, block, lane] using
          (ne_of_lt hsep).symm
  · intro i j hij x y
    have hlt : (block i).val < (block j).val := by
      simpa [block] using hij
    simpa [adjacentPacketMatchingFlattenedOutput, block, lane] using
      (hcontract i).2.2.2.1 (block j) hlt (lane j) x y

/-- Instantiate the grouped-output adapter followed by the inter-block
boundary matching. This proves two consecutive seven-layer rounds preserve a
physically ordered packet state when the second round is matched across the
first round's ordered two-lane blocks. -/
theorem adjacentThenBoundaryMatching_preservesPhysicalState
    {r N : Nat} {α : Type} [LinearOrder α]
    (packets : Fin (2 * (2 * r)) → Fin 64 ↪ Fin N)
    (v : Fin N → α)
    (hpacketDisjoint : ∀ i j, i ≠ j → ∀ x y, packets i x ≠ packets j y)
    (hsorted : ∀ i, Monotone (fun x => v (packets i x)))
    (hmono : ∀ i, StrictMono (packets i))
    (hordered : ∀ i j, i.val < j.val → ∀ x y, packets i x < packets j y) :
    let first := genIndexedPacketRound packets hpacketDisjoint
      (adjacentPacketMatching (2 * r)) (adjacentPacketMatching_noFixed (2 * r))
    let output := adjacentPacketMatchingFlattenedOutput packets hordered
    ∃ next : IndexedPacketPhysicalRoundState (2 * (2 * r)) N α
        (Finset.univ.biUnion (fun i => packetEmbeddingSupport (output i))),
      next.values = (genIndexedPacketRound output
        (adjacentPacketMatchingFlattenedOutput_contract packets hpacketDisjoint
          hordered v hsorted hmono).2.2.1
        (interBlockBoundaryMatching r).edges
        (interBlockBoundaryMatching r).noFixed).exec (first.exec v) ∧
      first.depth ≤ 7 ∧
      (genIndexedPacketRound output
        (adjacentPacketMatchingFlattenedOutput_contract packets hpacketDisjoint
          hordered v hsorted hmono).2.2.1
        (interBlockBoundaryMatching r).edges
        (interBlockBoundaryMatching r).noFixed).depth ≤ 7 := by
  dsimp
  let first := genIndexedPacketRound packets hpacketDisjoint
    (adjacentPacketMatching (2 * r)) (adjacentPacketMatching_noFixed (2 * r))
  let output := adjacentPacketMatchingFlattenedOutput packets hordered
  have hout := adjacentPacketMatchingFlattenedOutput_contract packets
    hpacketDisjoint hordered v hsorted hmono
  obtain ⟨next, hnextValues, hnextDepth⟩ :=
    interBlockBoundaryMatching_preservesPhysicalState output (first.exec v)
      hout.2.2.1 hout.1 hout.2.1 hout.2.2.2
  have hfirstDepth : first.depth ≤ 7 := by
    dsimp [first]
    exact genIndexedPacketRound_depth_le packets hpacketDisjoint
      (adjacentPacketMatching (2 * r))
      (adjacentPacketMatching_nodup (2 * r))
      (adjacentPacketMatching_noFixed (2 * r))
      (adjacentPacketMatching_vertexDisjoint (2 * r))
  refine ⟨next, ?_, hfirstDepth, hnextDepth⟩
  simpa [first, output] using hnextValues

/-- Iterate an adaptive policy that chooses the next partial matching from
the current physically ordered packet state. The policy must orient every
edge from the lower support to the higher one at each reached state. -/
noncomputable def iterateIndexedOrderedPacketMatchings {m N : Nat} {α : Type}
    [LinearOrder α] {support : Finset (Fin N)}
    (policy : IndexedPacketPhysicalRoundState m N α support → IndexedPacketMatching m)
    (hordered : ∀ state, ∀ e ∈ (policy state).edges, ∀ x y,
      state.packets e.1 x < state.packets e.2 y)
    (initial : IndexedPacketPhysicalRoundState m N α support) :
    Nat → IndexedPacketPhysicalRoundState m N α support
  | 0 => initial
  | n + 1 => Classical.choose
      (indexedPacketMatching_preservesPhysicalState (policy
        (iterateIndexedOrderedPacketMatchings policy hordered initial n))
        (iterateIndexedOrderedPacketMatchings policy hordered initial n)
        (hordered (iterateIndexedOrderedPacketMatchings policy hordered initial n)))

/-- Exact values and seven-layer depth for each adaptive, physically ordered
matching step. This does not assert any rank-profile contraction. -/
theorem iterateIndexedOrderedPacketMatchings_step {m N : Nat} {α : Type}
    [LinearOrder α] {support : Finset (Fin N)}
    (policy : IndexedPacketPhysicalRoundState m N α support → IndexedPacketMatching m)
    (hordered : ∀ state, ∀ e ∈ (policy state).edges, ∀ x y,
      state.packets e.1 x < state.packets e.2 y)
    (initial : IndexedPacketPhysicalRoundState m N α support) (n : Nat) :
    (iterateIndexedOrderedPacketMatchings policy hordered initial (n + 1)).values =
      (genIndexedPacketRound
        (iterateIndexedOrderedPacketMatchings policy hordered initial n).packets
        (iterateIndexedOrderedPacketMatchings policy hordered initial n).disjoint
        (policy (iterateIndexedOrderedPacketMatchings policy hordered initial n)).edges
        (policy (iterateIndexedOrderedPacketMatchings policy hordered initial n)).noFixed).exec
        (iterateIndexedOrderedPacketMatchings policy hordered initial n).values ∧
      (genIndexedPacketRound
        (iterateIndexedOrderedPacketMatchings policy hordered initial n).packets
        (iterateIndexedOrderedPacketMatchings policy hordered initial n).disjoint
        (policy (iterateIndexedOrderedPacketMatchings policy hordered initial n)).edges
        (policy (iterateIndexedOrderedPacketMatchings policy hordered initial n)).noFixed).depth ≤ 7 := by
  exact Classical.choose_spec
    (indexedPacketMatching_preservesPhysicalState (policy
      (iterateIndexedOrderedPacketMatchings policy hordered initial n))
      (iterateIndexedOrderedPacketMatchings policy hordered initial n)
      (hordered (iterateIndexedOrderedPacketMatchings policy hordered initial n)))

/-- Iterate a supplied schedule of arbitrary partial matchings. Each step
retains the state invariant, including when the packet count is odd. -/
noncomputable def iterateIndexedPacketMatchings {m N : Nat} {α : Type}
    [LinearOrder α] {support : Finset (Fin N)}
    (schedule : Nat → IndexedPacketMatching m)
    (initial : IndexedPacketRoundState m N α support) :
    Nat → IndexedPacketRoundState m N α support
  | 0 => initial
  | n + 1 => Classical.choose
      (indexedPacketMatching_preservesState (schedule n)
        (iterateIndexedPacketMatchings schedule initial n))

/-- Exact value recurrence and seven-layer cost for an arbitrary singleton-
aware schedule step. -/
theorem iterateIndexedPacketMatchings_step {m N : Nat} {α : Type}
    [LinearOrder α] {support : Finset (Fin N)}
    (schedule : Nat → IndexedPacketMatching m)
    (initial : IndexedPacketRoundState m N α support) (n : Nat) :
    (iterateIndexedPacketMatchings schedule initial (n + 1)).values =
      (genIndexedPacketRound
        (iterateIndexedPacketMatchings schedule initial n).packets
        (iterateIndexedPacketMatchings schedule initial n).disjoint
        (schedule n).edges (schedule n).noFixed).exec
        (iterateIndexedPacketMatchings schedule initial n).values ∧
    (genIndexedPacketRound
        (iterateIndexedPacketMatchings schedule initial n).packets
        (iterateIndexedPacketMatchings schedule initial n).disjoint
        (schedule n).edges (schedule n).noFixed).depth ≤ 7 := by
  simpa [iterateIndexedPacketMatchings] using
    Classical.choose_spec
      (indexedPacketMatching_preservesState (schedule n)
        (iterateIndexedPacketMatchings schedule initial n))

/-- Iterate any externally supplied sequence of perfect logical matchings.
The state type itself carries sortedness, disjointness, and support at every
time; `iterate..._step` records the exact network/value recurrence and its
seven-layer per-round cost. -/
noncomputable def iterateIndexedPacketPerfectMatchings {m N : Nat} {α : Type}
    [LinearOrder α] {support : Finset (Fin N)}
    (schedule : Nat → IndexedPacketPerfectMatching m)
    (initial : IndexedPacketRoundState m N α support) :
    Nat → IndexedPacketRoundState m N α support
  | 0 => initial
  | n + 1 => Classical.choose
      (indexedPacketPerfectMatching_preservesState (schedule n)
        (iterateIndexedPacketPerfectMatchings schedule initial n))

/-- One step of the iterated matching schedule is exactly the prescribed
seven-layer round, and has depth at most seven. -/
theorem iterateIndexedPacketPerfectMatchings_step {m N : Nat} {α : Type}
    [LinearOrder α] {support : Finset (Fin N)}
    (schedule : Nat → IndexedPacketPerfectMatching m)
    (initial : IndexedPacketRoundState m N α support) (n : Nat) :
    (iterateIndexedPacketPerfectMatchings schedule initial (n + 1)).values =
      (genIndexedPacketRound
        (iterateIndexedPacketPerfectMatchings schedule initial n).packets
        (iterateIndexedPacketPerfectMatchings schedule initial n).disjoint
        (schedule n).edges (schedule n).noFixed).exec
        (iterateIndexedPacketPerfectMatchings schedule initial n).values ∧
    (genIndexedPacketRound
        (iterateIndexedPacketPerfectMatchings schedule initial n).packets
        (iterateIndexedPacketPerfectMatchings schedule initial n).disjoint
        (schedule n).edges (schedule n).noFixed).depth ≤ 7 := by
  simpa [iterateIndexedPacketPerfectMatchings] using
    Classical.choose_spec
      (indexedPacketPerfectMatching_preservesState (schedule n)
        (iterateIndexedPacketPerfectMatchings schedule initial n))


end Chvatal.PacketAlignment
