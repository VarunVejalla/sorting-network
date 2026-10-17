import PacketRepair64
import PacketGenMerge
import PacketMergeTreeGen
import AKS.Chvatal.RealBlocks

/-! Canonical finite-index bridge from one generalized matching round to the
packet-family interface used by receiver induction. This file tracks logical
packet embeddings; it does not identify them with later positional
`WireFlow` cuts. -/

namespace Chvatal.PacketAlignment

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
      (∀ e ∈ blocks, ∀ j : Fin (packetPowerTree6 (α := α)).leafCount,
        Monotone (fun i =>
          (genScatterMergeTreeBatch (packetPowerTree6 (α := α)) blocks).exec
            ((flowA7_sourcePortRepairStage hd t ht2 ht).exec v)
            (genScatterMergeTreeOutputEmbedding (packetPowerTree6 (α := α)) e j i))) := by
  obtain ⟨m, packets, hsorted, hdis, hcover, hcount⟩ :=
    flowA7_receiver_allCases_packetCount hd t ht2 ht b hb hchild v hpack
  have hdivM : 64 ∣ m := by
    simpa [hcount] using hdiv
  obtain ⟨blocks, hnodup, hblocksDisjoint, hdepth, hsortedOut⟩ :=
    packetFamily_divisible64_merge packets hdivM hdis
      ((flowA7_sourcePortRepairStage hd t ht2 ht).exec v) hsorted
  exact ⟨blocks, hnodup, hblocksDisjoint, hdepth, hsortedOut⟩

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

/-- Every perfect logical matching round maps a valid state back into the same
state interface. This is the induction step needed to iterate an arbitrary
matching schedule; the schedule still needs a separate contraction theorem. -/
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
