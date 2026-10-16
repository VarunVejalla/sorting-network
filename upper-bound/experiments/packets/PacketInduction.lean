import PacketRepair64
import PacketGenMerge

/-! Canonical finite-index bridge from one generalized matching round to the
packet-family interface used by receiver induction. This file tracks logical
packet embeddings; it does not identify them with later positional
`WireFlow` cuts. -/

namespace Chvatal.PacketAlignment

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

end Chvatal.PacketAlignment
