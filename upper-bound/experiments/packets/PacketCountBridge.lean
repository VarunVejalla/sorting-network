import PacketSenderCycle

/-! Enumeration-independent threshold counts for the actual repair network.
The scalar energy theorem requires this bridge rather than just support unions. -/

namespace Chvatal.PacketAlignment

open Classical BigOperators

noncomputable def trueCountOn {N : Nat} (s : Finset (Fin N)) (v : Fin N → Bool) : Nat :=
  Fintype.card {w : s // v w.val = true}

theorem boolTrueCount_embedding {m N : Nat} (s : Finset (Fin N))
    (e : Fin m ↪ Fin N) (he : Set.range e = {w | w ∈ s}) (v : Fin N → Bool) :
    boolTrueCount (v ∘ e) = trueCountOn s v := by
  have hmem (i : Fin m) : e i ∈ s := by
    have h : e i ∈ Set.range e := ⟨i, rfl⟩
    rwa [he] at h
  let f : {i : Fin m // v (e i) = true} → {w : s // v w.val = true} :=
    fun i => ⟨⟨e i.val, hmem i.val⟩, i.property⟩
  apply Fintype.card_congr (Equiv.ofBijective f ?_)
  constructor
  · intro i j h
    apply Subtype.ext
    apply e.injective
    exact congrArg (fun z : {w : s // v w.val = true} => z.val.val) h
  · intro w
    have hw : w.val.val ∈ Set.range e := by rw [he]; exact w.val.property
    obtain ⟨i, hi⟩ := hw
    refine ⟨⟨i, by simpa only [hi] using w.property⟩, ?_⟩
    apply Subtype.ext
    exact Subtype.ext hi

theorem boolTrueCount_orderEmb {N m : Nat} (s : Finset (Fin N)) (hs : s.card = m)
    (v : Fin N → Bool) :
    boolTrueCount (v ∘ s.orderEmbOfFin hs) = trueCountOn s v := by
  apply boolTrueCount_embedding s (s.orderEmbOfFin hs).toEmbedding
  ext w
  constructor
  · rintro ⟨i, rfl⟩
    exact s.orderEmbOfFin_mem hs i
  · intro hw
    obtain ⟨i, hi⟩ := (s.orderIsoOfFin hs).surjective ⟨w, hw⟩
    exact ⟨i, congrArg Subtype.val hi⟩

theorem trueCountOn_pair {N : Nat} (A B : Finset (Fin N))
    (hA : A.card = 32) (hB : B.card = 32)
    (hsep : ∀ a ∈ A, ∀ b ∈ B, a < b) (v : Fin N → Bool) :
    trueCountOn (A ∪ B) v = trueCountOn A v + trueCountOn B v := by
  let e := orderedHalfPairEmbedding A B hA hB hsep
  have h := boolTrueCount_halves (m := 32) (v ∘ e)
  have htotal := boolTrueCount_embedding (A ∪ B) e.toEmbedding
    (orderedHalfPairEmbedding_range A B hA hB hsep) v
  change boolTrueCount (v ∘ e) = trueCountOn (A ∪ B) v at htotal
  have hl : (fun i : Fin 32 => (v ∘ e) (Fin.castAdd 32 i)) =
      v ∘ A.orderEmbOfFin hA := by
    funext i
    simp only [Function.comp_apply, e, orderedHalfPairEmbedding_left]
  have hr : (fun i : Fin 32 => (v ∘ e) (Fin.natAdd 32 i)) =
      v ∘ B.orderEmbOfFin hB := by
    funext i
    simp only [Function.comp_apply, e, orderedHalfPairEmbedding_right]
  rw [hl, hr, boolTrueCount_orderEmb, boolTrueCount_orderEmb, htotal] at h
  omega

/-- Sorted physical half-pairs realize the exact complementary count split. -/
theorem trueCountOn_sorted_halves {N : Nat} (A B : Finset (Fin N))
    (hA : A.card = 32) (hB : B.card = 32)
    (hsep : ∀ a ∈ A, ∀ b ∈ B, a < b) (v : Fin N → Bool)
    (hv : RankSortedOn (A ∪ B) v) :
    trueCountOn A v = trueCountOn (A ∪ B) v - 32 ∧
      trueCountOn B v = min 32 (trueCountOn (A ∪ B) v) := by
  let e := orderedHalfPairEmbedding A B hA hB hsep
  have hmono : Monotone (v ∘ e) := by
    intro i j hij
    have hmem (k : Fin 64) : e k ∈ A ∪ B := by
      have h : e k ∈ Set.range e := ⟨k, rfl⟩
      rwa [show Set.range e = {w | w ∈ A ∪ B} from
        orderedHalfPairEmbedding_range A B hA hB hsep] at h
    apply hv (hmem i) (hmem j)
    exact Fin.le_iff_val_le_val.mp (e.monotone hij)
  have h := sorted_bool_halves_trueCount (m := 32) (v ∘ e) hmono
  have htotal := boolTrueCount_embedding (A ∪ B) e.toEmbedding
    (orderedHalfPairEmbedding_range A B hA hB hsep) v
  change boolTrueCount (v ∘ e) = trueCountOn (A ∪ B) v at htotal
  have hl : (fun i : Fin 32 => (v ∘ e) (Fin.castAdd 32 i)) =
      v ∘ A.orderEmbOfFin hA := by
    funext i
    simp only [Function.comp_apply, e, orderedHalfPairEmbedding_left]
  have hr : (fun i : Fin 32 => (v ∘ e) (Fin.natAdd 32 i)) =
      v ∘ B.orderEmbOfFin hB := by
    funext i
    simp only [Function.comp_apply, e, orderedHalfPairEmbedding_right]
  rwa [hl, hr, boolTrueCount_orderEmb, boolTrueCount_orderEmb, htotal] at h

/-- Parallel repairs preserve each consumed pair's count separately. -/
theorem parallelHalfPairRepair_trueCountOn {ι : Type} [DecidableEq ι]
    {N : Nat} (ids : List ι) (hids : ids.Nodup) (A B : ι → Finset (Fin N))
    (hA : ∀ a, (A a).card = 32) (hB : ∀ a, (B a).card = 32)
    (hsep : ∀ a, ∀ x ∈ A a, ∀ y ∈ B a, x < y)
    (hdis : ∀ a ∈ ids, ∀ b ∈ ids, a ≠ b → Disjoint (A a ∪ B a) (A b ∪ B b))
    (v : Fin N → Bool) (a : ι) (ha : a ∈ ids) :
    trueCountOn (A a ∪ B a) ((parallelHalfPairRepair ids A B hA hB hsep).exec v) =
      trueCountOn (A a ∪ B a) v := by
  let e := orderedHalfPairEmbedding (A a) (B a) (hA a) (hB a) (hsep a)
  have he := orderedHalfPairEmbedding_range (A a) (B a) (hA a) (hB a) (hsep a)
  rw [← boolTrueCount_embedding _ e.toEmbedding he,
    ← boolTrueCount_embedding _ e.toEmbedding he]
  change boolTrueCount ((parallelHalfPairRepair ids A B hA hB hsep).exec v ∘ e) =
    boolTrueCount (v ∘ e)
  have hexec : (parallelHalfPairRepair ids A B hA hB hsep).exec v ∘ e =
      (oddEvenMergeNet 6).exec (v ∘ e) := by
    funext i
    exact parallelHalfPairRepair_exec_inside ids hids A B hA hB hsep hdis v a ha i
  rw [hexec, boolTrueCount_exec]

theorem senderBoundary_half_properties {N : Nat} (s : Finset (Fin N)) (up down : Nat)
    (hs : s.card = up + 64 * down) (hu : 2 ∣ up)
    (hshift : up / 2 % 64 = 32) (i : Fin 65) :
    (senderBoundaryPrefix s up down i).card = 32 ∧
      (senderBoundarySuffix s up down i).card = 32 ∧
      ∀ a ∈ senderBoundaryPrefix s up down i,
        ∀ b ∈ senderBoundarySuffix s up down i, a < b := by
  let c := senderBoundaryCut up down i
  have hhalf : 32 ≤ up / 2 := by omega
  have hmul : i.val * down ≤ 64 * down := Nat.mul_le_mul_right down (by omega)
  have hueq := Nat.div_mul_cancel hu
  have hlo : 32 ≤ c := by dsimp [c, senderBoundaryCut]; omega
  have hhi : c + 32 ≤ s.card := by dsimp [c, senderBoundaryCut]; omega
  have hspan : 64 ≤ (c + 32) - (c - 32) := by omega
  have he : c - 32 + 32 = c := by omega
  have he' : c + 32 - 32 = c := by omega
  have hp := rankInterval_endpoint_pair s (c - 32) (c + 32) hspan hhi
  simp only [he, he'] at hp
  refine ⟨hp.2.1, hp.2.2.1, ?_⟩
  intro a ha b hb
  apply rankInterval_endpoint_pair_ordered s (c - 32) (c + 32) hspan
  · simpa only [he] using ha
  · simpa only [he'] using hb

theorem senderBoundary_half_counts {N : Nat} (s : Finset (Fin N)) (up down : Nat)
    (hs : s.card = up + 64 * down) (hu : 2 ∣ up)
    (hshift : up / 2 % 64 = 32) (hdiv : 64 ∣ down)
    (v : Fin N → Bool) (hv : PacketSortedOn s v) (i : Fin 65) :
    trueCountOn (senderBoundaryPrefix s up down i) v =
        trueCountOn (senderBoundaryCell s up down i) v - 32 ∧
      trueCountOn (senderBoundarySuffix s up down i) v =
        min 32 (trueCountOn (senderBoundaryCell s up down i) v) := by
  have hp := senderBoundary_half_properties s up down hs hu hshift i
  apply trueCountOn_sorted_halves _ _ hp.1 hp.2.1 hp.2.2
  change RankSortedOn (senderBoundaryCell s up down i) v
  rw [senderBoundaryCell_packet s up down hshift hdiv i]
  exact hv _

/-- Any execution preserving the actual repaired pair counts realizes the
65-cycle scalar model exactly. This includes the fixed parallel merge. -/
theorem senderRepair_rebin_count {N : Nat} (s : Finset (Fin N)) (up down : Nat)
    (hs : s.card = up + 64 * down) (hu : 2 ∣ up) (hc : 64 ∣ s.card)
    (hshift : up / 2 % 64 = 32) (hd : 64 ≤ down) (hdiv : 64 ∣ down)
    (v out : Fin N → Bool) (hv : PacketSortedOn s v)
    (hpres : ∀ i : Fin 65,
      trueCountOn (senderRepairLeft s up down i ∪ senderRepairRight s up down i) out =
      trueCountOn (senderRepairLeft s up down i ∪ senderRepairRight s up down i) v)
    (i : Fin 65) :
    trueCountOn (senderRepairLeft s up down i ∪ senderRepairRight s up down i) out =
      halfRebin 32 (fun j => trueCountOn (senderBoundaryCell s up down j) v) (finRotate 65) i := by
  rw [hpres]
  have hp := senderRepair_pair_properties s up down hs hu hc hshift hd i
  rw [trueCountOn_pair _ _ hp.1 hp.2.1 hp.2.2]
  have hiCount := senderBoundary_half_counts s up down hs hu hshift hdiv v hv i
  have hnCount := senderBoundary_half_counts s up down hs hu hshift hdiv v hv (finRotate 65 i)
  unfold halfRebin
  by_cases hi : i.val < 64
  · have hr : finRotate 65 i = ⟨i.val + 1, by omega⟩ := finRotate_of_lt hi
    have hl : senderRepairLeft s up down i = senderBoundarySuffix s up down i := by
      simp only [senderRepairLeft, if_pos hi, senderBoundarySuffix, senderBoundaryCut]
    have hright : senderRepairRight s up down i =
        senderBoundaryPrefix s up down (finRotate 65 i) := by
      simp only [senderRepairRight, if_pos hi, senderBoundaryPrefix, senderBoundaryCut, hr, Fin.val_mk]
    rw [hl, hright, hiCount.2, hnCount.1]
  · have hi64 : i.val = 64 := by have := i.isLt; omega
    have hiLast : i = Fin.last 64 := Fin.ext hi64
    have hr : finRotate 65 i = 0 := by rw [hiLast, finRotate_last]
    have hueq := Nat.div_mul_cancel hu
    have he : s.card - up / 2 = up / 2 + 64 * down := by omega
    have hl : senderRepairLeft s up down i =
        senderBoundaryPrefix s up down (finRotate 65 i) := by
      simp only [senderRepairLeft, if_neg hi, senderBoundaryPrefix, senderBoundaryCut,
        hr, Fin.val_zero, Nat.zero_mul, Nat.add_zero]
    have hright : senderRepairRight s up down i = senderBoundarySuffix s up down i := by
      simp only [senderRepairRight, senderBoundarySuffix, senderBoundaryCut, hi64, he,
        show ¬ (64 : Nat) < 64 by omega, if_false]
    rw [hl, hright, hnCount.1, hiCount.2, Nat.add_comm]

/-- The executed repair creates no sender-centered squared-count energy.
The reference may be the sender's fractional mean. -/
theorem senderRepair_centered_energy_le {N : Nat} (s : Finset (Fin N)) (up down : Nat)
    (hs : s.card = up + 64 * down) (hu : 2 ∣ up) (hc : 64 ∣ s.card)
    (hshift : up / 2 % 64 = 32) (hd : 64 ≤ down) (hdiv : 64 ∣ down)
    (v out : Fin N → Bool) (hv : PacketSortedOn s v)
    (hpres : ∀ i : Fin 65,
      trueCountOn (senderRepairLeft s up down i ∪ senderRepairRight s up down i) out =
      trueCountOn (senderRepairLeft s up down i ∪ senderRepairRight s up down i) v)
    (μ : Real) :
    (∑ i : Fin 65, ((trueCountOn
      (senderRepairLeft s up down i ∪ senderRepairRight s up down i) out : Real) - μ)^2) ≤
      ∑ i : Fin 65, ((trueCountOn (senderBoundaryCell s up down i) v : Real) - μ)^2 := by
  simp_rw [senderRepair_rebin_count s up down hs hu hc hshift hd hdiv v out hv hpres]
  exact halfRebin_centered_energy_le 32 _ (finRotate 65) μ

/-- A fixed six-layer network realizes the 65-cycle count transformation.
No choice of its comparators depends on the input or on a threshold. -/
theorem senderRepair_count_exists {N : Nat} (s : Finset (Fin N)) (up down : Nat)
    (hs : s.card = up + 64 * down) (hu : 2 ∣ up) (hc : 64 ∣ s.card)
    (hshift : up / 2 % 64 = 32) (hd : 64 ≤ down) (hdiv : 64 ∣ down) :
    ∃ net : ComparatorNetwork N, net.depth ≤ 6 ∧
      (∀ {α : Type} [LinearOrder α] (v : Fin N → α), PacketSortedOn s v →
        ∀ i : Fin 65, RankSortedOn
          (senderRepairLeft s up down i ∪ senderRepairRight s up down i) (net.exec v)) ∧
      (∀ v : Fin N → Bool, PacketSortedOn s v → ∀ i : Fin 65,
        trueCountOn (senderRepairLeft s up down i ∪ senderRepairRight s up down i) (net.exec v) =
        halfRebin 32 (fun j => trueCountOn (senderBoundaryCell s up down j) v) (finRotate 65) i) ∧
      (∀ v : Fin N → Bool, PacketSortedOn s v → ∀ μ : Real,
        (∑ i : Fin 65, ((trueCountOn
          (senderRepairLeft s up down i ∪ senderRepairRight s up down i) (net.exec v) : Real) - μ)^2) ≤
        ∑ i : Fin 65, ((trueCountOn (senderBoundaryCell s up down i) v : Real) - μ)^2) ∧
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
  let net := parallelHalfPairRepair (List.finRange 65) A B hA hB hsep
  have hpres (v : Fin N → Bool) (i : Fin 65) :
      trueCountOn (A i ∪ B i) (net.exec v) = trueCountOn (A i ∪ B i) v :=
    parallelHalfPairRepair_trueCountOn _ (List.nodup_finRange 65) A B hA hB hsep hdis
      v i (List.mem_finRange i)
  refine ⟨net, parallelHalfPairRepair_depth_le _ (List.nodup_finRange 65) A B hA hB hsep hdis,
    ?_, ?_, ?_, ?_⟩
  · intro α _ v hv i
    obtain ⟨hl, hr⟩ := senderRepair_inputs_sorted s up down v hs hc hshift hd hdiv hv i
    exact parallelHalfPairRepair_sorts_pair _ (List.nodup_finRange 65) A B hA hB hsep hdis
      v i (List.mem_finRange i) hl hr
  · intro v hv i
    exact senderRepair_rebin_count s up down hs hu hc hshift hd hdiv v (net.exec v) hv (hpres v) i
  · intro v hv μ
    exact senderRepair_centered_energy_le s up down hs hu hc hshift hd hdiv v (net.exec v) hv (hpres v) μ
  · intro α _ v w hw
    unfold net parallelHalfPairRepair repairOrderedHalfPair
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

theorem packetSortedOn_threshold {N : Nat} {α : Type} [LinearOrder α]
    (s : Finset (Fin N)) (v : Fin N → α) (hv : PacketSortedOn s v) (t : α) :
    PacketSortedOn s (fun w => decide (t ≤ v w)) := by
  have hm : Monotone (fun x : α => decide (t ≤ x)) := by
    intro x y hxy
    by_cases hx : t ≤ x
    · have hy : t ≤ y := hx.trans hxy
      simp [hx, hy]
    · simp [hx]
  intro p x y hx hy hxy
  exact hm (hv p hx hy hxy)

/-- A Boolean execution contract holds simultaneously at every value threshold
of the same fixed comparator network. -/
theorem senderRepair_count_at_threshold {N : Nat} {α : Type} [LinearOrder α]
    (s : Finset (Fin N)) (up down : Nat) (net : ComparatorNetwork N)
    (hcount : ∀ v : Fin N → Bool, PacketSortedOn s v → ∀ i : Fin 65,
      trueCountOn (senderRepairLeft s up down i ∪ senderRepairRight s up down i) (net.exec v) =
      halfRebin 32 (fun j => trueCountOn (senderBoundaryCell s up down j) v) (finRotate 65) i)
    (v : Fin N → α) (hv : PacketSortedOn s v) (t : α) (i : Fin 65) :
    trueCountOn (senderRepairLeft s up down i ∪ senderRepairRight s up down i)
        (fun w => decide (t ≤ net.exec v w)) =
      halfRebin 32 (fun j => trueCountOn (senderBoundaryCell s up down j)
        (fun w => decide (t ≤ v w))) (finRotate 65) i := by
  have h := hcount (fun w => decide (t ≤ v w)) (packetSortedOn_threshold s v hv t) i
  rwa [exec_threshold] at h

end Chvatal.PacketAlignment
