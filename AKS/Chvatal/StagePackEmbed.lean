module
/-
  # Depth of parallel pack embeddings on `64^d`

  Abstract bag wire layout: `numBags` order-embeddings into ambient wires with
  pairwise disjoint ranges. Scattering one pack of depth <= D into each bag
  yields a stage net of depth <= D (`depth_scatterEmbed_le` +
  `depth_flatMap_disjoint`).

  Contiguous tiling (`bagSize dvd N`) is the concrete layout for paper packs:
  ordinary m*n = 2^64 when d >= 11, root m*n = 2^83 when d >= 14.

  Status: depth accounting only. Does not construct scheduler Placement.regs
  for paper bag sizes, nor prove separator semantics / Sorts.
-/

public import AKS.Chvatal.SeparatorDepth
public import AKS.Chvatal.DepthSkeleton
public import AKS.Sort.Depth
public import AKS.Bitonic.Depth
public import Mathlib.Data.List.FinRange

set_option maxRecDepth 4096

@[expose] public section

namespace Chvatal

/-! ## Abstract bag wire layout -/

/-- Wire-disjoint embeddings of `numBags` local packs into ambient `N` wires. -/
structure BagWireLayout (bagSize N numBags : Nat) where
  embed : Fin numBags → (Fin bagSize ↪o Fin N)
  disjoint : ∀ {a b : Fin numBags}, a ≠ b →
    ∀ (i j : Fin bagSize), embed a i ≠ embed b j

/-- Parallel scatter of one pack across an abstract bag layout. -/
def parallelScatterBags {bagSize N numBags : Nat}
    (layout : BagWireLayout bagSize N numBags)
    (pack : ComparatorNetwork bagSize) :
    ComparatorNetwork N :=
  ⟨(List.finRange numBags).flatMap fun b =>
    (pack.scatterEmbed N (layout.embed b)).comparators⟩

private theorem parallelScatterBags_chunk_wire_disjoint {bagSize N numBags : Nat}
    (layout : BagWireLayout bagSize N numBags)
    (pack : ComparatorNetwork bagSize)
    {a b : Fin numBags} (hne : a ≠ b)
    (c1 : Comparator N)
    (hc1 : c1 ∈ (pack.scatterEmbed N (layout.embed a)).comparators)
    (c2 : Comparator N)
    (hc2 : c2 ∈ (pack.scatterEmbed N (layout.embed b)).comparators) :
    (c1.i ≠ c2.i ∧ c1.i ≠ c2.j) ∧ (c1.j ≠ c2.i ∧ c1.j ≠ c2.j) := by
  obtain ⟨d1, _, rfl⟩ := List.mem_map.mp hc1
  obtain ⟨d2, _, rfl⟩ := List.mem_map.mp hc2
  exact ⟨⟨layout.disjoint hne d1.i d2.i, layout.disjoint hne d1.i d2.j⟩,
    ⟨layout.disjoint hne d1.j d2.i, layout.disjoint hne d1.j d2.j⟩⟩

/-- Scattering packs of depth <= D across a wire-disjoint layout yields depth <= D. -/
theorem parallelScatterBags_depth_le {bagSize N numBags depth : Nat}
    (layout : BagWireLayout bagSize N numBags)
    (pack : ComparatorNetwork bagSize)
    (hd : pack.depth ≤ depth) :
    (parallelScatterBags layout pack).depth ≤ depth := by
  refine depth_flatMap_disjoint (List.finRange numBags)
    (fun b => (pack.scatterEmbed N (layout.embed b)).comparators) depth ?hchunk ?hdisj
  · intro b _
    exact (depth_scatterEmbed_le pack _ _).trans hd
  · refine List.Pairwise.imp ?_
      ((List.nodup_iff_pairwise_ne).mp (List.nodup_finRange numBags))
    intro a b hne c1 hc1 c2 hc2
    exact parallelScatterBags_chunk_wire_disjoint layout pack hne c1 hc1 c2 hc2

/-! ## Contiguous bag tiling -/

theorem bag_offset_add_le (bagSize N : Nat) (hpos : 0 < bagSize)
    (hdvd : bagSize ∣ N) (b : Fin (N / bagSize)) :
    b.val * bagSize + bagSize ≤ N := by
  have hmul : (N / bagSize) * bagSize = N := Nat.div_mul_cancel hdvd
  have hb : b.val + 1 ≤ N / bagSize := Nat.succ_le_of_lt b.isLt
  calc b.val * bagSize + bagSize
      = (b.val + 1) * bagSize := (Nat.succ_mul b.val bagSize).symm
    _ ≤ (N / bagSize) * bagSize := Nat.mul_le_mul_right _ hb
    _ = N := hmul

/-- Contiguous block embedding: wire i of bag b maps to b * bagSize + i. -/
def contiguousBagEmbed (bagSize N : Nat) (hpos : 0 < bagSize)
    (hdvd : bagSize ∣ N) (b : Fin (N / bagSize)) :
    Fin bagSize ↪o Fin N :=
  OrderEmbedding.ofStrictMono
    (fun i => ⟨b.val * bagSize + i.val, by
      have hle := bag_offset_add_le bagSize N hpos hdvd b
      have hi : i.val < bagSize := i.isLt
      omega⟩)
    (fun {a c} hac => by
      change a.val < c.val at hac
      exact Nat.add_lt_add_left hac _)

private theorem block_offset_gap {b b' m : Nat} (hlt : b < b') {i : Nat} (hi : i < m) :
    b * m + i < b' * m := by
  have hgap : b + 1 ≤ b' := Nat.succ_le_of_lt hlt
  calc b * m + i
      < b * m + m := Nat.add_lt_add_left hi _
    _ = (b + 1) * m := (Nat.succ_mul b m).symm
    _ ≤ b' * m := Nat.mul_le_mul_right _ hgap

theorem contiguousBagEmbed_disjoint (bagSize N : Nat) (hpos : 0 < bagSize)
    (hdvd : bagSize ∣ N) {a b : Fin (N / bagSize)} (hne : a ≠ b)
    (i j : Fin bagSize) :
    contiguousBagEmbed bagSize N hpos hdvd a i ≠
      contiguousBagEmbed bagSize N hpos hdvd b j := by
  intro heq
  have hval : a.val * bagSize + i.val = b.val * bagSize + j.val :=
    congrArg Fin.val heq
  have hb : a.val ≠ b.val := fun h => hne (Fin.ext h)
  rcases lt_or_gt_of_ne hb with hlt | hgt
  · have : a.val * bagSize + i.val < b.val * bagSize :=
      block_offset_gap hlt i.isLt
    omega
  · have : b.val * bagSize + j.val < a.val * bagSize :=
      block_offset_gap hgt j.isLt
    omega

/-- Contiguous tiling as a `BagWireLayout`. -/
def contiguousBagLayout (bagSize N : Nat) (hpos : 0 < bagSize)
    (hdvd : bagSize ∣ N) :
    BagWireLayout bagSize N (N / bagSize) where
  embed := contiguousBagEmbed bagSize N hpos hdvd
  disjoint := fun hne i j => contiguousBagEmbed_disjoint bagSize N hpos hdvd hne i j

/-- Parallel embedding of one pack template across all contiguous bags. -/
def parallelPackStageNet {bagSize : Nat} (N : Nat) (hpos : 0 < bagSize)
    (hdvd : bagSize ∣ N) (pack : ComparatorNetwork bagSize) :
    ComparatorNetwork N :=
  parallelScatterBags (contiguousBagLayout bagSize N hpos hdvd) pack

theorem parallelPackStageNet_depth_le {bagSize : Nat} (N : Nat) (hpos : 0 < bagSize)
    (hdvd : bagSize ∣ N) (pack : ComparatorNetwork bagSize) (D : Nat)
    (hD : pack.depth ≤ D) :
    (parallelPackStageNet N hpos hdvd pack).depth ≤ D :=
  parallelScatterBags_depth_le (contiguousBagLayout bagSize N hpos hdvd) pack hD

/-! ## Depth-only stage obligations (no Sorts) -/

/-- Ordinary stage depth budget on `64^d` (mirrors `ParallelFinalDepthObligation`). -/
structure OrdinarySeparatorDepthObligation (d : Nat) where
  net : ComparatorNetwork (64 ^ d)
  hdepth : net.depth ≤ ordinaryStagePaperDepth

/-- Root stage depth budget on `64^d` (mirrors `ParallelFinalDepthObligation`). -/
structure RootSeparatorDepthObligation (d : Nat) where
  net : ComparatorNetwork (64 ^ d)
  hdepth : net.depth ≤ rootSeparatorPaperDepth

/-- Alias used by older PackEmbed callers. -/
abbrev OrdinaryPackStageDepthObligation (d : Nat) := OrdinarySeparatorDepthObligation d

/-- Alias used by older PackEmbed callers. -/
abbrev RootPackStageDepthObligation (d : Nat) := RootSeparatorDepthObligation d

/-- From any pack of depth <= ordinary budget that tiles `64^d` contiguously. -/
def OrdinarySeparatorDepthObligation.of_parallelPack (d : Nat) {bagSize : Nat}
    (hpos : 0 < bagSize) (hdvd : bagSize ∣ 64 ^ d)
    (pack : ComparatorNetwork bagSize)
    (hD : pack.depth ≤ ordinaryStagePaperDepth) :
    OrdinarySeparatorDepthObligation d where
  net := parallelPackStageNet (64 ^ d) hpos hdvd pack
  hdepth := parallelPackStageNet_depth_le (64 ^ d) hpos hdvd pack
    ordinaryStagePaperDepth hD

/-- From any pack of depth <= root budget that tiles `64^d` contiguously. -/
def RootSeparatorDepthObligation.of_parallelPack (d : Nat) {bagSize : Nat}
    (hpos : 0 < bagSize) (hdvd : bagSize ∣ 64 ^ d)
    (pack : ComparatorNetwork bagSize)
    (hD : pack.depth ≤ rootSeparatorPaperDepth) :
    RootSeparatorDepthObligation d where
  net := parallelPackStageNet (64 ^ d) hpos hdvd pack
  hdepth := parallelPackStageNet_depth_le (64 ^ d) hpos hdvd pack
    rootSeparatorPaperDepth hD

/-- From an abstract wire-disjoint layout of packs into `64^d`. -/
def OrdinarySeparatorDepthObligation.of_layout (d : Nat) {bagSize numBags : Nat}
    (layout : BagWireLayout bagSize (64 ^ d) numBags)
    (pack : ComparatorNetwork bagSize)
    (hD : pack.depth ≤ ordinaryStagePaperDepth) :
    OrdinarySeparatorDepthObligation d where
  net := parallelScatterBags layout pack
  hdepth := parallelScatterBags_depth_le layout pack hD

def RootSeparatorDepthObligation.of_layout (d : Nat) {bagSize numBags : Nat}
    (layout : BagWireLayout bagSize (64 ^ d) numBags)
    (pack : ComparatorNetwork bagSize)
    (hD : pack.depth ≤ rootSeparatorPaperDepth) :
    RootSeparatorDepthObligation d where
  net := parallelScatterBags layout pack
  hdepth := parallelScatterBags_depth_le layout pack hD

/-! ## Paper pack sizes -/

/-- Paper-ordinary pack size m*n = 2^60 * 16 = 2^64. -/
def paperOrdinaryBagSize : Nat := paperOrdinaryGeometry.m * paperOrdinaryGeometry.n

theorem paperOrdinaryBagSize_eq : paperOrdinaryBagSize = 2 ^ 64 := by
  unfold paperOrdinaryBagSize paperOrdinaryGeometry ScrambleGeometry.ofShape
  decide

/-- Paper-root pack size m*n = 2^79 * 16 = 2^83. -/
def paperRootBagSize : Nat := paperRootGeometry.m * paperRootGeometry.n

theorem paperRootBagSize_eq : paperRootBagSize = 2 ^ 83 := by
  unfold paperRootBagSize paperRootGeometry ScrambleGeometry.ofShape
  decide

theorem pow64_eq_pow2_6d (d : Nat) : (64 : Nat) ^ d = 2 ^ (6 * d) := by
  have h64 : (64 : Nat) = 2 ^ 6 := by decide
  calc (64 : Nat) ^ d
      = (2 ^ 6) ^ d := by rw [h64]
    _ = 2 ^ (6 * d) := by rw [Nat.pow_mul]

/-- When d >= 11, 2^64 dvd 64^d = 2^(6d) since 64 <= 6d. -/
theorem paperOrdinaryBagSize_dvd_pow64 {d : Nat} (hd : 11 ≤ d) :
    paperOrdinaryBagSize ∣ 64 ^ d := by
  rw [paperOrdinaryBagSize_eq, pow64_eq_pow2_6d]
  exact (Nat.pow_dvd_pow_iff_le_right (by decide : 1 < 2)).2 (by omega : 64 ≤ 6 * d)

/-- When d >= 14, 2^83 dvd 64^d = 2^(6d) since 83 <= 6d. -/
theorem paperRootBagSize_dvd_pow64 {d : Nat} (hd : 14 ≤ d) :
    paperRootBagSize ∣ 64 ^ d := by
  rw [paperRootBagSize_eq, pow64_eq_pow2_6d]
  exact (Nat.pow_dvd_pow_iff_le_right (by decide : 1 < 2)).2 (by omega : 83 ≤ 6 * d)

/-- Canonical paper-ordinary pack tiles into an ordinary-stage depth obligation (d >= 11). -/
def OrdinarySeparatorDepthObligation.of_paperOrdinaryCanonical
    (d : Nat) (hd : 11 ≤ d)
    (σ : Scramble paperOrdinaryGeometry.m paperOrdinaryGeometry.n) :
    OrdinarySeparatorDepthObligation d :=
  OrdinarySeparatorDepthObligation.of_parallelPack d
    (by
      rw [paperOrdinaryBagSize_eq]
      exact Nat.pow_pos (by decide : 0 < 2))
    (paperOrdinaryBagSize_dvd_pow64 hd)
    (canonicalSortScrambleSortPack paperOrdinaryGeometry.m paperOrdinaryGeometry.n
      (by decide) σ).net
    (by
      simpa [paperOrdinaryBagSize, ScrambleGeometry.wires] using
        SortScrambleSortPack_paperOrdinary_depth_le_ordinaryStage σ)

/-- Canonical paper-root pack tiles into a root-stage depth obligation (d >= 14). -/
def RootSeparatorDepthObligation.of_paperRootCanonical
    (d : Nat) (hd : 14 ≤ d)
    (σ : Scramble paperRootGeometry.m paperRootGeometry.n) :
    RootSeparatorDepthObligation d :=
  RootSeparatorDepthObligation.of_parallelPack d
    (by
      rw [paperRootBagSize_eq]
      exact Nat.pow_pos (by decide : 0 < 2))
    (paperRootBagSize_dvd_pow64 hd)
    (canonicalSortScrambleSortPack paperRootGeometry.m paperRootGeometry.n
      (by decide) σ).net
    (by
      simpa [paperRootBagSize, ScrambleGeometry.wires] using
        SortScrambleSortPack_paperRoot_depth_le_rootSeparator σ)

/-- Older PackEmbed name for the ordinary paper tiling. -/
def OrdinaryPackStageDepthObligation.of_canonical (d : Nat) (hd : 11 ≤ d)
    (σ : Scramble paperOrdinaryGeometry.m paperOrdinaryGeometry.n) :
    OrdinaryPackStageDepthObligation d :=
  OrdinarySeparatorDepthObligation.of_paperOrdinaryCanonical d hd σ

/-- Older PackEmbed name for the root paper tiling. -/
def RootPackStageDepthObligation.of_canonical (d : Nat) (hd : 14 ≤ d)
    (σ : Scramble paperRootGeometry.m paperRootGeometry.n) :
    RootPackStageDepthObligation d :=
  RootSeparatorDepthObligation.of_paperRootCanonical d hd σ

/-- Residual: global Sorts for a depth-bounded ordinary stage shell. -/
def OrdinarySeparatorSortResidual (d : Nat) (O : OrdinarySeparatorDepthObligation d) : Prop :=
  ComparatorNetwork.Sorts.{0} O.net

/-- Residual: global Sorts for a depth-bounded root stage shell. -/
def RootSeparatorSortResidual (d : Nat) (O : RootSeparatorDepthObligation d) : Prop :=
  ComparatorNetwork.Sorts.{0} O.net

end Chvatal
