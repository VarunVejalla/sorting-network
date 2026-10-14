import AKS.Chvatal.WireFlow
import VariableSlots
import RaggedBootstrapFlow
import Mathlib.Tactic

namespace Tapered945

open Chvatal

/-- Physical wire ownership for an unequal-width split. The order is the
input-independent order on wire names, not the order of the keys they carry. -/
structure RaggedWireSplit {n : Nat} (s : Finset (Fin n)) where
  up : Nat
  widths : Nat → Nat
  up_even : 2 ∣ up
  conservation : s.card = up + slotPrefix widths 64

def raggedDownSet {n : Nat} (s : Finset (Fin n)) (up : Nat)
    (widths : Nat → Nat) (j : Nat) : Finset (Fin n) :=
  blockOf s (slotLo up widths j) (slotHi up widths j)

theorem slotPrefix_succ (widths : Nat → Nat) (j : Nat) :
    slotPrefix widths (j + 1) = slotPrefix widths j + widths j := by
  simp [slotPrefix, Finset.sum_range_succ]

theorem slotPrefix_mono (widths : Nat → Nat) {i j : Nat} (h : i ≤ j) :
    slotPrefix widths i ≤ slotPrefix widths j := by
  exact Finset.sum_le_sum_of_subset (Finset.range_mono h)

/-- Every rank below the total belongs to one slot, including when some
slots have width zero. No positivity hypothesis is needed. -/
theorem slotPrefix_cover (widths : Nat → Nat) (k r : Nat)
    (hr : r < slotPrefix widths k) :
    ∃ j, j < k ∧ slotPrefix widths j ≤ r ∧ r < slotPrefix widths (j + 1) := by
  induction k with
  | zero => simp [slotPrefix] at hr
  | succ k ih =>
    by_cases hk : r < slotPrefix widths k
    · obtain ⟨j, hj, hlo, hhi⟩ := ih hk
      exact ⟨j, by omega, hlo, hhi⟩
    · exact ⟨k, by omega, by omega, hr⟩

theorem raggedDownSet_subset {n : Nat} (s : Finset (Fin n))
    (up : Nat) (widths : Nat → Nat) (j : Nat) :
    raggedDownSet s up widths j ⊆ s := blockOf_subset

theorem raggedDownSet_card {n : Nat} {s : Finset (Fin n)}
    (split : RaggedWireSplit s) (j : Nat) (hj : j < 64) :
    (raggedDownSet s split.up split.widths j).card = split.widths j := by
  have hp := slotPrefix_mono split.widths (show j + 1 ≤ 64 by omega)
  rw [slotPrefix_succ] at hp
  unfold raggedDownSet slotHi slotLo
  rw [blockOf_card (by have := split.conservation; omega)]
  omega

theorem raggedUpSet_card {n : Nat} {s : Finset (Fin n)}
    (split : RaggedWireSplit s) : (upSet s split.up).card = split.up := by
  exact upSet_card split.up_even (by have := split.conservation; omega)

theorem raggedDownSet_disjoint {n : Nat} {s : Finset (Fin n)}
    (split : RaggedWireSplit s) {i j : Nat} (hij : i < j) :
    Disjoint (raggedDownSet s split.up split.widths i)
      (raggedDownSet s split.up split.widths j) := by
  have hp := slotPrefix_mono split.widths (show i + 1 ≤ j by omega)
  rw [slotPrefix_succ] at hp
  exact disjoint_blockOf (by dsimp [slotHi, slotLo]; omega)

theorem raggedUpDown_disjoint {n : Nat} {s : Finset (Fin n)}
    (split : RaggedWireSplit s) (j : Nat) (hj : j < 64) :
    Disjoint (upSet s split.up) (raggedDownSet s split.up split.widths j) := by
  have hp := slotPrefix_mono split.widths (show j + 1 ≤ 64 by omega)
  rw [slotPrefix_succ] at hp
  have heven := split.up_even
  have htotal := split.conservation
  unfold upSet raggedDownSet slotHi slotLo
  rw [Finset.disjoint_union_left]
  exact ⟨disjoint_blockOf (by omega), (disjoint_blockOf (by omega)).symm⟩

/-- The physical register is partitioned exactly into its two up fringes
and its 64 independently sized child slots. -/
theorem raggedWireSplit_cover {n : Nat} {s : Finset (Fin n)}
    (split : RaggedWireSplit s) {w : Fin n} (hw : w ∈ s) :
    w ∈ upSet s split.up ∨ ∃ j, j < 64 ∧ w ∈ raggedDownSet s split.up split.widths j := by
  have hr := rankIn_lt_card hw
  by_cases hlo : rankIn s w < split.up / 2
  · exact Or.inl (Finset.mem_union_left _ (mem_blockOf.mpr ⟨hw, Nat.zero_le _, hlo⟩))
  by_cases hhi : s.card - split.up / 2 ≤ rankIn s w
  · exact Or.inl (Finset.mem_union_right _ (mem_blockOf.mpr ⟨hw, hhi, hr⟩))
  have ht := split.conservation
  have he := split.up_even
  have hmid : rankIn s w - split.up / 2 < slotPrefix split.widths 64 := by omega
  obtain ⟨j, hj, hlow, hhigh⟩ := slotPrefix_cover split.widths 64
    (rankIn s w - split.up / 2) hmid
  rw [slotPrefix_succ] at hhigh
  right
  refine ⟨j, hj, mem_blockOf.mpr ⟨hw, ?_, ?_⟩⟩
  · dsimp [slotLo]; omega
  · dsimp [slotHi, slotLo]; omega

/-- Equality of actual physical sets, useful when rebuilding the next
placement from routed contributions. -/
theorem raggedWireSplit_union {n : Nat} {s : Finset (Fin n)}
    (split : RaggedWireSplit s) :
    upSet s split.up ∪ (Finset.range 64).biUnion
      (raggedDownSet s split.up split.widths) = s := by
  apply Finset.Subset.antisymm
  · refine Finset.union_subset upSet_subset ?_
    exact Finset.biUnion_subset.mpr (fun j _ => raggedDownSet_subset _ _ _ j)
  · intro w hw
    rcases raggedWireSplit_cover split hw with hu | ⟨j, hj, hd⟩
    · exact Finset.mem_union_left _ hu
    · exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨j, Finset.mem_range.mpr hj, hd⟩)

/-- Ownership persists after attaching the actual (injective) key placement;
wire partitions are independent of the keys used to instantiate them. -/
theorem raggedWireSplit_image_disjoint {n : Nat} {α : Type*} [DecidableEq α]
    {s : Finset (Fin n)} (split : RaggedWireSplit s)
    (keys : Fin n → α) (hkeys : Function.Injective keys) {i j : Nat} (hij : i < j) :
    Disjoint ((raggedDownSet s split.up split.widths i).image keys)
      ((raggedDownSet s split.up split.widths j).image keys) := by
  rw [Finset.disjoint_left]
  intro key hi hj
  obtain ⟨wi, hwi, hei⟩ := Finset.mem_image.mp hi
  obtain ⟨wj, hwj, hej⟩ := Finset.mem_image.mp hj
  have heq : wi = wj := hkeys (hei.trans hej.symm)
  subst wj
  exact Finset.disjoint_left.mp (raggedDownSet_disjoint split hij) hwi hwj

theorem raggedWireSplit_image_card {n : Nat} {α : Type*} [DecidableEq α]
    {s : Finset (Fin n)} (split : RaggedWireSplit s)
    (keys : Fin n → α) (hkeys : Function.Injective keys) (j : Nat) (hj : j < 64) :
    ((raggedDownSet s split.up split.widths j).image keys).card = split.widths j := by
  rw [Finset.card_image_of_injective _ hkeys]
  exact raggedDownSet_card split j hj

/-- Turn a checked integer flow into an actual physical wire partition. -/
def raggedWireSplitOfInteger {n : Nat} (s : Finset (Fin n))
    (up : Nat) (blocks : Fin 64 → Nat) (heven : Even up)
    (hup : up ≤ s.card) (htotal : (∑ j, blocks j) = s.card - up) :
    RaggedWireSplit s where
  up := up
  widths := fun j => if hj : j < 64 then blocks ⟨j, hj⟩ else 0
  up_even := by
    obtain ⟨k, hk⟩ := heven
    exact ⟨k, by omega⟩
  conservation := by
    have hs : slotPrefix (fun j => if hj : j < 64 then blocks ⟨j, hj⟩ else 0) 64 =
        ∑ j, blocks j := by
      unfold slotPrefix
      rw [← Fin.sum_univ_eq_sum_range]
      simp
    rw [hs, htotal]
    omega

/-- The address-dependent stage-one bootstrap is realized by physical wire
slices on any actual register with the checked bootstrap cardinality. -/
def bootstrapWireSplit {n : Nat} (d x : Nat) (hd : 14 ≤ d)
    (s : Finset (Fin n)) (hcard : s.card = seedRootDown d) : RaggedWireSplit s where
  up := bootstrapUpRows x * bootstrapColumns d
  widths := fun j => bootstrapSlotRows x j * bootstrapColumns d
  up_even := by
    obtain ⟨k, hk⟩ := (bootstrap_integer_split_exact d x hd).1
    exact ⟨k, by omega⟩
  conservation := by
    obtain ⟨_, hup, hsum, _⟩ := bootstrap_integer_split_exact d x hd
    have hs : slotPrefix (fun j => bootstrapSlotRows x j * bootstrapColumns d) 64 =
        ∑ j : Fin 64, bootstrapSlotRows x j.val * bootstrapColumns d := by
      exact (Fin.sum_univ_eq_sum_range
        (fun j => bootstrapSlotRows x j * bootstrapColumns d) 64).symm
    rw [hcard, hs, hsum]
    omega

/-- `none` is the up route; `some j` is child `j`. The up fringes share
one destination, so they are deliberately treated as a single port. -/
def raggedWirePort {n : Nat} {s : Finset (Fin n)} (split : RaggedWireSplit s) :
    Option (Fin 64) → Finset (Fin n)
  | none => upSet s split.up
  | some j => raggedDownSet s split.up split.widths j.val

theorem raggedWirePort_subset {n : Nat} {s : Finset (Fin n)}
    (split : RaggedWireSplit s) (port : Option (Fin 64)) :
    raggedWirePort split port ⊆ s := by
  cases port with
  | none => exact upSet_subset
  | some j => exact raggedDownSet_subset _ _ _ _

theorem raggedWirePort_disjoint {n : Nat} {s : Finset (Fin n)}
    (split : RaggedWireSplit s) (p q : Option (Fin 64)) (hne : p ≠ q) :
    Disjoint (raggedWirePort split p) (raggedWirePort split q) := by
  cases p with
  | none =>
    cases q with
    | none => exact False.elim (hne rfl)
    | some j => exact raggedUpDown_disjoint split _ j.isLt
  | some i =>
    cases q with
    | none => exact (raggedUpDown_disjoint split _ i.isLt).symm
    | some j =>
      have hv : i.val ≠ j.val := by
        intro he
        exact hne (congrArg some (Fin.ext he))
      rcases lt_or_gt_of_ne hv with hlt | hgt
      · exact raggedDownSet_disjoint split hlt
      · exact (raggedDownSet_disjoint split hgt).symm

theorem raggedWirePort_cover {n : Nat} {s : Finset (Fin n)}
    (split : RaggedWireSplit s) {w : Fin n} (hw : w ∈ s) :
    ∃ port, w ∈ raggedWirePort split port := by
  rcases raggedWireSplit_cover split hw with hu | ⟨j, hj, hd⟩
  · exact ⟨none, hu⟩
  · exact ⟨some ⟨j, hj⟩, hd⟩

theorem raggedWirePort_unique {n : Nat} {s : Finset (Fin n)}
    (split : RaggedWireSplit s) {w : Fin n} {p q : Option (Fin 64)}
    (hp : w ∈ raggedWirePort split p) (hq : w ∈ raggedWirePort split q) : p = q := by
  by_contra hne
  exact Finset.disjoint_left.mp (raggedWirePort_disjoint split p q hne) hp hq

/-- Simultaneous actual routing by a destination map. It permits arbitrary
address-dependent widths; only the destination map is supplied by the tree
scheduler. Multiple sources sent to the same destination are united. -/
def routeRaggedWires {n : Nat} {B : Type*} [Fintype B] [DecidableEq B]
    (S : B → Finset (Fin n)) (splits : ∀ b, RaggedWireSplit (S b))
    (destination : B → Option (Fin 64) → B) (target : B) : Finset (Fin n) :=
  Finset.univ.biUnion fun b => Finset.univ.biUnion fun port =>
    if destination b port = target then raggedWirePort (splits b) port else ∅

theorem mem_routeRaggedWires {n : Nat} {B : Type*} [Fintype B] [DecidableEq B]
    (S : B → Finset (Fin n)) (splits : ∀ b, RaggedWireSplit (S b))
    (destination : B → Option (Fin 64) → B) (target : B) (w : Fin n) :
    w ∈ routeRaggedWires S splits destination target ↔
      ∃ b port, destination b port = target ∧ w ∈ raggedWirePort (splits b) port := by
  simp only [routeRaggedWires, Finset.mem_biUnion, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨b, port, hw⟩
    by_cases hd : destination b port = target
    · exact ⟨b, port, hd, by simpa only [if_pos hd] using hw⟩
    · simp [hd] at hw
  · rintro ⟨b, port, hd, hw⟩
    exact ⟨b, port, by simpa only [if_pos hd] using hw⟩

theorem routeRaggedWires_disjoint {n : Nat} {B : Type*} [Fintype B] [DecidableEq B]
    (S : B → Finset (Fin n)) (splits : ∀ b, RaggedWireSplit (S b))
    (destination : B → Option (Fin 64) → B)
    (hsource : ∀ b c, b ≠ c → Disjoint (S b) (S c))
    (b c : B) (hne : b ≠ c) :
    Disjoint (routeRaggedWires S splits destination b)
      (routeRaggedWires S splits destination c) := by
  rw [Finset.disjoint_left]
  intro w hb hc
  obtain ⟨sb, pb, hdb, hwb⟩ := (mem_routeRaggedWires S splits destination b w).mp hb
  obtain ⟨sc, pc, hdc, hwc⟩ := (mem_routeRaggedWires S splits destination c w).mp hc
  have hs : sb = sc := by
    by_contra hsne
    exact Finset.disjoint_left.mp (hsource sb sc hsne)
      (raggedWirePort_subset (splits sb) pb hwb)
      (raggedWirePort_subset (splits sc) pc hwc)
  subst sc
  have hp := raggedWirePort_unique (splits sb) hwb hwc
  subst pc
  exact hne (hdb.symm.trans hdc)

theorem routeRaggedWires_complete {n : Nat} {B : Type*} [Fintype B] [DecidableEq B]
    (S : B → Finset (Fin n)) (splits : ∀ b, RaggedWireSplit (S b))
    (destination : B → Option (Fin 64) → B)
    (hsource : ∀ w, ∃ b, w ∈ S b) (w : Fin n) :
    ∃ b, w ∈ routeRaggedWires S splits destination b := by
  obtain ⟨sb, hw⟩ := hsource w
  obtain ⟨port, hp⟩ := raggedWirePort_cover (splits sb) hw
  exact ⟨destination sb port,
    (mem_routeRaggedWires S splits destination _ w).mpr ⟨sb, port, rfl, hp⟩⟩

end Tapered945
