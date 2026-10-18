import OutsiderSlotMass
import OutsiderOutsideMass
import FrontierRankCounting
import InvariantInputTails
import Mathlib.Tactic

namespace Tapered945

open Chvatal

/-- Convert a hierarchical native-prefix rank-cut bound into the desired
lower input-tail estimate. The only remaining term outside the interval cut
is the order-one outsider tail of the bag itself. -/
theorem outsider_prefix_tail_bound
    {d t : Nat} (pl : Placement 64 d)
    (perm : Fin (64 ^ d) → Fin (64 ^ d))
    (hperm : Function.Injective perm)
    (hP : TaperedOutsiderBoundLe d t pl perm)
    (q : KBag 64 d) (cut : Nat) (I : Finset (Fin (64 ^ d)))
    (D O : Nat) (hDle : D ≤ I.card)
    (hI : I = Finset.univ.filter (fun k : Fin (64 ^ d) =>
      q.lo ≤ k.val ∧ k.val < cut))
    (hRank : (((pl.regs q).image perm ∩ I).card ≤ I.card - D + O)) :
    (((pl.regs q).image perm).filter (fun k => k.val < cut)).card ≤
      mu * candidateReferenceCapacity d q.l t + (I.card - D + O) := by
  let K := (pl.regs q).image perm
  let E := ((pl.regs q).filter (fun w => (perm w).val < q.lo)).image perm
  have hE : E = K.filter (fun k => k.val < q.lo) := by
    ext k
    simp only [E, K, Finset.mem_image, Finset.mem_filter]
    constructor
    · rintro ⟨w, ⟨hw, hlow⟩, rfl⟩
      exact ⟨⟨w, hw, rfl⟩, hlow⟩
    · rintro ⟨⟨w, hw, rfl⟩, hlow⟩
      exact ⟨w, ⟨hw, hlow⟩, rfl⟩
  have hEcard : E.card =
      ((pl.regs q).filter (fun w => (perm w).val < q.lo)).card := by
    change (((pl.regs q).filter (fun w => (perm w).val < q.lo)).image perm).card = _
    rw [Finset.card_image_of_injective _ hperm]
  have hbase := (invariant_native_external_tails pl perm hP q).1
  have hEbase : (E.card : Rat) ≤
      mu * delta ^ 0 * candidateReferenceCapacity d q.l t := by
    rw [hEcard]
    exact hbase
  have hsub : K.filter (fun k => k.val < cut) ⊆
      E ∪ (K ∩ I) := by
    intro k hk
    have hlow := (Finset.mem_filter.mp hk).2
    by_cases hbelow : k.val < q.lo
    · exact Finset.mem_union_left _ (by rw [hE]; exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hk).1, hbelow⟩)
    · have hge : q.lo ≤ k.val := by omega
      have hki : k ∈ I := by rw [hI]; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨hge, hlow⟩⟩
      exact Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨(Finset.mem_filter.mp hk).1, hki⟩)
  have hNat : (K.filter (fun k => k.val < cut)).card ≤ E.card + (K ∩ I).card :=
    (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  have hNatCast : ((K.filter (fun k => k.val < cut)).card : Rat) ≤
      (E.card : Rat) + ((K ∩ I).card : Rat) := by exact_mod_cast hNat
  have hRankCast : ((K ∩ I).card : Rat) ≤ (I.card - D + O : Nat) := by
    exact_mod_cast hRank
  have hnatCast : ((I.card - D + O : Nat) : Rat) =
      (I.card : Rat) - D + O := by
    push_cast
    rw [Nat.cast_sub hDle]
  have hRankCast' : ((K ∩ I).card : Rat) ≤ (I.card : Rat) - D + O := by
    rw [hnatCast] at hRankCast
    exact hRankCast
  have hdelta : delta ^ 0 = (1 : Rat) := by norm_num
  rw [hdelta] at hEbase
  change ((K.filter (fun k => k.val < cut)).card : Rat) ≤ _
  rw [show K = (pl.regs q).image perm by rfl]
  calc
    _ ≤ (E.card : Rat) + ((K ∩ I).card : Rat) := hNatCast
    _ ≤ mu * candidateReferenceCapacity d q.l t + ((I.card : Rat) - D + O) :=
      add_le_add (by simpa [delta] using hEbase) hRankCast'

/-- The central hierarchical input-rank estimate. Selected descendant slots
provide native mass on the inside of the cut; incomparable outside bags charge
their leaks at the stranger order given by their distance to the common level;
ancestor/frontier storage is retained as `ambient`. All remaining premises
are concrete routing, width, and schedule facts. -/
theorem outsider_rank_cut_bound
    {d t : Nat} {Index : Type*} [DecidableEq Index]
    (pl : Placement 64 d)
    (perm : Fin (64 ^ d) → Fin (64 ^ d))
    (hperm : Function.Injective perm)
    (hP : TaperedOutsiderBoundLe d t pl perm)
    (q : KBag 64 d)
    (Jdesc : Finset (Fin 64))
    (I DescRaw Outside ambient : Finset (Fin (64 ^ d)))
    (descBags : Fin 64 → KBag 64 d)
    (descSlots : Fin 64 → Finset (Fin (64 ^ d)))
    (width descErr : Fin 64 → Nat)
    (Jout : Finset Index)
    (outBags : Index → KBag 64 d)
    (outSlots : Index → Finset (Fin (64 ^ d)))
    (outErr : Index → Nat) (ambientBound : Nat)
    (hI : I ⊆ nativeKeys q)
    (hdescCover : Jdesc.biUnion (fun j => nativeKeys (descBags j)) = I)
    (hdescNativeDisjoint : ∀ i ∈ Jdesc, ∀ j ∈ Jdesc, i ≠ j →
      Disjoint (nativeKeys (descBags i)) (nativeKeys (descBags j)))
    (hdescSlotRaw : ∀ j, descSlots j ⊆ DescRaw)
    (hdescSlotBag : ∀ j, descSlots j ⊆ pl.regs (descBags j))
    (hdescWidth : ∀ j, (descSlots j).card = width j)
    (hdescErr : ∀ j,
      mu * candidateReferenceCapacity d (descBags j).l t ≤ descErr j)
    (houtCover : Outside ⊆ Jout.biUnion
      (fun i => (outSlots i).image perm ∩ I) ∪ ambient)
    (houtSlot : ∀ i ∈ Jout, outSlots i ⊆ pl.regs (outBags i))
    (houtIncomp : ∀ i ∈ Jout,
      (outBags i).ancestor (outsiderSeparationRank q (outBags i)) ≠
        q.ancestor (q.l - min q.l (outBags i).l))
    (houtErr : ∀ i ∈ Jout,
      mu * delta ^ (outsiderSeparationRank q (outBags i)) *
        candidateReferenceCapacity d (outBags i).l t ≤ outErr i)
    (hambient : (ambient ∩ I).card ≤ ambientBound)
    (hpartition : I ⊆ (pl.regs q).image perm ∪ DescRaw.image perm ∪ Outside)
    (hKDesc : Disjoint ((pl.regs q).image perm) (DescRaw.image perm))
    (hKOutside : Disjoint ((pl.regs q).image perm) Outside)
    (hDescOutside : Disjoint (DescRaw.image perm) Outside) :
    (((pl.regs q).image perm ∩ I).card) ≤
      I.card - (∑ j ∈ Jdesc, (width j - descErr j)) +
        (ambientBound + ∑ i ∈ Jout, outErr i) := by
  have hdescMass := outsider_selected_native_mass_lower pl perm hperm hP
    Jdesc I DescRaw descBags descSlots width descErr hdescCover
    hdescNativeDisjoint hdescSlotRaw hdescSlotBag hdescWidth hdescErr
  have houtMass := outsider_incomparable_outside_native_mass_upper pl perm
    hperm hP q Jout I Outside ambient outBags outSlots outErr ambientBound
    hI houtCover houtSlot houtIncomp houtErr hambient
  exact prefix_count_le_of_three_way_cover
    ((pl.regs q).image perm) (DescRaw.image perm) Outside I I.card
    (∑ j ∈ Jdesc, (width j - descErr j))
    (ambientBound + ∑ i ∈ Jout, outErr i)
    hKDesc hKOutside hDescOutside hpartition rfl hdescMass houtMass

end Tapered945
