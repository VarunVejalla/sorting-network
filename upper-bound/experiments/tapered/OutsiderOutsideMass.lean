import OutsiderSlotMass
import RaggedSlotMass
import Mathlib.Tactic

namespace Tapered945

open Chvatal

/-- Distinct bags at one level have disjoint native key intervals. -/
theorem nativeKeys_disjoint_of_level_eq_ne {d : Nat}
    (a b : KBag 64 d) (hlevel : a.l = b.l) (hne : a ≠ b) :
    Disjoint (nativeKeys a) (nativeKeys b) := by
  apply Finset.disjoint_left.mpr
  intro k hka hkb
  have hka := (Finset.mem_filter.mp hka).2
  have hkb := (Finset.mem_filter.mp hkb).2
  change nativeBagIdx 64 d a.l k.val = a.x at hka
  change nativeBagIdx 64 d b.l k.val = b.x at hkb
  have hab : a.x = b.x := by
    calc
      a.x = nativeBagIdx 64 d a.l k.val := hka.symm
      _ = nativeBagIdx 64 d b.l k.val := by rw [hlevel]
      _ = b.x := hkb
  apply hne
  apply KBag.ext
  · exact hlevel
  · exact hab

/-- A key native to a bag is also native to any ancestor bag. -/
theorem native_ancestor_of_native {d : Nat} (q : KBag 64 d) (r : Nat)
    (hr : r ≤ q.l) (k : Fin (64 ^ d)) :
    q.Native k id → (q.ancestor r).Native k id := by
  intro hq
  have hqd := q.hl
  have hexp : d - (q.l - r) = (d - q.l) + r := by omega
  have hq' : k.val / 64 ^ (d - q.l) = q.x := by
    change nativeBagIdx 64 d q.l k.val = q.x at hq
    simpa [nativeBagIdx, bagSize] using hq
  change k.val / 64 ^ (d - (q.l - r)) = (q.x / 64 ^ r)
  rw [hexp, pow_add, ← Nat.div_div_eq_div_mul]
  rw [hq']

/-- The native interval of a bag is contained in every ancestor's native
interval. -/
theorem nativeKeys_ancestor_superset {d : Nat} (q : KBag 64 d) (r : Nat)
    (hr : r ≤ q.l) : nativeKeys q ⊆ nativeKeys (q.ancestor r) := by
  intro k hk
  have hq : q.Native k id := (Finset.mem_filter.mp hk).2
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, ?_⟩
  exact native_ancestor_of_native q r hr k hq

/-- The first bag on `z`'s path up to the common level of `q` and `z`. -/
def outsiderSeparationRank {d : Nat} (q z : KBag 64 d) : Nat :=
  z.l - min q.l z.l

/-- At the common level, incomparable bags have disjoint native intervals.
The explicit non-equality is the only tree-classification premise. -/
theorem outsider_common_level_native_disjoint {d : Nat}
    (q z : KBag 64 d)
    (hne : z.ancestor (outsiderSeparationRank q z) ≠
      q.ancestor (q.l - min q.l z.l)) :
    Disjoint (nativeKeys (z.ancestor (outsiderSeparationRank q z)))
      (nativeKeys (q.ancestor (q.l - min q.l z.l))) := by
  apply nativeKeys_disjoint_of_level_eq_ne
  · change z.l - (z.l - min q.l z.l) =
      q.l - (q.l - min q.l z.l)
    omega
  · exact hne

/-- O-side estimate with a separately exposed ancestor/frontier ambient set.
For each outside bag, choose the ancestor level whose native interval is
disjoint from the target prefix; P(t) charges every leaked key to that
higher-order stranger allowance. -/
theorem outsider_ranked_outside_native_mass_upper
    {d t : Nat} {Index : Type*} [DecidableEq Index]
    (pl : Placement 64 d)
    (perm : Fin (64 ^ d) → Fin (64 ^ d))
    (hperm : Function.Injective perm)
    (hP : TaperedOutsiderBoundLe d t pl perm)
    (J : Finset Index) (I Outside ambient : Finset (Fin (64 ^ d)))
    (bags : Index → KBag 64 d)
    (slots : Index → Finset (Fin (64 ^ d)))
    (rank : Index → Nat) (err : Index → Nat) (A : Nat)
    (hcover : Outside ⊆ J.biUnion
      (fun i => (slots i).image perm ∩ I) ∪ ambient)
    (hslot : ∀ i ∈ J, slots i ⊆ pl.regs (bags i))
    (hrank : ∀ i ∈ J, rank i ≤ d)
    (hdisj : ∀ i ∈ J,
      Disjoint (nativeKeys ((bags i).ancestor (rank i))) I)
    (herr : ∀ i ∈ J,
      mu * delta ^ (rank i) *
        candidateReferenceCapacity d (bags i).l t ≤ err i)
    (hambient : (ambient ∩ I).card ≤ A) :
    (Outside ∩ I).card ≤ A + ∑ i ∈ J, err i := by
  classical
  let leak : Index → Finset (Fin (64 ^ d)) :=
    fun i => (slots i).image perm ∩ I
  have hleakBound : ∀ i ∈ J, (leak i).card ≤ err i := by
    intro i hi
    let K := (slots i).filter (fun w => perm w ∈ I)
    have hK : K ⊆ pl.regs (bags i) :=
      Finset.Subset.trans (Finset.filter_subset _ _) (hslot i hi)
    have hbad : ∀ w ∈ K,
        (bags i).Strange (rank i + 1) w perm (by norm_num) := by
      intro w hw
      have hw' := Finset.mem_filter.mp hw
      have hkeyI : perm w ∈ I := hw'.2
      have hnative := Finset.disjoint_left.mp (hdisj i hi)
      have hnotNative : ¬ ((bags i).ancestor (rank i)).Native (perm w) id := by
        intro hn
        have hmem : perm w ∈ nativeKeys ((bags i).ancestor (rank i)) := by
          simp [nativeKeys, hn]
        exact hnative hmem hkeyI
      change rank i + 1 = 0 ∨
        ¬ ((bags i).ancestor ((rank i + 1) - 1)).Native w perm
      have hr' : (rank i + 1) - 1 = rank i := by omega
      rw [hr']
      simp only [show rank i + 1 ≠ 0 by omega, false_or]
      simpa [KBag.Native] using hnotNative
    have hbadCount := stranger_slot_error_bound pl perm hperm hP
      (bags i) (rank i) (hrank i hi) K (err i) hK (herr i hi) hbad
    have himage : K.image perm = leak i := by
      ext k
      simp only [K, leak, Finset.mem_image, Finset.mem_filter, Finset.mem_inter]
      constructor
      · rintro ⟨w, ⟨hw, hkey⟩, rfl⟩
        exact ⟨⟨w, hw, rfl⟩, hkey⟩
      · rintro ⟨⟨w, hw, rfl⟩, hkey⟩
        exact ⟨w, ⟨hw, hkey⟩, rfl⟩
    rw [himage] at hbadCount
    exact hbadCount
  have hsub : Outside ∩ I ⊆ J.biUnion leak ∪ (ambient ∩ I) := by
    intro k hk
    have hcov := hcover (Finset.mem_inter.mp hk).1
    rcases Finset.mem_union.mp hcov with hs | ha
    · exact Finset.mem_union_left _ (by simpa [leak] using hs)
    · exact Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨ha, (Finset.mem_inter.mp hk).2⟩)
  have hcard := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  have hbi : (J.biUnion leak).card ≤ ∑ i ∈ J, (leak i).card := by
    simpa using (Finset.card_biUnion_le (s := J) (t := leak))
  have herrsum : (∑ i ∈ J, (leak i).card) ≤ ∑ i ∈ J, err i := by
    apply Finset.sum_le_sum
    intro i hi
    exact hleakBound i hi
  omega

/-- Specialize the ranked O-side estimate to bags incomparable with `q`.
The same-level interval argument supplies the ancestor-disjointness premise;
the caller supplies only the tree classification, ownership, and ambient
ancestor/frontier bound. -/
theorem outsider_incomparable_outside_native_mass_upper
    {d t : Nat} {Index : Type*} [DecidableEq Index]
    (pl : Placement 64 d)
    (perm : Fin (64 ^ d) → Fin (64 ^ d))
    (hperm : Function.Injective perm)
    (hP : TaperedOutsiderBoundLe d t pl perm)
    (q : KBag 64 d) (J : Finset Index)
    (I Outside ambient : Finset (Fin (64 ^ d)))
    (bags : Index → KBag 64 d)
    (slots : Index → Finset (Fin (64 ^ d)))
    (err : Index → Nat) (A : Nat)
    (hI : I ⊆ nativeKeys q)
    (hcover : Outside ⊆ J.biUnion
      (fun i => (slots i).image perm ∩ I) ∪ ambient)
    (hslot : ∀ i ∈ J, slots i ⊆ pl.regs (bags i))
    (hne : ∀ i ∈ J,
      (bags i).ancestor (outsiderSeparationRank q (bags i)) ≠
        q.ancestor (q.l - min q.l (bags i).l))
    (herr : ∀ i ∈ J,
      mu * delta ^ (outsiderSeparationRank q (bags i)) *
        candidateReferenceCapacity d (bags i).l t ≤ err i)
    (hambient : (ambient ∩ I).card ≤ A) :
    (Outside ∩ I).card ≤ A + ∑ i ∈ J, err i := by
  apply outsider_ranked_outside_native_mass_upper pl perm hperm hP J I Outside ambient
    bags slots (fun i => outsiderSeparationRank q (bags i)) err A hcover hslot
  · intro i hi
    have hl := (bags i).hl
    dsimp [outsiderSeparationRank]
    omega
  · intro i hi
    have hqLevel : q.l - min q.l (bags i).l ≤ q.l := Nat.sub_le _ _
    have hIbar : I ⊆ nativeKeys (q.ancestor (q.l - min q.l (bags i).l)) :=
      Finset.Subset.trans hI
        (nativeKeys_ancestor_superset q _ hqLevel)
    exact Finset.disjoint_of_subset_right hIbar
      (outsider_common_level_native_disjoint q (bags i) (hne i hi))
  · exact herr
  · exact hambient

/-- Same-level bags distinct from `q` are automatically separated from the
native interval of `q`. This packages the O-side estimate for a full sibling
layer; only its wire ownership and the exceptional ambient registers remain
schedule-specific. -/
theorem outsider_same_level_outside_native_mass_upper
    {d t : Nat} {Index : Type*} [DecidableEq Index]
    (pl : Placement 64 d)
    (perm : Fin (64 ^ d) → Fin (64 ^ d))
    (hperm : Function.Injective perm)
    (hP : TaperedOutsiderBoundLe d t pl perm)
    (q : KBag 64 d) (J : Finset Index)
    (I Outside ambient : Finset (Fin (64 ^ d)))
    (bags : Index → KBag 64 d)
    (slots : Index → Finset (Fin (64 ^ d)))
    (err : Index → Nat) (A : Nat)
    (hI : I ⊆ nativeKeys q)
    (hcover : Outside ⊆ J.biUnion
      (fun i => (slots i).image perm ∩ I) ∪ ambient)
    (hslot : ∀ i ∈ J, slots i ⊆ pl.regs (bags i))
    (hlevel : ∀ i ∈ J, (bags i).l = q.l)
    (hne : ∀ i ∈ J, bags i ≠ q)
    (herr : ∀ i ∈ J,
      mu * candidateReferenceCapacity d (bags i).l t ≤ err i)
    (hambient : (ambient ∩ I).card ≤ A) :
    (Outside ∩ I).card ≤ A + ∑ i ∈ J, err i := by
  apply outsider_incomparable_outside_native_mass_upper
    pl perm hperm hP q J I Outside ambient bags slots err A hI hcover hslot
  · intro i hi
    have hl := hlevel i hi
    have hrank : outsiderSeparationRank q (bags i) = 0 := by
      simp [outsiderSeparationRank, hl]
    have hqrank : q.l - min q.l (bags i).l = 0 := by
      simp [hl]
    have hleft : (bags i).ancestor (outsiderSeparationRank q (bags i)) = bags i := by
      rw [hrank, Chvatal.ancestor_zero_eq]
    have hright : q.ancestor (q.l - min q.l (bags i).l) = q := by
      rw [hqrank, Chvatal.ancestor_zero_eq]
    rw [hleft, hright]
    exact hne i hi
  · intro i hi
    rw [show outsiderSeparationRank q (bags i) = 0 by
      simp [outsiderSeparationRank, hlevel i hi]]
    simpa using herr i hi
  · exact hambient

/-- Bound native-prefix mass in a collection of outside registers by their
order-one outsider allowances plus an explicitly retained ambient term. This
is the sibling/outside part of the O-side rank-cut recurrence; ancestor and
frontier ports must still be isolated in `ambient`. -/
theorem outsider_outside_native_mass_upper
    {d t : Nat} (pl : Placement 64 d)
    (perm : Fin (64 ^ d) → Fin (64 ^ d))
    (hperm : Function.Injective perm)
    (hP : TaperedOutsiderBoundLe d t pl perm)
    (J : Finset (Fin 64)) (I Outside ambient : Finset (Fin (64 ^ d)))
    (bags : Fin 64 → KBag 64 d)
    (slots : Fin 64 → Finset (Fin (64 ^ d)))
    (err : Fin 64 → Nat) (A : Nat)
    (hcover : Outside ⊆ J.biUnion (fun j => (slots j).image perm) ∪ ambient)
    (hslot : ∀ j ∈ J, slots j ⊆ pl.regs (bags j))
    (hdisj : ∀ j ∈ J, Disjoint (nativeKeys (bags j)) I)
    (herr : ∀ j ∈ J,
      mu * candidateReferenceCapacity d (bags j).l t ≤ err j)
    (hambient : (ambient ∩ I).card ≤ A) :
    (Outside ∩ I).card ≤ A + ∑ j ∈ J, err j := by
  let slots' : Fin 64 → Finset (Fin (64 ^ d)) := fun j => (slots j).image perm
  have hbad : ∀ j ∈ J,
      ((slots' j).filter (fun k => k ∉ nativeKeys (bags j))).card ≤ err j := by
    intro j hj
    simpa [slots', nativeKeys] using outsider_slot_error_bound pl perm hperm hP (bags j)
      (slots j) (err j) (hslot j hj) (herr j hj)
  exact outside_native_mass_upper_of_slot_errors J I Outside ambient
    slots' (fun j => nativeKeys (bags j)) err A hcover hdisj hbad hambient

end Tapered945
