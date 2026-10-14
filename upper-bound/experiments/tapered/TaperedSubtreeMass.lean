import TaperedOrdinaryKernel
import FrontierRankCounting
import NativeChildrenPartition
import RaggedRankRecurrence
import AKS.Chvatal.Lemma41Real
import Mathlib.Tactic

namespace Tapered945

open Chvatal

/-- Wires whose current key labels belong to a bag's native interval. -/
def nativeWireKeys {d : Nat} (w : KBag 64 d)
    (perm : Fin (64 ^ d) → Fin (64 ^ d)) : Finset (Fin (64 ^ d)) :=
  Finset.univ.filter (fun κ => w.Native κ perm)

/-! Transfer the established subtree outsider argument to the candidate's
tapered all-order invariant. This gives an explicit error budget for the
native mass missing from a selected descendant subtree. -/

/-- Keys in a complete descendant subtree that are nonnative to its root are
charged once at their exact ancestor distance. The per-level term is the
smaller of the tapered stranger allowance and the total register size. -/
theorem tapered_subtree_bad_le {d t : Nat}
    (pl : Placement 64 d) (perm : Fin (64 ^ d) → Fin (64 ^ d))
    (hP : TaperedOutsiderBoundLe d t pl perm)
    (a : Nat → Nat)
    (hcard : ∀ b : KBag 64 d, (pl.regs b).card = a b.l)
    (w : KBag 64 d) :
    (((subtreeKeys 64 d pl (by norm_num) w).filter
      (fun κ => ¬ w.Native κ perm)).card : Rat) ≤
      ∑ h ∈ Finset.range (d - w.l + 1),
        (64 : Rat) ^ h *
          min (mu * delta ^ h * candidateReferenceCapacity d (w.l + h) t)
            (a (w.l + h) : Rat) := by
  have hbr : 1 ≤ 64 := by norm_num
  unfold subtreeKeys subtreeBags
  rw [Finset.filter_biUnion,
    Finset.card_biUnion (fun z _ z' _ hne =>
      Finset.disjoint_filter_filter (pl.disjoint z z' hne)),
    Finset.sum_biUnion (fun h _ h' _ hne => descendants_disjoint hbr w hne)]
  push_cast
  refine Finset.sum_le_sum fun h hh => ?_
  rw [Finset.mem_range] at hh
  have hc := descendants_card hbr w h (by have := w.hl; omega)
  rw [show (64 : Rat) ^ h = ((descendants 64 d hbr w h).card : Rat) by
      rw [hc]; push_cast; rfl,
    ← nsmul_eq_mul, ← Finset.sum_const]
  refine Finset.sum_le_sum fun z hz => le_min ?_ ?_
  · have hzl := ((mem_descendants hbr w h z).mp hz).1
    have hxaddr := ((mem_descendants hbr w h z).mp hz).2
    have hanc : z.ancestor h hbr = w := by
      apply KBag.ext
      · change z.l - h = w.l
        omega
      · change z.x / 64 ^ h = w.x
        exact hxaddr
    have hbad :
        ((pl.regs z).filter (fun κ => ¬ w.Native κ perm)).card ≤
          z.strangers (h + 1) perm (pl.regs z) := by
      unfold KBag.strangers
      refine Finset.card_le_card fun κ hκ => ?_
      rw [Finset.mem_filter] at hκ ⊢
      refine ⟨hκ.1, Or.inr ?_⟩
      have hanc' : z.ancestor (h + 1 - 1) hbr = w := by
        rw [Nat.add_sub_cancel]
        exact hanc
      rw [hanc']
      exact hκ.2
    have hbound := hP z h (by omega)
    rw [hzl] at hbound
    have hbadRat : ((
        (pl.regs z).filter (fun κ => ¬ w.Native κ perm)).card : Rat) ≤
        (z.strangers (h + 1) perm (pl.regs z) : Rat) := by
      exact_mod_cast hbad
    exact hbadRat.trans hbound
  · rw [← ((mem_descendants hbr w h z).mp hz).1, ← hcard z]
    exact_mod_cast Finset.card_filter_le _ _

/-- Strict descendants only: their spill outside `w`'s native interval is
charged starting at stranger order two. This removes the root's order-one
allowance, which belongs to the current bag term in the rank-cut recurrence.
-/
theorem tapered_strict_subtree_bad_le {d t : Nat}
    (pl : Placement 64 d) (perm : Fin (64 ^ d) → Fin (64 ^ d))
    (hP : TaperedOutsiderBoundLe d t pl perm)
    (w : KBag 64 d) :
    (((strictSubtreeBags d w).biUnion pl.regs).filter
      (fun κ => ¬ w.Native κ perm)).card ≤
      ∑ z ∈ strictSubtreeBags d w,
        mu * delta ^ (z.l - w.l) *
          candidateReferenceCapacity d z.l t := by
  classical
  have hbr : 1 ≤ 64 := by norm_num
  rw [Finset.filter_biUnion,
    Finset.card_biUnion (fun z hz z' hz' hne =>
      Finset.disjoint_filter_filter (pl.disjoint z z' hne))]
  push_cast
  refine Finset.sum_le_sum fun z hz => ?_
  have hzSub : z ∈ subtreeBags 64 d hbr w := (Finset.mem_filter.mp hz).1
  have hzStrict : z.l ≠ w.l := (Finset.mem_filter.mp hz).2
  have hlevel := subtreeBags_l_ge hbr w z hzSub
  let r := z.l - w.l
  have hrpos : 1 ≤ r := by dsimp [r]; omega
  have hdist : ∃ h ∈ Finset.range (d - w.l + 1), z ∈ descendants 64 d hbr w h := by
    exact Finset.mem_biUnion.mp hzSub
  obtain ⟨h, hh, hzDesc⟩ := hdist
  have hdesc := (mem_descendants hbr w h z).mp hzDesc
  have hrh : r = h := by dsimp [r]; omega
  have hancestor : z.ancestor r hbr = w := by
    rw [hrh]
    apply KBag.ext
    · simp [KBag.ancestor]
      omega
    · simp [KBag.ancestor]
      exact hdesc.2
  have hbad :
      ((pl.regs z).filter (fun κ => ¬ w.Native κ perm)).card ≤
        z.strangers (r + 1) perm (pl.regs z) := by
    unfold KBag.strangers
    refine Finset.card_le_card fun κ hκ => ?_
    rw [Finset.mem_filter] at hκ ⊢
    refine ⟨hκ.1, Or.inr ?_⟩
    have hsub : (r + 1) - 1 = r := by omega
    rw [hsub, hancestor]
    exact hκ.2
  have hbound := hP z r (by
    dsimp [r]
    have := z.hl
    omega)
  have hbadRat : ((
      (pl.regs z).filter (fun κ => ¬ w.Native κ perm)).card : Rat) ≤
      (z.strangers (r + 1) perm (pl.regs z) : Rat) := by
    exact_mod_cast hbad
  exact hbadRat.trans hbound

/-- The strict descendant registers are exactly the full subtree registers
with the root register removed. -/
theorem strict_subtree_keys_eq_sdiff {d : Nat}
    (pl : Placement 64 d) (w : KBag 64 d) :
    (strictSubtreeBags d w).biUnion pl.regs =
      subtreeKeys 64 d pl (by norm_num) w \ pl.regs w := by
  classical
  ext κ
  constructor
  · intro hk
    obtain ⟨z, hz, hκ⟩ := Finset.mem_biUnion.mp hk
    have hz' := Finset.mem_filter.mp hz
    have hsub : z ∈ subtreeBags 64 d (by norm_num) w := hz'.1
    have hκsub : κ ∈ subtreeKeys 64 d pl (by norm_num) w := by
      exact Finset.mem_biUnion.mpr ⟨z, hsub, hκ⟩
    have hzw : z ≠ w := by
      intro heq
      subst z
      exact hz'.2 rfl
    have hnot : κ ∉ pl.regs w := by
      intro hκw
      exact (Finset.disjoint_left.mp (pl.disjoint z w hzw)) hκ hκw
    exact Finset.mem_sdiff.mpr ⟨hκsub, hnot⟩
  · intro hk
    have hk' := Finset.mem_sdiff.mp hk
    obtain ⟨z, hz, hκ⟩ := Finset.mem_biUnion.mp hk'.1
    have hz' : z ∈ strictSubtreeBags d w := by
      apply Finset.mem_filter.mpr
      refine ⟨hz, ?_⟩
      intro hlevel
      have hdescBag : z ∈ subtreeBags 64 d (by norm_num) w := hz
      obtain ⟨h, hh, hzd⟩ := Finset.mem_biUnion.mp hdescBag
      have hd := (mem_descendants (by norm_num : 1 ≤ 64) w h z).mp hzd
      have hh0 : h = 0 := by omega
      subst h
      have hzw : z = w := by
        apply KBag.ext
        · omega
        · simpa using hd.2
      subst z
      exact hk'.2 hκ
    exact Finset.mem_biUnion.mpr ⟨z, hz', hκ⟩

/-- If register sizes depend only on level, the exact strict-subtree mass is
the standard complete-subtree sum with the root occupancy removed. This is
the arithmetic interface used to instantiate the localized mass defect. -/
theorem card_strict_subtree_keys {d : Nat}
    (pl : Placement 64 d) (w : KBag 64 d) (a : Nat → Nat)
    (hcard : ∀ b : KBag 64 d, (pl.regs b).card = a b.l) :
    ((strictSubtreeBags d w).biUnion pl.regs).card =
      (∑ h ∈ Finset.range (d - w.l + 1), 64 ^ h * a (w.l + h)) - a w.l := by
  rw [strict_subtree_keys_eq_sdiff]
  have hroot : pl.regs w ⊆ subtreeKeys 64 d pl (by norm_num) w := by
    intro κ hκ
    apply Finset.mem_biUnion.mpr
    refine ⟨w, ?_, hκ⟩
    unfold subtreeBags
    apply Finset.mem_biUnion.mpr
    refine ⟨0, by simp, ?_⟩
    simp [descendants, KBag.ancestor]
  rw [Finset.card_sdiff_of_subset hroot,
    Chvatal.card_subtreeKeys (by norm_num) pl w a hcard, hcard w]

/-- Address-dependent form of the exact strict-subtree mass formula. Unlike
`card_strict_subtree_keys`, this needs no level-uniform occupancy assumption;
the terms can be replaced directly by routed local-flow counts. -/
theorem card_strict_subtree_keys_address_dependent {d : Nat}
    (pl : Placement 64 d) (w : KBag 64 d) :
    ((strictSubtreeBags d w).biUnion pl.regs).card =
      ∑ z ∈ strictSubtreeBags d w, (pl.regs z).card := by
  classical
  rw [Finset.card_biUnion (fun z hz z' hz' hne => pl.disjoint z z' hne)]

/-- Convert a bad-key error bound into a lower bound on native keys actually
present in a finite set. -/
theorem native_mass_lower_of_bad_budget {d : Nat}
    (S : Finset (Fin (64 ^ d))) (w : KBag 64 d)
    (perm : Fin (64 ^ d) → Fin (64 ^ d)) (M O : Nat)
    (hcard : S.card = M)
    (hbad : ((S.filter (fun κ => ¬ w.Native κ perm)).card : Rat) ≤ O) :
    M - O ≤ (S ∩ nativeWireKeys w perm).card := by
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := S) (fun κ => w.Native κ perm)
  have hnative :
      (S.filter (fun κ => w.Native κ perm)).card =
        (S ∩ nativeWireKeys w perm).card := by
    have hset : S.filter (fun κ => w.Native κ perm) =
        S ∩ nativeWireKeys w perm := by
      ext κ
      simp [nativeWireKeys]
    exact congrArg Finset.card hset
  rw [hnative, hcard] at hsplit
  have hbadNat : (S.filter (fun κ => ¬ w.Native κ perm)).card ≤ O := by
    exact_mod_cast hbad
  omega

/-- Descendant native-mass lower bound from the tapered outsider invariant.
Only the exact scheduled subtree cardinality and the numerical evaluation of
the strict-descendant error series remain for a concrete stage. -/
theorem tapered_strict_subtree_native_mass_lower {d t : Nat}
    (pl : Placement 64 d) (perm : Fin (64 ^ d) → Fin (64 ^ d))
    (hP : TaperedOutsiderBoundLe d t pl perm) (w : KBag 64 d)
    (M O : Nat)
    (hMass : ((strictSubtreeBags d w).biUnion pl.regs).card = M)
    (hBudget : (∑ z ∈ strictSubtreeBags d w,
      mu * delta ^ (z.l - w.l) *
        candidateReferenceCapacity d z.l t) ≤ O) :
    M - O ≤ (((strictSubtreeBags d w).biUnion pl.regs) ∩
      nativeWireKeys w perm).card := by
  apply native_mass_lower_of_bad_budget
    ((strictSubtreeBags d w).biUnion pl.regs) w perm M O hMass
  exact (tapered_strict_subtree_bad_le pl perm hP w).trans hBudget

/-- Any storage disjoint from the strict descendant subtree has at most the
subtree's native-mass defect plus its higher-order outsider spill inside the
selected native interval. This applies to the union of all ancestor/frontier
registers at once. -/
theorem ambient_set_native_bound_of_strict_subtree_mass {d t : Nat}
    (pl : Placement 64 d) (perm : Fin (64 ^ d) → Fin (64 ^ d))
    (hP : TaperedOutsiderBoundLe d t pl perm) (w : KBag 64 d)
    (Ambient : Finset (Fin (64 ^ d))) (D O : Nat)
    (hdisj : Disjoint Ambient ((strictSubtreeBags d w).biUnion pl.regs))
    (hMass : (nativeWireKeys w perm).card = D +
      ((strictSubtreeBags d w).biUnion pl.regs).card)
    (hBudget : (∑ z ∈ strictSubtreeBags d w,
      mu * delta ^ (z.l - w.l) * candidateReferenceCapacity d z.l t) ≤ O) :
    ((Ambient ∩ nativeWireKeys w perm).card ≤ D + O) := by
  have hbadRat := (tapered_strict_subtree_bad_le pl perm hP w).trans hBudget
  have hbadEq : ((strictSubtreeBags d w).biUnion pl.regs).filter
      (fun κ => κ ∉ nativeWireKeys w perm) =
    ((strictSubtreeBags d w).biUnion pl.regs).filter
      (fun κ => ¬ w.Native κ perm) := by
    ext κ
    simp [nativeWireKeys]
  have hbad : ((((strictSubtreeBags d w).biUnion pl.regs).filter
      (fun κ => κ ∉ nativeWireKeys w perm)).card) ≤ O := by
    rw [hbadEq]
    exact_mod_cast hbadRat
  have hcount := native_count_le_of_disjoint_storage Ambient
    ((strictSubtreeBags d w).biUnion pl.regs) (nativeWireKeys w perm) D O
    hdisj hMass hbad
  have hfilter : (Ambient.filter (fun κ => κ ∈ nativeWireKeys w perm)) =
      Ambient ∩ nativeWireKeys w perm := by
    ext κ
    simp
  simpa [hfilter] using hcount

/-- Convert an exact descendant-subtree mass and the preceding outsider sum
into a localized bound for any disjoint ambient register. This is the concrete
ancestor/frontier localization estimate; the scheduler must provide `hMass`
and make its defect plus tapered spill fit the signed reserve. -/
theorem ambient_register_native_bound_of_subtree_mass {d t : Nat}
    (pl : Placement 64 d) (perm : Fin (64 ^ d) → Fin (64 ^ d))
    (hP : TaperedOutsiderBoundLe d t pl perm)
    (a : Nat → Nat)
    (hcard : ∀ b : KBag 64 d, (pl.regs b).card = a b.l)
    (w ambientBag : KBag 64 d) (D O : Nat)
    (hdisj : Disjoint (pl.regs ambientBag)
      (subtreeKeys 64 d pl (by norm_num) w))
    (hMass : (nativeWireKeys w perm).card = D +
      (subtreeKeys 64 d pl (by norm_num) w).card)
    (hBudget : (∑ h ∈ Finset.range (d - w.l + 1),
      (64 : Rat) ^ h *
        min (mu * delta ^ h * candidateReferenceCapacity d (w.l + h) t)
          (a (w.l + h) : Rat)) ≤ O) :
    ((pl.regs ambientBag ∩ nativeWireKeys w perm).card) ≤ D + O := by
  have hO := (tapered_subtree_bad_le pl perm hP a hcard w).trans hBudget
  have hbadEq :
      (subtreeKeys 64 d pl (by norm_num) w).filter
        (fun κ => κ ∉ nativeWireKeys w perm) =
      (subtreeKeys 64 d pl (by norm_num) w).filter
        (fun κ => ¬ w.Native κ perm) := by
    ext κ
    simp [nativeWireKeys]
  have hbad :
      ((subtreeKeys 64 d pl (by norm_num) w).filter
        (fun κ => κ ∉ nativeWireKeys w perm)).card ≤ O := by
    rw [hbadEq]
    exact_mod_cast hO
  exact native_count_le_of_disjoint_storage
    (pl.regs ambientBag) (subtreeKeys 64 d pl (by norm_num) w)
    (nativeWireKeys w perm) D O hdisj hMass hbad

end Tapered945
