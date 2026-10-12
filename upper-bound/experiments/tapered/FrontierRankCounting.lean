import Mathlib.Data.Finset.Card
import Mathlib.Tactic

namespace Tapered945

/-! A scheduler-independent counting bridge for frontier rank arguments.
The intended `K` is the top bag, `S` is descendant storage below a child
prefix, and `Native` is the corresponding union of native key intervals. -/

/-- If the current bag and descendant storage are disjoint, descendant storage
has all but `D` of the native population, up to `O` outsiders, then the current
bag contains at most `D + O` native keys. -/
theorem native_count_le_of_disjoint_storage
    {α : Type*} [DecidableEq α]
    (K S Native : Finset α) (D O : Nat)
    (hdisj : Disjoint K S)
    (hMass : Native.card = D + S.card)
    (hBad : (S.filter fun x => x ∉ Native).card ≤ O) :
    (K.filter fun x => x ∈ Native).card ≤ D + O := by
  let X := K.filter fun x => x ∈ Native
  let Y := S.filter fun x => x ∈ Native
  have hXYdisj : Disjoint X Y :=
    Finset.disjoint_of_subset_left (Finset.filter_subset _ _)
      (Finset.disjoint_of_subset_right (Finset.filter_subset _ _) hdisj)
  have hXYsub : X ∪ Y ⊆ Native := by
    intro x hx
    rcases Finset.mem_union.mp hx with hx | hy
    · exact (Finset.mem_filter.mp hx).2
    · exact (Finset.mem_filter.mp hy).2
  have hXYcard : X.card + Y.card ≤ Native.card := by
    rw [← Finset.card_union_of_disjoint hXYdisj]
    exact Finset.card_le_card hXYsub
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := S) (fun x => x ∈ Native)
  change X.card ≤ D + O
  have hsplit' : Y.card + (S.filter fun x => x ∉ Native).card = S.card := by
    simpa [Y] using hsplit
  omega

/-- A native rank prefix is split among the current bag, the selected
descendant subtrees, and storage outside the parent subtree. If the selected
descendants contain at least `D` prefix keys and outside storage contains at
most `O`, the current bag contributes at most `P-D+O`. -/
theorem prefix_count_le_of_three_way_cover
    {α : Type*} [DecidableEq α]
    (K S X I : Finset α) (P D O : Nat)
    (hKS : Disjoint K S) (hKX : Disjoint K X) (hSX : Disjoint S X)
    (hcover : I ⊆ K ∪ S ∪ X) (hI : I.card = P)
    (hD : D ≤ (S ∩ I).card) (hO : (X ∩ I).card ≤ O) :
    (K ∩ I).card ≤ P - D + O := by
  let KI := K ∩ I
  let SI := S ∩ I
  let XI := X ∩ I
  have hdisjKI_SI : Disjoint KI SI := by
    apply Finset.disjoint_left.mpr
    intro x hx hy
    exact (Finset.disjoint_left.mp hKS) (Finset.mem_inter.mp hx).1
      (Finset.mem_inter.mp hy).1
  have hdisjKI_XI : Disjoint KI XI := by
    apply Finset.disjoint_left.mpr
    intro x hx hy
    exact (Finset.disjoint_left.mp hKX) (Finset.mem_inter.mp hx).1
      (Finset.mem_inter.mp hy).1
  have hdisjSI_XI : Disjoint SI XI := by
    apply Finset.disjoint_left.mpr
    intro x hx hy
    exact (Finset.disjoint_left.mp hSX) (Finset.mem_inter.mp hx).1
      (Finset.mem_inter.mp hy).1
  have hunion : KI ∪ (SI ∪ XI) = I := by
    ext x
    constructor
    · intro hx
      rcases Finset.mem_union.mp hx with hx | hx
      · exact (Finset.mem_inter.mp hx).2
      · rcases Finset.mem_union.mp hx with hx | hx
        · exact (Finset.mem_inter.mp hx).2
        · exact (Finset.mem_inter.mp hx).2
    · intro hx
      have hx' := hcover hx
      rcases Finset.mem_union.mp hx' with hks | hxX
      · rcases Finset.mem_union.mp hks with hk | hs
        · exact Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨hk, hx⟩)
        · exact Finset.mem_union_right _ (Finset.mem_union_left _
            (Finset.mem_inter.mpr ⟨hs, hx⟩))
      · exact Finset.mem_union_right _ (Finset.mem_union_right _
          (Finset.mem_inter.mpr ⟨hxX, hx⟩))
  have hdisjKI_rest : Disjoint KI (SI ∪ XI) :=
    Finset.disjoint_union_right.mpr ⟨hdisjKI_SI, hdisjKI_XI⟩
  have hcard1 : KI.card + (SI ∪ XI).card = P := by
    rw [← Finset.card_union_of_disjoint hdisjKI_rest, hunion, hI]
  have hcard2 : (SI ∪ XI).card = SI.card + XI.card :=
    Finset.card_union_of_disjoint hdisjSI_XI
  have hcard : KI.card + SI.card + XI.card = P := by omega
  dsimp [KI, SI, XI] at hcard ⊢
  omega

end Tapered945
