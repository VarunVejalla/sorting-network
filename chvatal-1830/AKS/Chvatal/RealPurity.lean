module

/-
  # Purity of the real Chvátal network at the meeting level

  Combines the node networks (`RealNets`), the stage kernel (`RealKernel`) with its two
  fields (`BadSendField`, `FringeSendField`), and the induction (`RealInduction`):
  for every input permutation `v`, after the `t_f` stages of the real network, every bag on
  level `d - 6` contains no order-2 outsiders.
-/

public import AKS.Chvatal.RealNets
public import AKS.Chvatal.RealKernel
public import AKS.Chvatal.RealInduction
public import AKS.Chvatal.BadSendField
public import AKS.Chvatal.FringeSendField

@[expose] public section

namespace Chvatal

/-- The stage kernels of the real network, from the two field theorems. -/
noncomputable def realKernelFamily {d : ℕ} (hd : 7 ≤ d)
    (nets : ℕ → (b : KBag 64 d) → (n : ℕ) → ComparatorNetwork n)
    (hspecs : RealSpecs hd nets) (v : Equiv.Perm (Fin (64 ^ d))) :
    ∀ t, 1 ≤ t → ∀ (ht : t + 1 ≤ tf7 d),
      OutsiderBoundLe params7 invariantReal d (levelSchedule7 d hd) t
        (execPlacement (flowSizes7 d hd) nets v t (by omega)) id →
      StageKernel params7 invariantReal d (levelSchedule7 d hd) t
        (execPlacement (flowSizes7 d hd) nets v t (by omega)) id
        (execPlacement (flowSizes7 d hd) nets v (t + 1) ht) id :=
  fun t ht1 ht hP =>
    realStageKernel hd nets v t ht hP
      (badSendField_real hd nets hspecs v t ht1 ht hP)
      (fringeSendField_real hd nets hspecs v t ht1 ht hP)

/-- **Purity of the real network.** For `d ≥ 14` (needed for the root's `m = 2^79` pack) and
    every input permutation `v`, after `t_f` stages of `realNets` the keys on any level-`(d-6)`
    bag are all addressed below its ancestor of order 1 (no order-2 strangers). -/
theorem realNets_purity {d : ℕ} (hd14 : 14 ≤ d) (v : Equiv.Perm (Fin (64 ^ d)))
    (b : KBag 64 d) (hb : b.l = d - 6) :
    b.strangers 2 id
      ((execPlacement (flowSizes7 d (by omega)) (realNets d (by omega)) v (tf7 d) le_rfl).regs b)
      (by norm_num : 1 ≤ 64) = 0 :=
  real_purity (by omega) (realNets d (by omega)) (realNets_specs (by omega) hd14) v
    (realKernelFamily (by omega) (realNets d (by omega)) (realNets_specs (by omega) hd14) v) b hb

end Chvatal
