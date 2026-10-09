module

public import AKS.Chvatal.RealNets
public import AKS.Chvatal.RealKernel
public import AKS.Chvatal.RealInduction
public import AKS.Chvatal.BadSendField
public import AKS.Chvatal.FringeSendField

@[expose] public section

/-! Purity of the real network at the meeting level: for every input permutation, after the `t_f`
stages every bag on level `d - 6` contains no order-2 outsiders (stage kernels from the two field
theorems, then the induction `real_purity`). -/

namespace Chvatal

/-- **Purity of the real network.** For `d ≥ 14` (needed for the root's `m = 2^79` pack) and
every input permutation `v`, after `t_f` stages of `realNets` the keys on any level-`(d-6)`
bag are all addressed below its ancestor of order 1 (no order-2 strangers). -/
theorem realNets_purity {d : ℕ} (hd14 : 14 ≤ d) (v : Equiv.Perm (Fin (64 ^ d)))
    (b : KBag 64 d) (hb : b.l = d - 6) :
    b.strangers 2 id
      ((execPlacement (flowSizes7 d (by omega)) (realNets d (by omega)) v (tf7 d) le_rfl).regs b)
      (by norm_num : 1 ≤ 64) = 0 :=
  real_purity (by omega) (realNets d (by omega)) (realNets_specs (by omega) hd14) v
    (fun t ht1 ht hP =>
      realStageKernel (by omega) (realNets d (by omega)) v t ht hP
        (badSendField_real (by omega) (realNets d (by omega)) (realNets_specs (by omega) hd14)
          v t ht1 ht hP)
        (fringeSendField_real (by omega) (realNets d (by omega)) (realNets_specs (by omega) hd14)
          v t ht1 ht hP)) b hb

end Chvatal
