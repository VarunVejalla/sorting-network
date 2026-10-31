import D2PhysicalPackRankDisplacement
import D2BlockSortDisplacement
import D2SenderRankBridge
import AKS.Chvatal.NodeKeys

namespace Chvatal.D2PhysicalSenderRankDisplacement

open Chvatal.D2PhysicalPackRankDisplacement
open Chvatal

private abbrev Width := 4096 * 64

private def pack : ComparatorNetwork Width :=
  physicalPack2Net 4096 64 (by omega)
    (D2LiftedShuffleBridge.strideScramble 35)
    (D2LiftedShuffleBridge.strideScramble 25)

/-! The theorem below converts the full-permutation estimate into the form
needed for a real sender: the input may be any injective list of global keys.
Comparator execution commutes with replacing those keys by their ranks in the
sender, so the local rank at every output slot inherits the same error. -/

theorem arbitrary_sender_local_rank_displacement
    {M : Nat} (x : Fin Width → Fin M)
    (hx : Function.Injective x) (w : Fin Width) :
    (rk (keySet x) (pack.exec x w) : Nat) ≤ w.val + 3455 ∧
      w.val ≤ rk (keySet x) (pack.exec x w) + 3455 := by
  let rperm : Equiv.Perm (Fin Width) := rankPerm hx
  have hbij : Function.Bijective (rperm : Fin Width → Fin Width) := rperm.bijective
  have hdisp :=
    physicalPack2Net_two_stride_rank_displacement
      (rperm : Fin Width → Fin Width) hbij w
  have hrank := exec_rankPerm hx pack w
  change (pack.exec (rperm : Fin Width → Fin Width) w).val =
    rk (keySet x) (pack.exec x w) at hrank
  change (pack.exec (rperm : Fin Width → Fin Width) w).val ≤ w.val + 3455 ∧
    w.val ≤ (pack.exec (rperm : Fin Width → Fin Width) w).val + 3455 at hdisp
  rw [← hrank]
  exact hdisp

/-! This adapter makes the dependence on the sender's physical address gaps
explicit. It is the exact local-to-global rank-transfer statement needed by a
stage proof: if consecutive sender slots skip at most `G` global wires, this
fixed sorter adds at most `3455 * G` to a global pointwise rank envelope. -/

theorem physical_sender_adds_gap_scaled_rank_error
    {N E G : Nat} (addr : Fin Width → Fin N) (f : Fin N → Fin N)
    (haddr : StrictMono addr)
    (hgap : ∀ i j, i.val ≤ j.val →
      (addr j).val ≤ (addr i).val + G * (j.val - i.val))
    (hfInjective : Function.Injective f)
    (hfdisp : ∀ p, (f p).val ≤ p.val + E ∧ p.val ≤ (f p).val + E) :
    ∀ i, (pack.exec (f ∘ addr) i).val ≤ (addr i).val + E + G * 3455 ∧
      (addr i).val ≤ (pack.exec (f ∘ addr) i).val + E + G * 3455 := by
  exact D2SenderRankBridge.network_sender_displacement_of_rank_bound
    pack addr f haddr hgap hfInjective hfdisp
    (fun v hbij w => physicalPack2Net_two_stride_rank_displacement v hbij w)

end Chvatal.D2PhysicalSenderRankDisplacement
