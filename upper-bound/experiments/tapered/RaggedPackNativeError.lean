import BootstrapSeparatorOutput
import AKS.Chvatal.NodeKeys
import NativeChildrenPartition
import Mathlib.Tactic

namespace Tapered945

open Chvatal

/-- The B2 separator-output estimate also holds for actual finite key labels,
not just their natural-number values. The proof transfers the filtered output
cardinality through `Fin.val`, using injectivity of network execution. -/
theorem physical_ragged_output_fin_wrong_le
    {m n M : Nat} (hn : 0 < n)
    (σ₁ σ₂ : Scramble m n) (epsB : Real)
    (hB : HasPackSemanticPropertyB2 hn σ₁ σ₂ epsB)
    (hBflip : HasPackSemanticPropertyB2 hn (flipScramble σ₁) (flipScramble σ₂) epsB)
    (profile : RaggedFlowContract m) (j : Nat) (hj1 : 1 ≤ j) (hj63 : j ≤ 63)
    (xr : Fin (m * n) → Fin M) (hxr : Function.Injective xr)
    (lo hi : Nat) (A : Real)
    (hA : ((((keySet xr).image Fin.val).filter (fun κ =>
      (profile.start + raggedPrefixRows profile.width j) * n ≤
          BW.rankN ((keySet xr).image Fin.val) κ ∧
      BW.rankN ((keySet xr).image Fin.val) κ <
          (profile.start + raggedPrefixRows profile.width (j + 1)) * n ∧
      ¬ (lo ≤ κ ∧ κ < hi))).card : Real) ≤ A) :
    ((((Finset.univ.filter (fun c : Fin (m * n) =>
      (profile.start + raggedPrefixRows profile.width j) * n ≤ c.val ∧
      c.val < (profile.start + raggedPrefixRows profile.width (j + 1)) * n)).image
        (fun c => (physicalPack2Net m n hn σ₁ σ₂).exec xr c)).filter
        (fun κ => ¬ (lo ≤ κ.val ∧ κ.val < hi))).card : Real) ≤
      A + epsB * (m * n) := by
  let net := physicalPack2Net m n hn σ₁ σ₂
  let cells := Finset.univ.filter (fun c : Fin (m * n) =>
    (profile.start + raggedPrefixRows profile.width j) * n ≤ c.val ∧
    c.val < (profile.start + raggedPrefixRows profile.width (j + 1)) * n)
  have hnetInj : Function.Injective (net.exec xr) := exec_keySet_injective hxr net
  have hfin : ((cells.image (net.exec xr)).filter
      (fun κ : Fin M => ¬ (lo ≤ κ.val ∧ κ.val < hi))).card =
      (cells.filter (fun c => ¬ (lo ≤ (net.exec xr c).val ∧
        (net.exec xr c).val < hi))).card := by
    rw [Finset.filter_image, Finset.card_image_of_injective _ hnetInj]
  have hnat : ((cells.image (fun c => (net.exec xr c).val)).filter
      (fun κ => ¬ (lo ≤ κ ∧ κ < hi))).card =
      (cells.filter (fun c => ¬ (lo ≤ (net.exec xr c).val ∧
        (net.exec xr c).val < hi))).card := by
    rw [Finset.filter_image]
    simpa only [Function.comp_def] using
      (Finset.card_image_of_injective _ (Fin.val_injective.comp hnetInj))
  have hcount : ((cells.image (net.exec xr)).filter
      (fun κ : Fin M => ¬ (lo ≤ κ.val ∧ κ.val < hi))).card =
      ((cells.image (fun c => (net.exec xr c).val)).filter
        (fun κ => ¬ (lo ≤ κ ∧ κ < hi))).card := hfin.trans hnat.symm
  have h := physical_ragged_output_wrong_le hn σ₁ σ₂ epsB hB hBflip
    profile j hj1 hj63 xr hxr lo hi A hA
  rw [hcount]
  simpa [net, cells] using h

/-- Specialization to a bag's actual child-native interval. -/
theorem physical_ragged_output_fin_child_wrong_le
    {d m n : Nat} (hn : 0 < n)
    (σ₁ σ₂ : Scramble m n) (epsB : Real)
    (hB : HasPackSemanticPropertyB2 hn σ₁ σ₂ epsB)
    (hBflip : HasPackSemanticPropertyB2 hn (flipScramble σ₁) (flipScramble σ₂) epsB)
    (profile : RaggedFlowContract m) (j : Nat) (hj1 : 1 ≤ j) (hj63 : j ≤ 63)
    (xr : Fin (m * n) → Fin (64 ^ d)) (hxr : Function.Injective xr)
    (q : KBag 64 d) (hq : q.l < d) (A : Real)
    (hA : ((((keySet xr).image Fin.val).filter (fun κ =>
      (profile.start + raggedPrefixRows profile.width j) * n ≤
          BW.rankN ((keySet xr).image Fin.val) κ ∧
      BW.rankN ((keySet xr).image Fin.val) κ <
          (profile.start + raggedPrefixRows profile.width (j + 1)) * n ∧
      ¬ (q.x * 64 ^ (d - q.l) + j * 64 ^ (d - q.l - 1) ≤ κ ∧
          κ < q.x * 64 ^ (d - q.l) + (j + 1) * 64 ^ (d - q.l - 1)))).card : Real) ≤ A) :
    ((((Finset.univ.filter (fun c : Fin (m * n) =>
      (profile.start + raggedPrefixRows profile.width j) * n ≤ c.val ∧
      c.val < (profile.start + raggedPrefixRows profile.width (j + 1)) * n)).image
        (fun c => (physicalPack2Net m n hn σ₁ σ₂).exec xr c)).filter
        (fun κ => κ ∉ nativeKeys (q.child j  (by omega) hq))).card : Real) ≤
      A + epsB * (m * n) := by
  have h := physical_ragged_output_fin_wrong_le hn σ₁ σ₂ epsB hB hBflip
    profile j hj1 hj63 xr hxr
    (q.x * 64 ^ (d - q.l) + j * 64 ^ (d - q.l - 1))
    (q.x * 64 ^ (d - q.l) + (j + 1) * 64 ^ (d - q.l - 1)) A hA
  let outputs := (Finset.univ.filter (fun c : Fin (m * n) =>
        (profile.start + raggedPrefixRows profile.width j) * n ≤ c.val ∧
        c.val < (profile.start + raggedPrefixRows profile.width (j + 1)) * n)).image
          (fun c => (physicalPack2Net m n hn σ₁ σ₂).exec xr c)
  have hfilter :
      outputs.filter (fun κ => κ ∉ nativeKeys (q.child j (by omega) hq)) =
      outputs.filter (fun κ =>
        ¬ (q.x * 64 ^ (d - q.l) + j * 64 ^ (d - q.l - 1) ≤ κ.val ∧
          κ.val < q.x * 64 ^ (d - q.l) + (j + 1) * 64 ^ (d - q.l - 1))) := by
    apply Finset.filter_congr
    intro κ _
    simp only [nativeKeys, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [native_child_interval q hq j (by omega) κ]
  rw [hfilter]
  simpa [outputs] using h

end Tapered945
