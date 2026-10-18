import RaggedPackNativeError
import Mathlib.Tactic

namespace Tapered945

open Chvatal

/-- The first child slot also has the usual two-boundary B2 output estimate.
Unlike an internal slot, its left boundary is the initial fringe, so its
positivity is supplied explicitly. The right boundary follows from the
positive width of slot zero and the profile prefix bound. -/
theorem physical_ragged_output_fin_wrong_le_endpoint
    {m n M : Nat} (hn : 0 < n)
    (σ₁ σ₂ : Scramble m n) (epsB : Real)
    (hB : HasPackSemanticPropertyB2 hn σ₁ σ₂ epsB)
    (hBflip : HasPackSemanticPropertyB2 hn (flipScramble σ₁) (flipScramble σ₂) epsB)
    (profile : RaggedFlowContract m)
    (hstart : 1 ≤ profile.start) (hwidth : 0 < profile.width 0)
    (xr : Fin (m * n) → Fin M) (hxr : Function.Injective xr)
    (lo hi : Nat) (A : Real)
    (hA : ((((keySet xr).image Fin.val).filter (fun κ =>
      profile.start * n ≤ BW.rankN ((keySet xr).image Fin.val) κ ∧
      BW.rankN ((keySet xr).image Fin.val) κ <
          (profile.start + profile.width 0) * n ∧
      ¬ (lo ≤ κ ∧ κ < hi))).card : Real) ≤ A) :
    ((((Finset.univ.filter (fun c : Fin (m * n) =>
      profile.start * n ≤ c.val ∧
      c.val < (profile.start + profile.width 0) * n)).image
        (fun c => (physicalPack2Net m n hn σ₁ σ₂).exec xr c)).filter
        (fun κ => ¬ (lo ≤ κ.val ∧ κ.val < hi))).card : Real) ≤
      A + epsB * (m * n) := by
  let net := physicalPack2Net m n hn σ₁ σ₂
  let cells := Finset.univ.filter (fun c : Fin (m * n) =>
    profile.start * n ≤ c.val ∧
      c.val < (profile.start + profile.width 0) * n)
  have hright_pos : 1 ≤ profile.start + raggedPrefixRows profile.width 1 := by
    simp [raggedPrefixRows]
    omega
  have hleft_bound : profile.start + raggedPrefixRows profile.width 0 ≤ m := by
    have hp := profile.prefix_bound 0 (by omega)
    simpa [raggedPrefixRows] using hp.trans (Nat.sub_le _ _)
  have hright_bound : profile.start + raggedPrefixRows profile.width 1 ≤ m := by
    have hp := profile.prefix_bound 1 (by omega)
    exact hp.trans (Nat.sub_le _ _)
  have hL := pack2_ragged_boundary_low hn σ₁ σ₂ hBflip
    (rankPerm hxr) profile.width 0 profile.start hstart hleft_bound
  have hH := pack2_ragged_boundary_high hn σ₁ σ₂ hB
    (rankPerm hxr) profile.width 1 profile.start hright_pos hright_bound
  have h := separator_output_wrong_keys_le net xr hxr
    (profile.start * n) ((profile.start + profile.width 0) * n) lo hi A
    ((epsB / 2) * (m * n)) ((epsB / 2) * (m * n)) hA hL hH
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
  rw [hcount]
  have hout := h
  simp only [net] at hout
  calc
    _ ≤ A + (epsB / 2) * (m * n) + (epsB / 2) * (m * n) := hout
    _ = A + epsB * (m * n) := by ring

/-- Endpoint specialization to the first actual native child interval. -/
theorem physical_ragged_output_fin_child_wrong_le_endpoint
    {d m n : Nat} (hn : 0 < n)
    (σ₁ σ₂ : Scramble m n) (epsB : Real)
    (hB : HasPackSemanticPropertyB2 hn σ₁ σ₂ epsB)
    (hBflip : HasPackSemanticPropertyB2 hn (flipScramble σ₁) (flipScramble σ₂) epsB)
    (profile : RaggedFlowContract m)
    (hstart : 1 ≤ profile.start) (hwidth : 0 < profile.width 0)
    (xr : Fin (m * n) → Fin (64 ^ d)) (hxr : Function.Injective xr)
    (q : KBag 64 d) (hq : q.l < d) (A : Real)
    (hA : ((((keySet xr).image Fin.val).filter (fun κ =>
      profile.start * n ≤ BW.rankN ((keySet xr).image Fin.val) κ ∧
      BW.rankN ((keySet xr).image Fin.val) κ <
          (profile.start + profile.width 0) * n ∧
      ¬ (q.x * 64 ^ (d - q.l) ≤ κ ∧
          κ < q.x * 64 ^ (d - q.l) + 64 ^ (d - q.l - 1)))).card : Real) ≤ A) :
    ((((Finset.univ.filter (fun c : Fin (m * n) =>
      profile.start * n ≤ c.val ∧
      c.val < (profile.start + profile.width 0) * n)).image
        (fun c => (physicalPack2Net m n hn σ₁ σ₂).exec xr c)).filter
        (fun κ => κ ∉ nativeKeys (q.child 0 (by omega) hq))).card : Real) ≤
      A + epsB * (m * n) := by
  have h := physical_ragged_output_fin_wrong_le_endpoint hn σ₁ σ₂ epsB
    hB hBflip profile hstart hwidth xr hxr
    (q.x * 64 ^ (d - q.l))
    (q.x * 64 ^ (d - q.l) + 64 ^ (d - q.l - 1)) A hA
  let outputs := (Finset.univ.filter (fun c : Fin (m * n) =>
      profile.start * n ≤ c.val ∧
      c.val < (profile.start + profile.width 0) * n)).image
        (fun c => (physicalPack2Net m n hn σ₁ σ₂).exec xr c)
  have hfilter :
      outputs.filter (fun κ => κ ∉ nativeKeys (q.child 0 (by omega) hq)) =
      outputs.filter (fun κ =>
        ¬ (q.x * 64 ^ (d - q.l) ≤ κ.val ∧
          κ.val < q.x * 64 ^ (d - q.l) + 64 ^ (d - q.l - 1))) := by
    apply Finset.filter_congr
    intro κ _
    simp only [nativeKeys, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [native_child_interval q hq 0 (by omega) κ]
    simp
  rw [hfilter]
  simpa [outputs] using h

end Tapered945
