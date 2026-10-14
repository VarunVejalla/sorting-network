import SeparatorKeyBridge
import StageOneWindowGate
import RaggedBootstrapFlow

namespace Tapered945
open Chvatal

/-- Actual physical row-aligned ragged slots incur exactly two half-B errors. -/
theorem physical_ragged_output_wrong_le {m n M : Nat} (hn : 0 < n)
    (σ₁ σ₂ : Scramble m n) (epsB : Real)
    (hB : HasPackSemanticPropertyB2 hn σ₁ σ₂ epsB)
    (hBflip : HasPackSemanticPropertyB2 hn (flipScramble σ₁) (flipScramble σ₂) epsB)
    (profile : RaggedFlowContract m) (j : Nat) (hj1 : 1 ≤ j) (hj63 : j ≤ 63)
    (xr : Fin (m * n) → Fin M) (hxr : Function.Injective xr)
    (lo hi : Nat) (A : Real)
    (hA : ((((keySet xr).image Fin.val).filter (fun κ =>
      (profile.start + raggedPrefixRows profile.width j) * n ≤ BW.rankN ((keySet xr).image Fin.val) κ ∧
      BW.rankN ((keySet xr).image Fin.val) κ < (profile.start + raggedPrefixRows profile.width (j+1)) * n ∧
      ¬ (lo ≤ κ ∧ κ < hi))).card : Real) ≤ A) :
    ((((Finset.univ.filter (fun c : Fin (m*n) =>
      (profile.start + raggedPrefixRows profile.width j) * n ≤ c.val ∧
      c.val < (profile.start + raggedPrefixRows profile.width (j+1)) * n)).image
        (fun c => ((physicalPack2Net m n hn σ₁ σ₂).exec xr c).val)).filter
        (fun κ => ¬ (lo ≤ κ ∧ κ < hi))).card : Real) ≤ A + epsB * (m*n) := by
  have hl := (ragged_flow_boundary_bounds hn σ₁ σ₂ hB hBflip (rankPerm hxr) profile j hj1 (by omega)).2
  have hh := (ragged_flow_boundary_bounds hn σ₁ σ₂ hB hBflip (rankPerm hxr) profile (j+1) (by omega) (by omega)).1
  have h := separator_output_wrong_keys_le (physicalPack2Net m n hn σ₁ σ₂) xr hxr
    ((profile.start + raggedPrefixRows profile.width j)*n)
    ((profile.start + raggedPrefixRows profile.width (j+1))*n) lo hi A
    ((epsB/2)*(m*n)) ((epsB/2)*(m*n)) hA hl hh
  calc
    _ ≤ A + (epsB/2)*(m*n) + (epsB/2)*(m*n) := h
    _ = A + epsB*(m*n) := by ring

theorem bootstrap_cut_wires (d x j : Nat) :
    ((bootstrapRaggedProfile x).start +
      raggedPrefixRows (bootstrapRaggedProfile x).width j) * bootstrapColumns d =
      bootstrapUpRows x * bootstrapColumns d / 2 +
      ∑ i ∈ Finset.range j, bootstrapSlotRows x i * bootstrapColumns d := by
  change (bootstrapFringeRows x + ∑ i ∈ Finset.range j, bootstrapSlotRows x i) *
    bootstrapColumns d = _
  rw [Nat.add_mul, Finset.sum_mul]
  have he := bootstrap_fringe_rows_exact x
  have hm : bootstrapUpRows x * bootstrapColumns d =
      2 * (bootstrapFringeRows x * bootstrapColumns d) := by rw [he]; ring
  rw [hm]
  omega

theorem bootstrap_cut_wires_succ (d x j : Nat) :
    ((bootstrapRaggedProfile x).start +
      raggedPrefixRows (bootstrapRaggedProfile x).width (j+1)) * bootstrapColumns d =
      bootstrapUpRows x * bootstrapColumns d / 2 +
      (∑ i ∈ Finset.range j, bootstrapSlotRows x i * bootstrapColumns d) +
      bootstrapSlotRows x j * bootstrapColumns d := by
  rw [bootstrap_cut_wires, Finset.sum_range_succ]
  omega

/-- The actual stage-one register, enumerated injectively and passed through
the physical bootstrap separator. The B2 provider is an explicit premise;
this theorem does not assert existence of the required scrambles. -/
theorem candidate_bootstrap_stage_one_output_wrong_le
    (d : Nat) (hd : 14 ≤ d)
    (nets : Nat → (b : KBag 64 d) → (n : Nat) → ComparatorNetwork n)
    (v : Equiv.Perm (Fin (64 ^ d)))
    (hspec : NodeSpec (seedRootInput d) 0 (seedRootDown d)
      (nets 0 (KBag.root 64 d) (seedRootInput d))
      (specEB 0 (seedRootInput d)) (specJmax 0) eps)
    (a : Fin 64) (j : Nat) (hj1 : 1 ≤ j) (hj62 : j ≤ 62)
    (hn : 0 < bootstrapColumns d)
    (σ₁ σ₂ : Scramble bootstrapRows (bootstrapColumns d)) (epsB : Real)
    (hB : HasPackSemanticPropertyB2 hn σ₁ σ₂ epsB)
    (hBflip : HasPackSemanticPropertyB2 hn (flipScramble σ₁) (flipScramble σ₂) epsB) :
    let b := (KBag.root 64 d).child a.val a.isLt (by simp [KBag.root]; omega)
    let K := ((execPlacement (candidateSeedFlowSizes d hd) nets v 1 (by omega)).regs b).image Fin.val
    let U := b.x * 64 ^ (d - b.l)
    let S := 64 ^ (d - b.l - 1)
    ∀ (xr : Fin (bootstrapRows * bootstrapColumns d) → Fin (64^d)),
      Function.Injective xr → (keySet xr).image Fin.val = K →
    ((((Finset.univ.filter (fun c : Fin (bootstrapRows * bootstrapColumns d) =>
      ((bootstrapRaggedProfile b.x).start +
        raggedPrefixRows (bootstrapRaggedProfile b.x).width j) * bootstrapColumns d ≤ c.val ∧
      c.val < ((bootstrapRaggedProfile b.x).start +
        raggedPrefixRows (bootstrapRaggedProfile b.x).width (j+1)) * bootstrapColumns d)).image
      (fun c => ((physicalPack2Net bootstrapRows (bootstrapColumns d) hn σ₁ σ₂).exec xr c).val)).filter
      (fun κ => ¬ (U+j*S ≤ κ ∧ κ < U+(j+1)*S))).card : Real) ≤
      2 * paperRootEpsB * (64 : Real)^d + ((reserve * seedRootDown d : Rat) : Real) +
        epsB * seedRootDown d := by
  intro b K U S xr hxr hkeys
  have hinput := candidate_bootstrap_stage_one_wrong_rank_bound d hd nets v hspec a j hj1 hj62
  have hA : ((((keySet xr).image Fin.val).filter (fun κ =>
      ((bootstrapRaggedProfile b.x).start + raggedPrefixRows (bootstrapRaggedProfile b.x).width j) *
        bootstrapColumns d ≤ BW.rankN ((keySet xr).image Fin.val) κ ∧
      BW.rankN ((keySet xr).image Fin.val) κ <
        ((bootstrapRaggedProfile b.x).start + raggedPrefixRows (bootstrapRaggedProfile b.x).width (j+1)) *
          bootstrapColumns d ∧ ¬ (U+j*S ≤ κ ∧ κ < U+(j+1)*S))).card : Real) ≤
      2 * paperRootEpsB * (64 : Real)^d + ((reserve * seedRootDown d : Rat) : Real) := by
    rw [hkeys, bootstrap_cut_wires, bootstrap_cut_wires_succ]
    exact hinput
  have h := physical_ragged_output_wrong_le hn σ₁ σ₂ epsB hB hBflip
    (bootstrapRaggedProfile b.x) j hj1 (by omega) xr hxr (U+j*S) (U+(j+1)*S)
    (2 * paperRootEpsB * (64 : Real)^d + ((reserve * seedRootDown d : Rat) : Real)) hA
  have hfactor : (bootstrapRows : Real) * bootstrapColumns d = (seedRootDown d : Real) := by
    exact_mod_cast (bootstrap_input_factorization d hd).symm
  rw [hfactor] at h
  exact h

end Tapered945
