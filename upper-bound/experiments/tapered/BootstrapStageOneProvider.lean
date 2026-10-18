import BootstrapSeparatorOutput
import TruncatedFringeProvider
import WireRoundingBudget

namespace Tapered945

open Chvatal

/-- The exact rectangular dimensions used by the stage-one bootstrap admit
one scramble pair with both orientations' bulk certificates and all four
truncated fringe certificates. -/
theorem bootstrap_separator_pair_exists (d : Nat) (hd : 14 ≤ d) :
    ∃ σ₁ σ₂ : Scramble bootstrapRows (bootstrapColumns d),
      HasPackSemanticPropertyB2 (by have h := bootstrapColumns_ge16 d hd; omega)
        σ₁ σ₂ (1/2^21) ∧
      HasPackSemanticPropertyB2 (by have h := bootstrapColumns_ge16 d hd; omega)
        (flipScramble σ₁) (flipScramble σ₂) (1/2^21) ∧
      F2SmallRank F2Params.std (truncateBottomScramble σ₁) ∧
      F2R1 F2Params.std (truncateBottomScramble σ₁) ∧
      F2R2n F2Params.std (truncateBottomScramble σ₂) ∧
      F2SmallRank F2Params.std (truncateBottomScramble (flipScramble σ₁)) ∧
      F2R1 F2Params.std (truncateBottomScramble (flipScramble σ₁)) ∧
      F2R2n F2Params.std (truncateBottomScramble (flipScramble σ₂)) := by
  have hrows : 2^34 ≤ bootstrapRows := by norm_num [bootstrapRows]
  have hretained : 131040 ≤ bootstrapRows - 1 := by norm_num [bootstrapRows]
  have hn : 16 ≤ bootstrapColumns d := bootstrapColumns_ge16 d hd
  have hpos : 0 < bootstrapRows := by norm_num [bootstrapRows]
  have hrows' : 2^34 ≤ (bootstrapRows - 1) + 1 := by omega
  obtain ⟨σ₁, σ₂, hnormal, hflip⟩ :=
    truncated_fringe_bulk_pair_exists (m := bootstrapRows - 1)
      hrows' hretained hn
  refine ⟨σ₁, σ₂, ?_, ?_, hnormal.1, hnormal.2.1, hnormal.2.2.1,
    hflip.1, hflip.2.1, hflip.2.2.1⟩
  · exact hnormal.2.2.2
  · exact hflip.2.2.2

/-- The separator's stage-one output allowance is exactly within the next
reference-capacity order-zero budget. This is a scalar comparison; the local
output theorem supplies the left-hand side for each actual child. -/
theorem bootstrap_stage_one_separator_budget_le (d : Nat) (hd : 14 ≤ d) :
    2 * Chvatal.paperRootEpsB * (64 : Real)^d +
      ((reserve * seedRootDown d : Rat) : Real) +
      ((epsB * seedRootDown d : Rat) : Real) ≤
        (mu : Real) * (4 * (seedRootDown d : Real)) := by
  have hroot : (64 : Real)^d = 64 * (seedRootDown d : Real) := by
    exact_mod_cast (seed_root_conservation d (by omega))
  have hreserve : ((reserve * seedRootDown d : Rat) : Real) =
      (reserve : Real) * (seedRootDown d : Real) := by norm_cast
  have heps : ((epsB * seedRootDown d : Rat) : Real) =
      (epsB : Real) * (seedRootDown d : Real) := by norm_cast
  rw [hroot, hreserve, heps]
  calc
    (2 * Chvatal.paperRootEpsB * (64 * (seedRootDown d : Real)) +
        (reserve : Real) * (seedRootDown d : Real) +
        (epsB : Real) * (seedRootDown d : Real)) =
      (2 * Chvatal.paperRootEpsB * 64 + (reserve : Real) + (epsB : Real)) *
        (seedRootDown d : Real) := by ring
    _ ≤ (mu : Real) * (4 * (seedRootDown d : Real)) :=
      bootstrap_output_budget_le (seedRootDown d : Real) (by positivity)

/-- Enumerate any finite set without losing injectivity or its image. -/
theorem exists_injective_finset_enum {α : Type*} [DecidableEq α] (S : Finset α) :
    ∃ f : Fin S.card → α, Function.Injective f ∧ Finset.univ.image f = S := by
  classical
  let e : Fin S.card ≃ S := Fintype.equivOfCardEq (by simp)
  refine ⟨fun i => (e i).val, ?_, ?_⟩
  · intro i j h
    apply Fin.ext
    exact congrArg Fin.val (e.injective (Subtype.ext h))
  · ext x
    constructor
    · intro hx
      rcases Finset.mem_image.mp hx with ⟨i, -, rfl⟩
      exact (e i).property
    · intro hx
      let i : Fin S.card := e.symm ⟨x, hx⟩
      refine Finset.mem_image.mpr ⟨i, Finset.mem_univ i, ?_⟩
      exact congrArg Subtype.val (e.apply_symm_apply ⟨x, hx⟩)

/-- The actual stage-one child register has exactly the bootstrap rectangle's
cardinality, hence can be enumerated as the input of its next physical pack. -/
theorem bootstrap_stage_one_child_enum
    (d : Nat) (hd : 14 ≤ d)
    (nets : Nat → (b : KBag 64 d) → (n : Nat) → ComparatorNetwork n)
    (v : Equiv.Perm (Fin (64^d))) (a : Fin 64) :
    let b := (KBag.root 64 d).child a.val a.isLt (by simp [KBag.root]; omega)
    let S := (execPlacement (candidateSeedFlowSizes d hd) nets v 1 (by omega)).regs b
    ∃ xr : Fin (bootstrapRows * bootstrapColumns d) → Fin (64^d),
      Function.Injective xr ∧ (keySet xr).image Fin.val = S.image Fin.val := by
  classical
  dsimp
  let b := (KBag.root 64 d).child a.val a.isLt (by simp [KBag.root]; omega)
  let S := (execPlacement (candidateSeedFlowSizes d hd) nets v 1 (by omega)).regs b
  have hb : b.l = 1 := by simp [b, KBag.root, KBag.child_l]
  have hcard : S.card = bootstrapRows * bootstrapColumns d := by
    calc
      S.card = seedRootDown d := by
        dsimp [S]
        rw [execPlacement_card]
        simp [candidateSeedFlowSizes, seedNodeSize, b, hb, seedRootDown]
      _ = bootstrapRows * bootstrapColumns d := bootstrap_input_factorization d hd
  let e : Fin (bootstrapRows * bootstrapColumns d) ≃ S :=
    Fintype.equivOfCardEq (by simp [hcard])
  let xr : Fin (bootstrapRows * bootstrapColumns d) → Fin (64^d) := fun i => (e i).val
  have hinj : Function.Injective xr := by
    intro i j h
    apply e.injective
    exact Subtype.ext h
  have himage : Finset.univ.image xr = S := by
    ext x
    constructor
    · intro hx
      rcases Finset.mem_image.mp hx with ⟨i, -, rfl⟩
      exact (e i).property
    · intro hx
      let i : Fin (bootstrapRows * bootstrapColumns d) := e.symm ⟨x, hx⟩
      refine Finset.mem_image.mpr ⟨i, Finset.mem_univ i, ?_⟩
      exact congrArg Subtype.val (e.apply_symm_apply ⟨x, hx⟩)
  refine ⟨xr, hinj, ?_⟩
  change (Finset.univ.image xr).image Fin.val = S.image Fin.val
  rw [himage]

/-- Apply the ragged separator output estimate to the actual stage-one child
register. Its input enumeration is now constructed from the register itself. -/
theorem candidate_bootstrap_stage_one_actual_output_wrong_le
    (d : Nat) (hd : 14 ≤ d)
    (nets : Nat → (b : KBag 64 d) → (n : Nat) → ComparatorNetwork n)
    (v : Equiv.Perm (Fin (64^d)))
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
    ∃ xr : Fin (bootstrapRows * bootstrapColumns d) → Fin (64^d),
      Function.Injective xr ∧ (keySet xr).image Fin.val = K ∧
      ((((Finset.univ.filter (fun c : Fin (bootstrapRows * bootstrapColumns d) =>
        ((bootstrapRaggedProfile b.x).start +
          raggedPrefixRows (bootstrapRaggedProfile b.x).width j) * bootstrapColumns d ≤ c.val ∧
        c.val < ((bootstrapRaggedProfile b.x).start +
          raggedPrefixRows (bootstrapRaggedProfile b.x).width (j+1)) * bootstrapColumns d)).image
        (fun c => ((physicalPack2Net bootstrapRows (bootstrapColumns d) hn σ₁ σ₂).exec xr c).val)).filter
        (fun κ => ¬ (U+j*S ≤ κ ∧ κ < U+(j+1)*S))).card : Real) ≤
          2 * paperRootEpsB * (64 : Real)^d + ((reserve * seedRootDown d : Rat) : Real) +
            epsB * seedRootDown d := by
  intro b K U S
  obtain ⟨xr, hxr, hkeys⟩ := bootstrap_stage_one_child_enum d hd nets v a
  refine ⟨xr, hxr, hkeys, ?_⟩
  exact candidate_bootstrap_stage_one_output_wrong_le d hd nets v hspec a j hj1 hj62
    hn σ₁ σ₂ epsB hB hBflip xr hxr hkeys

/-- Unconditional local stage-one separator transition: compatible two-sided
bulk scrambles exist at the exact bootstrap rectangle, the actual child
register is enumerated, and its post-separator slot error has the explicit
root-reserve-plus-bulk bound. The root `NodeSpec` remains the stated premise. -/
theorem candidate_bootstrap_stage_one_actual_output_exists
    (d : Nat) (hd : 14 ≤ d)
    (nets : Nat → (b : KBag 64 d) → (n : Nat) → ComparatorNetwork n)
    (v : Equiv.Perm (Fin (64^d)))
    (hspec : NodeSpec (seedRootInput d) 0 (seedRootDown d)
      (nets 0 (KBag.root 64 d) (seedRootInput d))
      (specEB 0 (seedRootInput d)) (specJmax 0) eps)
    (a : Fin 64) (j : Nat) (hj1 : 1 ≤ j) (hj62 : j ≤ 62)
    (hn : 0 < bootstrapColumns d) :
    let b := (KBag.root 64 d).child a.val a.isLt (by simp [KBag.root]; omega)
    let K := ((execPlacement (candidateSeedFlowSizes d hd) nets v 1 (by omega)).regs b).image Fin.val
    let U := b.x * 64 ^ (d - b.l)
    let S := 64 ^ (d - b.l - 1)
    ∃ σ₁ σ₂ : Scramble bootstrapRows (bootstrapColumns d),
      ∃ xr : Fin (bootstrapRows * bootstrapColumns d) → Fin (64^d),
        HasPackSemanticPropertyB2 hn σ₁ σ₂ (1/2^21) ∧
        HasPackSemanticPropertyB2 hn (flipScramble σ₁) (flipScramble σ₂) (1/2^21) ∧
        Function.Injective xr ∧ (keySet xr).image Fin.val = K ∧
        ((((Finset.univ.filter (fun c : Fin (bootstrapRows * bootstrapColumns d) =>
          ((bootstrapRaggedProfile b.x).start +
            raggedPrefixRows (bootstrapRaggedProfile b.x).width j) * bootstrapColumns d ≤ c.val ∧
          c.val < ((bootstrapRaggedProfile b.x).start +
            raggedPrefixRows (bootstrapRaggedProfile b.x).width (j+1)) * bootstrapColumns d)).image
          (fun c => ((physicalPack2Net bootstrapRows (bootstrapColumns d) hn σ₁ σ₂).exec xr c).val)).filter
          (fun κ => ¬ (U+j*S ≤ κ ∧ κ < U+(j+1)*S))).card : Real) ≤
            2 * paperRootEpsB * (64 : Real)^d + ((reserve * seedRootDown d : Rat) : Real) +
              (1/2^21 : Real) * seedRootDown d ∧
        ((((Finset.univ.filter (fun c : Fin (bootstrapRows * bootstrapColumns d) =>
          ((bootstrapRaggedProfile b.x).start +
            raggedPrefixRows (bootstrapRaggedProfile b.x).width j) * bootstrapColumns d ≤ c.val ∧
          c.val < ((bootstrapRaggedProfile b.x).start +
            raggedPrefixRows (bootstrapRaggedProfile b.x).width (j+1)) * bootstrapColumns d)).image
          (fun c => ((physicalPack2Net bootstrapRows (bootstrapColumns d) hn σ₁ σ₂).exec xr c).val)).filter
          (fun κ => ¬ (U+j*S ≤ κ ∧ κ < U+(j+1)*S))).card : Real) ≤
            (mu : Real) * (4 * (seedRootDown d : Real)) := by
  intro b K U S
  obtain ⟨σ₁, σ₂, hB, hBflip, -, -, -, -, -, -⟩ :=
    bootstrap_separator_pair_exists d hd
  obtain ⟨xr, hxr, hkeys, houtput⟩ :=
    candidate_bootstrap_stage_one_actual_output_wrong_le d hd nets v hspec a j hj1 hj62
      hn σ₁ σ₂ (1/2^21) hB hBflip
  have heps : (1/2^21 : Real) * seedRootDown d =
      ((epsB * seedRootDown d : Rat) : Real) := by norm_num [epsB]
  refine ⟨σ₁, σ₂, xr, hB, hBflip, hxr, hkeys, houtput, ?_⟩
  calc
    _ ≤ 2 * paperRootEpsB * (64 : Real)^d +
        ((reserve * seedRootDown d : Rat) : Real) +
        ((epsB * seedRootDown d : Rat) : Real) := by rw [← heps]; exact houtput
    _ ≤ (mu : Real) * (4 * (seedRootDown d : Real)) :=
      bootstrap_stage_one_separator_budget_le d hd

end Tapered945
