import AKS.Sub800.R1Main
import AKS.Sub800.R1Cells
import AKS.Sub800.R2Cells
import AKS.Sub800.Fringe7934
import AKS.Sub800.Fringe406109

/-! # The 789.75 point

The R1 point of R1-PROOF: `μ = (1 − 2^-10)·63/4194304`, `δ = 135/10^8`, `ε_B = 1/105000`,
`ε_F = 1/190000`, `η = 1 + 7/4096`, `γ = μ/10`; bulk `R1Cells`/`R2Cells` (`E1 = 18421/50000000`)
on rows `[50859009, 2^26]`; Batcher's sort up to `2^45`; fringe classes `f = 7934` and
`f = 406109` at `δ_F = 1/8`, `J = 190000`. The stage depth is `3 S(26) = 1053`, so the generic
headline (`R1Main`) gives `3 · 1053/4 = 789.75`.

To re-price the route, change the data here (and regenerate the numeric certificates): the proofs in
`R1Kernel` … `R1Main` do not depend on these values. -/

namespace R1T

open Sub800 Chvatal SortingDepth Filter

/-- `μ = (1 − 2^-10) · μ₄₄`, `μ₄₄ = ½ δ_F (Aνk − 1)/(A²k²)`. -/
def mu78975 : ℚ := 1023 / 1024 * (63 / 4194304)

/-- The invariant scalars. -/
def sc78975 : R1Scal where
  mu := mu78975
  delta := 135 / 100000000
  epsB := 1 / 105000
  epsF := 1 / 190000
  eta := 1 + 7 / 4096
  gam := mu78975 / 10
  mu_pos := by unfold mu78975; norm_num
  delta_pos := by norm_num
  delta_le_one := by norm_num
  epsF_pos := by norm_num
  epsB_nonneg := by norm_num
  eta_nonneg := by norm_num
  gam_nonneg := by unfold mu78975; norm_num
  cond_sib := by norm_num
  cond42 := by unfold mu78975 rstar; norm_num
  cond45 := by norm_num
  mu_final := by unfold mu78975; norm_num
  mu_rise := by unfold mu78975; norm_num
  mu_mid := by unfold mu78975; norm_num

/-- The walk-bound bulk on rows `[50859009, 2^26]`. -/
noncomputable def bulk78975 : BulkCert where
  E1 := 18421 / 50000000
  epsB := 1 / 105000
  Mlo := 50859009
  q := 26
  r1 := fun hn hmM hm => R1Cells.round1_numeric hn (by exact_mod_cast hmM) hm
  r2 := fun hn hmM hmHi hm => R2Cells.round2_numeric hn (by exact_mod_cast hmM)
    (by norm_num at hmHi ⊢; exact hmHi) hm

/-- Fringe class `f = 7934`. -/
noncomputable def class7934 : FClass where
  C := ⟨Fringe7934.P, Fringe7934.fringe_fail⟩
  dF := 1 / 8
  hδ := by rw [Fringe7934.hδ]; norm_num

/-- Fringe class `f = 406109`. -/
noncomputable def class406109 : FClass where
  C := ⟨Fringe406109.P, Fringe406109.fringe_fail⟩
  dF := 1 / 8
  hδ := by rw [Fringe406109.hδ]; norm_num

theorem f7934 : Fringe7934.P.f = 7934 := by
  have := Fringe7934.hf; exact_mod_cast this

theorem f406109 : Fringe406109.P.f = 406109 := by
  have := Fringe406109.hf; exact_mod_cast this

/-- **The 789.75 point.** -/
noncomputable def point78975 : R1Point where
  sc := sc78975
  bulk := bulk78975
  s := 45
  A := class7934
  B := class406109
  hepsB := by simp [bulk78975, sc78975]
  hJA := by
    show (((1 / 190000 : ℚ)) : ℝ) = 1 / (Fringe7934.P.J : ℝ)
    rw [Fringe7934.hJ]; norm_num
  hJB := by
    show (((1 / 190000 : ℚ)) : ℝ) = 1 / (Fringe406109.P.J : ℝ)
    rw [Fringe406109.hJ]; norm_num
  hs := by norm_num
  batcher := by
    show bitonicDepthBudget 45 ≤ 3 * bitonicDepthBudget 26
    rw [bitonicDepthBudget_eq, bitonicDepthBudget_eq]; norm_num
  stage_big := by
    show 2845 ≤ 15 * (3 * bitonicDepthBudget 26)
    rw [bitonicDepthBudget_eq]; norm_num
  geomA63 := by
    show GeomOK Fringe7934.P.f 63 524032 525312 (2 ^ 45 / 525312 + 1) 50859009 26 mu78975 (1 / 8)
      (1 / 105000) (1 + 7 / 4096) (mu78975 / 10)
    rw [f7934]; unfold GeomOK mu78975; decide +kernel
  geomA64 := by
    show GeomOK Fringe7934.P.f 64 524032 525312 (2 ^ 45 / 525312 + 1) 50859009 26 mu78975 (1 / 8)
      (1 / 105000) (1 + 7 / 4096) (mu78975 / 10)
    rw [f7934]; unfold GeomOK mu78975; decide +kernel
  geomB := by
    show GeomOK Fringe406109.P.f 63 8176 8192 (2 ^ 45 / 8192 + 1) 50859009 26 mu78975 (1 / 8)
      (1 / 105000) (1 + 7 / 4096) (mu78975 / 10)
    rw [f406109]; unfold GeomOK mu78975; decide +kernel
  bonly := by
    show BonlyOK 45 50859009 26 (1 / 105000) (1 + 7 / 4096) (mu78975 / 10)
    unfold BonlyOK mu78975; decide +kernel
  root := by
    show (1 / 59000000 : ℚ) / 2 * 64 + 1 / 2 ^ 36 ≤ (1 / 105000 * (1 + 7 / 4096) + mu78975 / 10) / 2
    unfold mu78975; norm_num

theorem point78975_stage : point78975.stage = 1053 := by
  show 3 * bitonicDepthBudget 26 = 1053; rw [bitonicDepthBudget_eq]

/-- The R1 sorter at the 789.75 point: depth `≤ 2709 + 1053 (3d − 15) + 136` on `16^d` wires. -/
theorem r1_sorter_78975 {d : ℕ} (hd : 12 ≤ d) :
    ∃ T : ComparatorNetwork (16 ^ d), ComparatorNetwork.Sorts.{0} T ∧
      T.depth ≤ 2709 + 1053 * (3 * d - 15) + 136 := by
  simpa [point78975_stage] using r1_sorter point78975 hd

/-- **Pointwise bound.** For every `n ≥ 16^12`, `D(n) ≤ 789.75 · log₂ n + 3159`. -/
theorem minimum_depth_le {n : ℕ} (hn : 16 ^ 12 ≤ n) :
    (minimum n : ℝ) ≤ 3159 / 4 * Real.logb 2 (n : ℝ) + 3159 := by
  have := point78975.minimum_depth_le hn
  rw [point78975_stage] at this
  norm_num at this ⊢
  exact this

/-- **`limsup D(n)/log₂ n ≤ 789.75`.** -/
theorem limsup_minimum_div_logb_le_78975 :
    limsup (fun n : ℕ ↦ (minimum n : ℝ) / Real.logb 2 n) atTop ≤ (3159 / 4 : ℝ) := by
  have := point78975.limsup_minimum_div_logb_le
  rw [point78975_stage] at this
  norm_num at this ⊢
  exact this

/-- **`limsup D(n)/log₂ n ≤ 800`.** -/
theorem limsup_minimum_div_logb_le_800 :
    limsup (fun n : ℕ ↦ (minimum n : ℝ) / Real.logb 2 n) atTop ≤ (800 : ℝ) :=
  limsup_minimum_div_logb_le_78975.trans (by norm_num)

end R1T
