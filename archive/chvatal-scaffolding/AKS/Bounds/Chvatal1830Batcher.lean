import AKS.Bounds.Asymptotic
import AKS.Chvatal.BatcherAssembly
import AKS.Chvatal.StageAssembly
import AKS.Sort.Shrink

/-! # Finite-range 1830-form bound via full-wire Batcher

**Honest status.** Full-wire Batcher on `64^d` has depth `≤ totalDepth d` for
`7 ≤ d ≤ 603` (`batcherFitsTotalDepthMax`). Restricting to `n` wires with
`Nat.clog 64 n = d` yields a sorting network whose depth meets the padded
§7 form `1830 log₂ n − 58657`. This is **not** the paper Chvátal schedule, and
it does **not** give `limsup D(n)/log₂ n ≤ 1830` (Batcher exceeds `totalDepth`
for every `d > 603`; see `bitonicDepthBudget_6d_gt_totalDepth`).

Strongest unconditional endpoints:
* `minimum_depth_le_1830_logb_of_batcher_range` — every `n` with
  `7 ≤ clog 64 n ≤ 603`;
* `exists_batcher_totalDepth_of_le_max` — Batcher witnesses for that `d`-range;
* `limsup_minimum_div_logb_le_1830_of_forall_totalDepth` — conditional limsup
  if every `d ≥ 7` has some sorter of depth `≤ totalDepth d`;
* `Limsup1830Residual` — open obligation for `d > 603`.
-/

namespace SortingDepth

open Chvatal Filter
open scoped Topology

/-- Restricted Batcher witness on `n` wires when `7 ≤ clog 64 n ≤ 603`. -/
def batcher1830Network (n : ℕ) (d : ℕ) (hclog : Nat.clog 64 n = d)
    (_hd : 7 ≤ d) (_hmax : d ≤ batcherFitsTotalDepthMax) : ComparatorNetwork n :=
  (chvatalFinalBatcherNet d).restrictWires n (by
    rw [← hclog]
    exact Nat.le_pow_clog (by decide : 1 < 64) n)

theorem batcher1830Network_sorts (n d : ℕ) (hclog : Nat.clog 64 n = d)
    (hd : 7 ≤ d) (hmax : d ≤ batcherFitsTotalDepthMax) :
    ComparatorNetwork.Sorts.{0} (batcher1830Network n d hclog hd hmax) :=
  restrictWires_sorts (chvatalFinalBatcherNet d) n
    (by rw [← hclog]; exact Nat.le_pow_clog (by decide : 1 < 64) n)
    (fun v ↦ (chvatalFinalBatcherNet_sorts d) (α := Bool) v)

theorem batcher1830Network_depth_le (n d : ℕ) (hclog : Nat.clog 64 n = d)
    (hd : 7 ≤ d) (hmax : d ≤ batcherFitsTotalDepthMax) :
    (batcher1830Network n d hclog hd hmax).depth ≤ totalDepth d :=
  (restrictWires_depth_le _ _ _).trans
    (chvatalFinalBatcherNet_depth_le_totalDepth hd hmax)

/-- Kernel-checked: for `1 < n` with `7 ≤ clog 64 n ≤ 603`,
    `D(n) ≤ 1830 log₂ n − 58657`. Stages are Batcher, not paper separators. -/
theorem minimum_depth_le_1830_logb_of_batcher_range {n : ℕ} (hn : 1 < n)
    (hd : 7 ≤ Nat.clog 64 n) (hmax : Nat.clog 64 n ≤ batcherFitsTotalDepthMax) :
    (minimum n : ℝ) ≤ 1830 * Real.logb 2 (n : ℝ) - 58657 := by
  set d := Nat.clog 64 n
  have hclog : Nat.clog 64 n = d := rfl
  let net := batcher1830Network n d hclog hd hmax
  have hs := batcher1830Network_sorts n d hclog hd hmax
  have hm : (minimum n : ℝ) ≤ (net.depth : ℝ) := by
    exact_mod_cast minimum_le net hs
  have hdep := batcher1830Network_depth_le n d hclog hd hmax
  have h1 : (net.depth : ℝ) ≤ (totalDepth d : ℝ) := by exact_mod_cast hdep
  exact hm.trans (h1.trans (totalDepth_logb_le hd hclog hn))

/-- Explicit Batcher witnesses of depth `≤ totalDepth d` on the finite range. -/
theorem exists_batcher_totalDepth_of_le_max {d : ℕ} (hd : 7 ≤ d)
    (hmax : d ≤ batcherFitsTotalDepthMax) :
    ∃ net : ComparatorNetwork (64 ^ d),
      ComparatorNetwork.Sorts.{0} net ∧ net.depth ≤ totalDepth d :=
  ⟨chvatalFinalBatcherNet d, chvatalFinalBatcherNet_sorts d,
    chvatalFinalBatcherNet_depth_le_totalDepth hd hmax⟩

/-- Conditional limsup package: a sorting net of depth `≤ totalDepth d` for every
    `d ≥ 7` implies `limsup D(n)/log₂ n ≤ 1830`. Still open unconditionally
    (Batcher only reaches `d ≤ 603`; paper separators remain for large `d`). -/
theorem limsup_minimum_div_logb_le_1830_of_forall_totalDepth
    (h : ∀ d : ℕ, 7 ≤ d →
      ∃ net : ComparatorNetwork (64 ^ d),
        ComparatorNetwork.Sorts.{0} net ∧ net.depth ≤ totalDepth d) :
    limsup (fun n : ℕ ↦ (minimum n : ℝ) / Real.logb 2 n) atTop ≤ (1830 : ℝ) := by
  have hnonneg : ∀ᶠ n : ℕ in atTop, 0 ≤ (minimum n : ℝ) / Real.logb 2 n := by
    filter_upwards [eventually_ge_atTop 2] with n hn
    have hnR : (1 : ℝ) < n := by exact_mod_cast (show 1 < n by omega)
    exact div_nonneg (Nat.cast_nonneg _) (Real.logb_pos (by norm_num) hnR).le
  have hle : ∀ᶠ n : ℕ in atTop,
      (minimum n : ℝ) / Real.logb 2 n ≤ (1830 : ℝ) := by
    filter_upwards [eventually_ge_atTop (64 ^ 7)] with n hn64
    have hn : 1 < n := lt_of_lt_of_le (by decide : 1 < 64 ^ 7) hn64
    have hd7 : 7 ≤ Nat.clog 64 n := by
      have hmono : Nat.clog 64 (64 ^ 7) ≤ Nat.clog 64 n :=
        Nat.clog_mono_right 64 hn64
      rwa [Chvatal.clog64_pow_eq 7] at hmono
    set d := Nat.clog 64 n
    obtain ⟨net0, hs0, hdep0⟩ := h d hd7
    have hle_pow : n ≤ 64 ^ d := by
      rw [← show Nat.clog 64 n = d from rfl]
      exact Nat.le_pow_clog (by decide : 1 < 64) n
    let net := net0.restrictWires n hle_pow
    have hs : ComparatorNetwork.Sorts.{0} net :=
      restrictWires_sorts net0 n hle_pow (fun v ↦ hs0 (α := Bool) v)
    have hdep : net.depth ≤ totalDepth d :=
      (restrictWires_depth_le _ _ _).trans hdep0
    have hm : (minimum n : ℝ) ≤ (net.depth : ℝ) := by
      exact_mod_cast minimum_le net hs
    have h1 : (net.depth : ℝ) ≤ (totalDepth d : ℝ) := by exact_mod_cast hdep
    have hpad : (net.depth : ℝ) ≤ 1830 * Real.logb 2 (n : ℝ) - 58657 :=
      h1.trans (totalDepth_logb_le hd7 rfl hn)
    have hbound : (minimum n : ℝ) ≤ 1830 * Real.logb 2 (n : ℝ) :=
      (hm.trans hpad).trans (by linarith)
    have hnR : (1 : ℝ) < n := by exact_mod_cast hn
    have hl : 0 < Real.logb 2 (n : ℝ) := Real.logb_pos (by norm_num) hnR
    exact (div_le_iff₀ hl).mpr (by
      simpa [mul_comm] using hbound)
  exact (limsup_le_limsup hle
    (isCoboundedUnder_le_of_eventually_le atTop hnonneg)
    isBoundedUnder_const).trans (le_of_eq (limsup_const (1830 : ℝ)))

/-- Residual for unconditional `limsup ≤ 1830`: need sorters of depth
    `≤ totalDepth d` for every `d > 603`. Batcher cannot supply them. -/
def Limsup1830Residual : Prop :=
  ∀ d : ℕ, batcherFitsTotalDepthMax < d →
    ∃ net : ComparatorNetwork (64 ^ d),
      ComparatorNetwork.Sorts.{0} net ∧ net.depth ≤ totalDepth d

/-- Combining the Batcher range with `Limsup1830Residual` yields limsup `≤ 1830`. -/
theorem limsup_minimum_div_logb_le_1830_of_batcher_and_residual
    (hRes : Limsup1830Residual) :
    limsup (fun n : ℕ ↦ (minimum n : ℝ) / Real.logb 2 n) atTop ≤ (1830 : ℝ) := by
  refine limsup_minimum_div_logb_le_1830_of_forall_totalDepth ?_
  intro d hd
  by_cases hmax : d ≤ batcherFitsTotalDepthMax
  · exact exists_batcher_totalDepth_of_le_max hd hmax
  · exact hRes d (lt_of_not_ge hmax)

/-- If paper depth-shell assemblies sort for every `d > 603`, limsup `≤ 1830`.
    Depth `≤ totalDepth` is kernel-checked (`paperDepthShellNetwork_depth_le`);
    `Sorts` remains `PaperDepthShellSortResidual`. -/
theorem limsup_minimum_div_logb_le_1830_of_paperDepthShellSorts
    (hσr : ∀ d : ℕ, batcherFitsTotalDepthMax < d →
      Scramble paperRootGeometry.m paperRootGeometry.n)
    (hσo : ∀ d : ℕ, batcherFitsTotalDepthMax < d →
      Scramble paperOrdinaryGeometry.m paperOrdinaryGeometry.n)
    (hs : ∀ d : ℕ, (hd : batcherFitsTotalDepthMax < d) →
      PaperDepthShellSortResidual d (by
        exact (by decide : 14 ≤ 604).trans (Nat.succ_le_of_lt hd))
        (hσr d hd) (hσo d hd)) :
    limsup (fun n : ℕ ↦ (minimum n : ℝ) / Real.logb 2 n) atTop ≤ (1830 : ℝ) := by
  refine limsup_minimum_div_logb_le_1830_of_batcher_and_residual ?_
  intro d hd
  have hd14 : 14 ≤ d := (by decide : 14 ≤ 604).trans (Nat.succ_le_of_lt hd)
  exact exists_totalDepth_of_paperDepthShellSorts hd hd14 (hσr d hd) (hσo d hd) (hs d hd)

/-- Default scramble (identity on each row) for pack tiling depth shells. -/
def identityScramble (m n : Nat) : Scramble m n :=
  fun _ => 1

/-- If paper depth-shell networks sort for every `d > 603` (identity scrambles),
    then limsup `≤ 1830`. Depth is already kernel-checked. -/
theorem limsup_minimum_div_logb_le_1830_of_paperDepthShellSorts_id
    (hs : ∀ d : ℕ, (hd : batcherFitsTotalDepthMax < d) →
      PaperDepthShellSortResidual d
        ((by decide : 14 ≤ 604).trans (Nat.succ_le_of_lt hd))
        (identityScramble _ _) (identityScramble _ _)) :
    limsup (fun n : ℕ ↦ (minimum n : ℝ) / Real.logb 2 n) atTop ≤ (1830 : ℝ) :=
  limsup_minimum_div_logb_le_1830_of_paperDepthShellSorts
    (fun _ _ => identityScramble _ _)
    (fun _ _ => identityScramble _ _)
    hs

/-- Finite-window “eventually” form: once `n ≥ 64^7`, every `n` whose `clog 64`
    stays in the Batcher range meets the padded bound. Not an `atTop` claim for
    all large `n` (clog eventually exceeds 603). -/
theorem eventually_minimum_depth_le_1830_logb_of_batcher_window :
    ∀ᶠ n : ℕ in atTop,
      7 ≤ Nat.clog 64 n → Nat.clog 64 n ≤ batcherFitsTotalDepthMax →
        (minimum n : ℝ) ≤ 1830 * Real.logb 2 (n : ℝ) - 58657 := by
  filter_upwards [eventually_ge_atTop (64 ^ 7)] with n hn64 hd7 hmax
  have hn : 1 < n := lt_of_lt_of_le (by decide : 1 < 64 ^ 7) hn64
  exact minimum_depth_le_1830_logb_of_batcher_range hn hd7 hmax

end SortingDepth
