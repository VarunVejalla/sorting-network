module

public import AKS.Separator.PatersonFamily
public import AKS.Separator.FromHalver

/-! # Five-level network underlying Paterson's separator -/

@[expose] public section

namespace Paterson

noncomputable def level2Family : AlphaHalverFamily patersonDelta2 (4 * patersonMu) :=
  entropyHalverFamily (4 * patersonMu) patersonDelta2
    (by norm_num [patersonMu]) (by norm_num [patersonMu])
    (by norm_num [patersonDelta2]) (by norm_num [patersonDelta2])

noncomputable def level3Family : AlphaHalverFamily patersonDelta3 (8 * patersonMu) :=
  entropyHalverFamily (8 * patersonMu) patersonDelta3
    (by norm_num [patersonMu]) (by norm_num [patersonMu])
    (by norm_num [patersonDelta3]) (by norm_num [patersonDelta3])

noncomputable def level4Family : AlphaHalverFamily patersonDelta4 (16 * patersonMu) :=
  entropyHalverFamily (16 * patersonMu) patersonDelta4
    (by norm_num [patersonMu]) (by norm_num [patersonMu])
    (by norm_num [patersonDelta4]) (by norm_num [patersonDelta4])

noncomputable def level5Family : AlphaHalverFamily patersonDelta5 (32 * patersonMu) :=
  entropyHalverFamily (32 * patersonMu) patersonDelta5
    (by norm_num [patersonMu]) (by norm_num [patersonMu])
    (by norm_num [patersonDelta5]) (by norm_num [patersonDelta5])

/-- Level zero carries both first-level contracts. Subsequent levels use
supported fractions `4μ`, `8μ`, `16μ`, and `32μ`. -/
noncomputable def stageNetwork (level m : ℕ) : ComparatorNetwork (2 * m) :=
  if level = 0 then firstLevelNetwork m
  else if level = 1 then level2Family.net m
  else if level = 2 then level3Family.net m
  else if level = 3 then level4Family.net m
  else if level = 4 then level5Family.net m
  else ⟨[]⟩

def stageDepth (level : ℕ) : ℕ :=
  if level = 0 then 263
  else if level = 1 then 155
  else if level = 2 then 167
  else if level = 3 then 187
  else if level = 4 then 217
  else 0

/-- The fraction of all local wires whose extreme-value cohorts are covered. -/
noncomputable def stageSupport (level : ℕ) : ℝ :=
  if level = 0 then patersonMu
  else if level = 1 then ((4 * patersonMu : ℚ) : ℝ) / 2
  else if level = 2 then ((8 * patersonMu : ℚ) : ℝ) / 2
  else if level = 3 then ((16 * patersonMu : ℚ) : ℝ) / 2
  else if level = 4 then ((32 * patersonMu : ℚ) : ℝ) / 2
  else 0

def stageError (level : ℕ) : ℝ :=
  if level = 0 then patersonDelta1
  else if level = 1 then patersonDelta2
  else if level = 2 then patersonDelta3
  else if level = 3 then patersonDelta4
  else if level = 4 then patersonDelta5
  else 0

def stageAlpha (level : ℕ) : ℚ :=
  if level = 0 then 2 * patersonMu
  else if level = 1 then 4 * patersonMu
  else if level = 2 then 8 * patersonMu
  else if level = 3 then 16 * patersonMu
  else if level = 4 then 32 * patersonMu
  else 0

def stageErrorQ (level : ℕ) : ℚ :=
  if level = 0 then patersonDelta1
  else if level = 1 then patersonDelta2
  else if level = 2 then patersonDelta3
  else if level = 3 then patersonDelta4
  else if level = 4 then patersonDelta5
  else 0

theorem stageNetwork_halver (level m : ℕ) (hle : level < 5) :
    IsEpsilonAlphaHalver (stageNetwork level m)
      (stageErrorQ level) (stageAlpha level) := by
  interval_cases level
  · simpa [stageNetwork, stageErrorQ, stageAlpha] using firstLevelNetwork_restricted m
  · simpa [stageNetwork, stageErrorQ, stageAlpha] using level2Family.isHalver m
  · simpa [stageNetwork, stageErrorQ, stageAlpha] using level3Family.isHalver m
  · simpa [stageNetwork, stageErrorQ, stageAlpha] using level4Family.isHalver m
  · simpa [stageNetwork, stageErrorQ, stageAlpha] using level5Family.isHalver m

theorem stageAlpha_eq (level : ℕ) (hle : level < 5) :
    stageAlpha level = 2 ^ (level + 1) * patersonMu := by
  interval_cases level <;> norm_num [stageAlpha]

theorem stageErrorQ_nonneg (level : ℕ) (hle : level < 5) :
    0 ≤ stageErrorQ level := by
  interval_cases level <;> norm_num [stageErrorQ, patersonDelta1, patersonDelta2,
    patersonDelta3, patersonDelta4, patersonDelta5]

theorem stageError_eq (level : ℕ) :
    stageError level = (stageErrorQ level : ℝ) := by
  unfold stageError stageErrorQ
  split_ifs <;> simp

/-- Every selected local stage meets its advertised supported-range contract.
The theorem is intentionally local: composing the stages still requires the
Paterson stranger-count induction. -/
theorem stageNetwork_supported (level m : ℕ) (hle : level < 5) :
    IsSupportedSeparator (stageNetwork level m) m
      (stageSupport level) (stageError level) := by
  interval_cases level
  · simpa [stageNetwork, stageSupport, stageError] using firstLevelNetwork_supported m
  · simpa [stageNetwork, stageSupport, stageError] using
      (restricted_halver_is_supported_separator (level2Family.isHalver m))
  · simpa [stageNetwork, stageSupport, stageError] using
      (restricted_halver_is_supported_separator (level3Family.isHalver m))
  · simpa [stageNetwork, stageSupport, stageError] using
      (restricted_halver_is_supported_separator (level4Family.isHalver m))
  · simpa [stageNetwork, stageSupport, stageError] using
      (restricted_halver_is_supported_separator (level5Family.isHalver m))

theorem stageNetwork_depth_le (level m : ℕ) :
    (stageNetwork level m).depth ≤ stageDepth level := by
  by_cases h0 : level = 0
  · subst level
    simpa [stageNetwork, stageDepth] using firstLevelNetwork_depth_le m
  by_cases h1 : level = 1
  · subst level
    have hbudget : level2Family.depth ≤ 155 :=
      Nat.ceil_le.mpr depth_bound_level2
    simpa [stageNetwork, stageDepth] using
      (level2Family.depth_le m).trans hbudget
  by_cases h2 : level = 2
  · subst level
    have hbudget : level3Family.depth ≤ 167 :=
      Nat.ceil_le.mpr depth_bound_level3
    simpa [stageNetwork, stageDepth] using
      (level3Family.depth_le m).trans hbudget
  by_cases h3 : level = 3
  · subst level
    have hbudget : level4Family.depth ≤ 187 :=
      Nat.ceil_le.mpr depth_bound_level4
    simpa [stageNetwork, stageDepth] using
      (level4Family.depth_le m).trans hbudget
  by_cases h4 : level = 4
  · subst level
    have hbudget : level5Family.depth ≤ 217 :=
      Nat.ceil_le.mpr depth_bound_level5
    simpa [stageNetwork, stageDepth] using
      (level5Family.depth_le m).trans hbudget
  simp [stageNetwork, stageDepth, h0, h1, h2, h3, h4, ComparatorNetwork.depth]

/-- The five recursively halved levels, with different halver families. -/
noncomputable def separatorNetwork (n : ℕ) : ComparatorNetwork n :=
  ⟨(List.range 5).flatMap fun level =>
    (halverAtLevel n (stageNetwork level) level).comparators⟩

private theorem stageList_depth_le (n : ℕ) (levels : List ℕ) :
    (⟨levels.flatMap fun level =>
      (halverAtLevel n (stageNetwork level) level).comparators⟩ :
        ComparatorNetwork n).depth ≤
      (levels.map stageDepth).sum := by
  induction levels with
  | nil => simp [ComparatorNetwork.depth]
  | cons level levels ih =>
    simp only [List.flatMap_cons, List.map_cons, List.sum_cons]
    have happ := depth_append
      (halverAtLevel n (stageNetwork level) level)
      (⟨levels.flatMap fun j =>
        (halverAtLevel n (stageNetwork j) j).comparators⟩ : ComparatorNetwork n)
    have hlevel := halverAtLevel_depth_le n (stageNetwork level)
      (stageNetwork_depth_le level) level
    exact happ.trans (add_le_add hlevel ih)

/-- The actual five-level comparator network has depth at most 989. This
statement is independent of its still-open Paterson separator correctness. -/
theorem separatorNetwork_depth_le (n : ℕ) :
    (separatorNetwork n).depth ≤ 989 := by
  have h := stageList_depth_le n (List.range 5)
  change (separatorNetwork n).depth ≤ (List.range 5 |>.map stageDepth).sum at h
  exact h

end Paterson
