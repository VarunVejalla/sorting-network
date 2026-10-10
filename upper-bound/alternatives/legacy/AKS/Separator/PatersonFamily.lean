module

public import AKS.Separator.PatersonDefs

/-! # Noncomputable families selected from Paterson's existence theorems -/

@[expose] public section

namespace Paterson

/-- A fixed restricted halver at every side arity, all with the ceiling of
Paterson's entropy formula as their depth budget. -/
noncomputable def entropyHalverFamily (a e : ℚ)
    (ha : 0 < a) (ha1 : a ≤ 1) (he : 0 < e) (hehalf : e < 1 / 2) :
    AlphaHalverFamily e a where
  hε_pos := he
  hε_lt_half := hehalf
  hα_pos := ha
  hα_le_one := ha1
  depth := ⌈patersonHalverDepthBound a e⌉₊
  net := fun m => Classical.choose
    (exists_paterson_halver_all_arities (m := m) ha ha1 he hehalf.le)
  isHalver := by
    intro m
    exact (Classical.choose_spec
      (exists_paterson_halver_all_arities (m := m) ha ha1 he hehalf.le)).1
  depth_le := by
    intro m
    exact (Classical.choose_spec
      (exists_paterson_halver_all_arities (m := m) ha ha1 he hehalf.le)).2

/-- A fixed network at every side arity satisfying both first-level contracts
with the jointly proved depth-263 budget. -/
noncomputable def firstLevelNetwork (m : ℕ) : ComparatorNetwork (2 * m) :=
  Classical.choose (exists_paterson_first_level_all_arities m)

theorem firstLevelNetwork_supported (m : ℕ) :
    IsSupportedSeparator (firstLevelNetwork m) m (patersonMu : ℝ) patersonDelta1 := by
  have h := (Classical.choose_spec (exists_paterson_first_level_all_arities m)).1
  simpa [firstLevelNetwork] using restricted_halver_is_supported_separator h

theorem firstLevelNetwork_restricted (m : ℕ) :
    IsEpsilonAlphaHalver (firstLevelNetwork m) patersonDelta1 (2 * patersonMu) :=
  (Classical.choose_spec (exists_paterson_first_level_all_arities m)).1

theorem firstLevelNetwork_good (m : ℕ) :
    IsEpsilonAlphaHalver (firstLevelNetwork m) patersonDelta0 patersonAlpha0 :=
  (Classical.choose_spec (exists_paterson_first_level_all_arities m)).2.1

theorem firstLevelNetwork_depth_le (m : ℕ) :
    (firstLevelNetwork m).depth ≤ 263 :=
  (Classical.choose_spec (exists_paterson_first_level_all_arities m)).2.2

end Paterson
