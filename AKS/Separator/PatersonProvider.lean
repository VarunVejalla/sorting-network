module

public import AKS.Separator.Provider
public import AKS.Halver.PatersonFull

/-! # A Paterson provider for the established bag scheduler

This first complete route uses full-support Paterson halvers in the
prefix-doubling separator. It is distinct from the tighter five-level
supported separator and rounded Paterson bag construction.
-/

@[expose] public section

namespace Paterson

theorem provider_error_le {δ : ℚ} (hd : 1 / 63 ≤ δ) :
    (89 / 35000 : ℚ) ≤ (89 / 5000) / ↑(sepTotalLayers δ) := by
  have ht : sepTotalLayers δ ≤ 7 := by
    have h := numSepLevels_antitone (by norm_num : (0 : ℚ) < 1 / 63) hd
    have hb : numSepLevels (1 / 63) = 5 := by decide +kernel
    unfold sepTotalLayers
    omega
  have hp := sepTotalLayers_pos δ
  apply (le_div_iff₀ (Nat.cast_pos.mpr hp)).mpr
  have htQ : (sepTotalLayers δ : ℚ) ≤ 7 := by exact_mod_cast ht
  nlinarith

noncomputable def providerFamily (δ : ℚ) (hd : 1 / 63 ≤ δ) :
    HalverFamily ((89 / 5000) / ↑(sepTotalLayers δ)) where
  depth := 5490
  net := fullFamily.net
  isHalver m := (fullFamily.isHalver m).mono (Rat.cast_le.mpr (provider_error_le hd))
  depth_le := fullFamily.depth_le

noncomputable def providerNet (δ : ℚ) (hδ : 0 < δ) (m : ℕ) :
    ComparatorNetwork (2 * m) :=
  if hd : 1 / 63 ≤ δ then
    separatorNet δ (89 / 5000) hδ (by norm_num) m (providerFamily δ hd)
  else separatorNet δ (89 / 5000) hδ (by norm_num) m

noncomputable def bagProvider : BagSeparators (1 / 63) (89 / 5000) where
  depth := 71370
  net := providerNet
  isSeparator δ hδ hl m := by
    unfold providerNet
    split
    · exact separatorNet_isSeparator _ _ _ _ hl _ (providerFamily _ _)
    · exact separatorNet_isSeparator _ _ _ _ hl _
  isHalver δ hδ m := by
    unfold providerNet
    split
    · exact separatorNet_isHalver _ _ _ _ _ (providerFamily _ _)
    · exact separatorNet_isHalver _ _ _ _ _
  depth_le δ hδ hd m := by
    unfold providerNet
    rw [dif_pos hd]
    apply (separatorNet_depth_le _ _ _ _ _ (providerFamily _ hd)).trans
    have h := numSepLevels_antitone (by norm_num : (0 : ℚ) < 1 / 63) hd
    have hb : numSepLevels (1 / 63) = 5 := by decide +kernel
    change (2 * (numSepLevels δ + 1) + 1) * 5490 ≤ 71370
    omega

end Paterson
