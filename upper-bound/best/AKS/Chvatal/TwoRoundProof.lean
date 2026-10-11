module

public import AKS.Chvatal.TwoRoundHyp
public import AKS.Chvatal.F2Exists

/-! # Proof of `TwoRoundSeparatorExists`

Three cases: `f = 0` (bulk B2 only), `131040 ≤ f < 8.5·10⁹` (the two-round F2 route,
`exists_twoRound_mid`), and `f ≥ 8.5·10⁹` (the one-round Property F route,
`ExistsScrambleSeparator_twoSided_two`). -/

@[expose] public section

namespace Chvatal

theorem twoRoundSeparatorExists : TwoRoundSeparatorExists := by
  intro m n f b hm1 hm2 hn hshape hf hfm
  have hm : 2 ^ 42 ≤ m := hm1.le
  rcases hf with h0 | ⟨hf1, hev⟩
  · subst h0
    obtain ⟨σ1, σ2, ⟨-, hB1⟩, ⟨-, hB2⟩⟩ := ExistsScrambleSeparator_twoSided_B2 hm hn
      (fun _ => True) (by simp)
    exact ⟨σ1, σ2, ⟨hB1, hB2⟩, fun h => absurd h (lt_irrefl 0)⟩
  · by_cases hlt : f < 8500000000
    · obtain ⟨σ1, σ2, hB, hF⟩ := exists_twoRound_mid hm hn hf1 hlt hfm
      exact ⟨σ1, σ2, hB, fun _ => hF⟩
    · push_neg at hlt
      have hm100 : 100 ≤ m := le_trans (by norm_num) hm
      let g : ScrambleGeometry :=
        ScrambleGeometry.ofShape m n b f 64 hm100 hn (by omega) hev hshape.symm.symm
      obtain ⟨σ1, σ2, ⟨hB1, hF1⟩, ⟨hB2, hF2⟩⟩ :=
        ExistsScrambleSeparator_twoSided_two (g := g) (by exact hlt) (by exact hm)
          (deltaF := 128 / 4095) (epsF := eps) le_rfl le_rfl
      exact ⟨σ1, σ2, ⟨hB1, hB2⟩, fun _ => ⟨hF1, hF2⟩⟩

end Chvatal
