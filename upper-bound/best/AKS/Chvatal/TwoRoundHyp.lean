module

public import AKS.Chvatal.PackSpec2
public import AKS.Chvatal.FlipSpec

/-! # The two-round separator existence hypothesis

`TwoRoundSeparatorExists` is the (probabilistic) content that the two-round separator tree needs
and that is not yet proved in this package: for every geometry `m = 2f + 64 b` of an ordinary node
(window `2^42 < m ≤ 2^43`, `n ≥ 16`, fringe `f = 0` or `f ≥ 131040` even), there are two
scramblings `σ1, σ2` with two-round Property B (`ε_B = 1/59000000`), and, when `f > 0`,
two-round Property F (`δ_F = 128/4095`, `ε_F = eps`), both for `(σ1, σ2)` and for the flipped
pair.  The bulk part (Property B2 at `m ≥ 2^42`) is `ExistsScrambleSeparator_twoSided_B2`; the
missing part is the joint fringe/B2 existence at `f ≈ 131040`. -/

@[expose] public section

namespace Chvatal

/-- Existence of a two-round scrambling pair for every ordinary node geometry. -/
def TwoRoundSeparatorExists : Prop :=
  ∀ (m n f b : ℕ) (_hm1 : 2 ^ 42 < m) (_hm2 : m ≤ 2 ^ 43) (hn : 16 ≤ n)
    (_hshape : m = 2 * f + 64 * b) (_hf : f = 0 ∨ (131040 ≤ f ∧ Even f))
    (hfm : f ≤ m),
    ∃ σ1 σ2 : Scramble m n,
      (HasPackSemanticPropertyB2 (lt_of_lt_of_le (by norm_num) hn) σ1 σ2 (1 / 59000000) ∧
        HasPackSemanticPropertyB2 (lt_of_lt_of_le (by norm_num) hn)
          (flipScramble σ1) (flipScramble σ2) (1 / 59000000)) ∧
      (0 < f →
        HasPackSemanticPropertyF2 (lt_of_lt_of_le (by norm_num) hn) σ1 σ2 f hfm (128 / 4095) eps ∧
        HasPackSemanticPropertyF2 (lt_of_lt_of_le (by norm_num) hn)
          (flipScramble σ1) (flipScramble σ2) f hfm (128 / 4095) eps)

end Chvatal
