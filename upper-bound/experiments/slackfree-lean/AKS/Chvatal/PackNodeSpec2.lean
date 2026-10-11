module

public import AKS.Chvatal.KernelSetup
public import AKS.Chvatal.PackSpec2

/-! # Node guarantee of the two-round separator

`packNodeSpec2` is the two-round analogue of `packNodeSpec`: the same `NodeSpec` parameters for
`physicalPack2Net`.  Both two-round Property B (`HasPackSemanticPropertyB2`) and two-round
Property F (`HasPackSemanticPropertyF2`, for `(σ1,σ2)` and the flipped pair) are hypotheses. -/

@[expose] public section

namespace Chvatal

theorem specJmax_le_real (π j : ℕ) (hj : j ≤ specJmax π) :
    (j : ℝ) ≤ (128 / 4095 : ℝ) * ((π : ℝ) / 2) :=
  (Nat.cast_le.2 hj).trans (Nat.floor_le (by positivity))

theorem packNodeSpec2 {m n f b : ℕ} (hn : 0 < n) (σ1 σ2 : Scramble m n)
    (hmfb : m = 2 * f + 64 * b) (hfm : f ≤ m) {epsB EB : ℝ}
    (hEB : EB = epsB / 2 * ((m * n : ℕ) : ℝ))
    (hB1 : HasPackSemanticPropertyB2 hn σ1 σ2 epsB)
    (hB2 : HasPackSemanticPropertyB2 hn (flipScramble σ1) (flipScramble σ2) epsB)
    (hF2 : 0 < f →
      HasPackSemanticPropertyF2 hn σ1 σ2 f hfm (128 / 4095) eps ∧
      HasPackSemanticPropertyF2 hn (flipScramble σ1) (flipScramble σ2) f hfm (128 / 4095) eps) :
    NodeSpec (m * n) (2 * f * n) (b * n) (physicalPack2Net m n hn σ1 σ2) EB
      (specJmax (2 * f * n)) eps := by
  have hFF : HasPackSemanticPropertyF2 hn σ1 σ2 f hfm (128 / 4095) eps ∧
      HasPackSemanticPropertyF2 hn (flipScramble σ1) (flipScramble σ2) f hfm (128 / 4095) eps := by
    rcases Nat.eq_zero_or_pos f with h0 | h0
    · subst h0
      exact ⟨fun v j hj hjd => by simp at hjd; omega, fun v j hj hjd => by simp at hjd; omega⟩
    · exact hF2 h0
  have hH := packSpec2_high hn σ1 σ2 hmfb hfm hB1 hFF.1
  have hL := packSpec2_low hn σ1 σ2 hmfb hfm hB2 hFF.2
  have hconv : ∀ j : ℕ, j ≤ specJmax (2 * f * n) → (j : ℝ) ≤ (128 / 4095 : ℝ) * (f * n) := by
    intro j hj
    have h := specJmax_le_real _ j hj
    have e : ((2 * f * n : ℕ) : ℝ) / 2 = f * n := by push_cast; ring
    rwa [e] at h
  have hEB' : epsB / 2 * ((m : ℝ) * n) = EB := by rw [hEB]; push_cast; ring
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x p hp hpa
    exact (hH.1 x p hp hpa).trans (le_of_eq hEB')
  · intro x p hp hpa
    exact (hL.1 x p hp hpa).trans (le_of_eq hEB')
  · intro x j hj hjJ hja
    exact hH.2 x j hj (hconv j hjJ) hja
  · intro x j hj hjJ hja
    exact hL.2 x j hj (hconv j hjJ)

/-- Depth of the two-round node network for `m ≤ 2^k`: `3 k (k+1) / 2`. -/
theorem pack2_depth_le (m n : ℕ) (hn : 0 < n) (σ1 σ2 : Scramble m n) (k : ℕ) (hm : m ≤ 2 ^ k) :
    (physicalPack2Net m n hn σ1 σ2).depth ≤ 3 * (k * (k + 1)) / 2 := by
  refine (physicalPack2Net_depth_le_budget m n hn σ1 σ2).trans ?_
  have h1 : Nat.clog 2 m ≤ k := by
    have := Nat.clog_mono_right 2 hm
    rwa [Nat.clog_pow 2 k (by norm_num)] at this
  have h2 := bitonicDepthBudget_mono h1
  have := bitonicDepthBudget_double k
  omega

end Chvatal
