module

public import AKS.Kahale.FibonacciBound
public import AKS.Kahale.BinomialPotential

/-! # Exact saturation and an arithmetic witness for the scalar method

These are statements about a relaxation, not about sorting networks. In
particular, `scalarWitness` is an arity compatible with every extracted
binomial inequality; it does not construct a sorting network of that arity.
-/

@[expose] public section

namespace Kahale

theorem deficitPotential_equal_pair (r L a : ℕ) :
    2 * deficitPotential (r + 1) L a =
      2 * (deficitPotential r L a + deficitPotential r L (a + 1)) := by
  rw [deficitPotential]

theorem choose_le_fibonacci (t i : ℕ) : Nat.choose t i ≤ Nat.fib (t + i + 1) := by
  rw [Nat.fib_succ_eq_sum_choose]
  exact Finset.single_le_sum (fun p _ ↦ Nat.zero_le (Nat.choose p.1 p.2))
    (by simp : (t, i) ∈ Finset.antidiagonal (t + i))

theorem prefix_choose_le_fibonacci (d s i : ℕ) (hi : i ≤ s) :
    Nat.choose (d - s) i ≤ Nat.fib (d + 1) := by
  by_cases hs : s ≤ d
  · exact (choose_le_fibonacci (d - s) i).trans (Nat.fib_mono (by omega))
  · have he : d - s = 0 := by omega
    rw [he]
    cases i with
    | zero =>
      simp only [Nat.choose_zero_right]
      exact Nat.fib_pos.mpr (by omega : 0 < d + 1)
    | succ i => simp

/-- An arithmetic witness for all single-term constraints simultaneously. -/
def scalarWitness (d : ℕ) : ℕ := 2 ^ (d + 1) / Nat.fib (d + 1)

theorem scalarWitness_constraints (d s : ℕ) :
    scalarWitness d * Nat.choose (d - s) s ≤ 2 ^ (d + 1) * (s + 1) := by
  calc scalarWitness d * Nat.choose (d - s) s
      ≤ scalarWitness d * Nat.fib (d + 1) :=
        Nat.mul_le_mul_left _ (prefix_choose_le_fibonacci d s s le_rfl)
    _ ≤ 2 ^ (d + 1) := Nat.div_mul_le_self _ _
    _ ≤ 2 ^ (d + 1) * (s + 1) := by simp

theorem fibonacci_le_goldenRatio_pow (d : ℕ) :
    (Nat.fib (d + 1) : ℝ) ≤ Real.goldenRatio ^ d := by
  have h := Real.goldenRatio_mul_fib_succ_add_fib d
  rw [pow_succ] at h
  nlinarith [Nat.cast_nonneg (α := ℝ) (Nat.fib d), Real.goldenRatio_pos]

/-- Integer total mass, but the level populations in the relaxation are fractional. -/
def relaxedArity (d : ℕ) : ℕ := 2 ^ d / ((d + 1) * Nat.fib (d + 1))

def binomialLowMass (t s : ℕ) : ℕ :=
  ∑ i ∈ Finset.range (s + 1), Nat.choose t i

theorem relaxedArity_all_prefix_counts (d s : ℕ) (hs : s ≤ d) :
    relaxedArity d * binomialLowMass (d - s) s ≤ 2 ^ d := by
  have hb : binomialLowMass (d - s) s ≤ (s + 1) * Nat.fib (d + 1) := by
    unfold binomialLowMass
    calc ∑ i ∈ Finset.range (s + 1), Nat.choose (d - s) i
        ≤ ∑ _i ∈ Finset.range (s + 1), Nat.fib (d + 1) := by
          apply Finset.sum_le_sum
          intro i hi
          exact prefix_choose_le_fibonacci d s i (by simpa using Finset.mem_range.mp hi)
      _ = _ := by simp
  calc relaxedArity d * binomialLowMass (d - s) s
      ≤ relaxedArity d * ((s + 1) * Nat.fib (d + 1)) := Nat.mul_le_mul_left _ hb
    _ ≤ relaxedArity d * ((d + 1) * Nat.fib (d + 1)) := by gcongr
    _ ≤ 2 ^ d := Nat.div_mul_le_self _ _

def binomialWeightedMass (t s : ℕ) : ℕ :=
  ∑ i ∈ Finset.range (s + 1), (s + 1 - i) * Nat.choose t i

theorem relaxedArity_full_weighted_constraints (d s : ℕ) (hs : s ≤ d) :
    relaxedArity d * binomialWeightedMass (d - s) s ≤ 2 ^ (d + 1) * (s + 1) := by
  have hb : binomialWeightedMass (d - s) s ≤ (s + 1) * binomialLowMass (d - s) s := by
    unfold binomialWeightedMass binomialLowMass
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    exact Nat.mul_le_mul_right _ (Nat.sub_le _ _)
  calc relaxedArity d * binomialWeightedMass (d - s) s
      ≤ relaxedArity d * ((s + 1) * binomialLowMass (d - s) s) :=
        Nat.mul_le_mul_left _ hb
    _ = (relaxedArity d * binomialLowMass (d - s) s) * (s + 1) := by ring
    _ ≤ 2 ^ d * (s + 1) := Nat.mul_le_mul_right _ (relaxedArity_all_prefix_counts d s hs)
    _ ≤ 2 ^ (d + 1) * (s + 1) := by gcongr <;> omega

end Kahale
