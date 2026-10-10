module

public import AKS.Separator.PatersonPrefix

/-! # The proved Paterson separator certificate

This combines the supported-range correctness theorem with the depth bound
for the same five-level network. It is a local certificate for arities
divisible by 32, not a sorting-network theorem or an arbitrary-arity separator.
The contract and level errors follow Paterson (1990); see
`docs/paterson-interface.md` for the source and remaining global obligations.
-/

@[expose] public section

namespace Paterson

/-- The five-stage error is exactly the sum used in the interior tail budget. -/
theorem prefixError_five : prefixError 5 = (patersonTailError : ℝ) := by
  norm_num [prefixError, stageError, List.range_succ, patersonTailError]
  ring

/-- The same selected network has both the supported-range guarantee and the
certified depth bound. The support is `μ = 1/50`, while each fringe has `n/32`
wires; these are different quantities. -/
theorem separatorNetwork_certificate_of_dvd32 (n : ℕ) (h32 : 32 ∣ n) :
    IsSupportedSeparator (separatorNetwork n) (n / 32)
      (patersonMu : ℝ) (patersonTailError : ℝ) ∧
    (separatorNetwork n).depth ≤ 989 := by
  refine ⟨?_, separatorNetwork_depth_le n⟩
  simpa only [prefixError_five] using separatorNetwork_supported_of_dvd32 n h32

end Paterson
