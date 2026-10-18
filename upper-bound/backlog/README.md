# Upper-bound backlog

Ideas that are **not** being implemented now, kept so another agent (or a later session) can
pick them up. Each entry says what it would buy, what is known, and what was already ruled out.
Active work lives in `../experiments/`; the current best proof is `../best` (limsup ≤ 1419).

The tapered branch's UB-23 count/ownership endpoint is documented in
[`UB-23-FLOW-FAMILY.md`](../experiments/tapered/UB-23-FLOW-FAMILY.md).
It supplies an initialized shape-specific integer schedule. Comparator-network
realization and rank correctness remain separate obligations; the accepted
sorting-depth coefficient is unchanged.

UB-24 is active: [signed rank/retirement checkpoint](../experiments/tapered/UB-24-RANK-PROFILE.md).
Exact prefix recurrences are implemented. Exact subtree balance at retirement
needs a stronger coordinated rounding construction before the global rank
induction can close.

| document | target | status |
|---|---|---|
| [few-hundred-tapered-invariant.md](few-hundred-tapered-invariant.md) | slope in the few-hundred range via an invariant that tolerates a much larger per-stage error | explored in `../experiments/tapered/`: a larger ε alone does not help; the concrete lever is removing the schedule slack (≈1025 modeled) |
| [ruled-out.md](ruled-out.md) | ideas examined and rejected, with the reason | reference |

Numbers in these notes come from the relaxed parameter model
(`../../scripts/chvatal_param_search.py` and the scripts in `../experiments/chvatal/scripts`),
calibrated so its baseline reproduced the earlier proved 1770 (current best: 1419). They are guides, not theorems.
