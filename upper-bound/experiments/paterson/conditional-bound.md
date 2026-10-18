# Conditional global bound

This is an informal conditional theorem derived from the existing recursion.
Arithmetic instances are checked by `audit_budget.py`; the generalized
network construction and adapter contracts are not formalized here.

## Cost theorem

Suppose an oblivious forest construction preserves the current global rank
and allocation invariants, and has these uniform bounds:

- Each comparison phase has depth at most `s` and reduces comparison fuel by one.
- Each root split/rebuild has depth at most `r`, reduces the binary scale `k` by one, and preserves fuel. Its two child constructions run in parallel.
- Terminal cases have depth at most a fixed `b`.
- Initial comparison fuel is `S(k)`.
- The final fixed rank-arrangement correction has depth at most `k`.

Then a correct sorter on `2^k` inputs has depth at most

    s S(k) + (r + 1) k + b.

Proof: induct on `k + fuel`. The potential `s*fuel + r*k + b`
bounds terminal depth. A comparison spends `s` and lowers fuel; a split spends
`r` and lowers `k` in each child. Depth of their parallel composition is the
maximum child depth. Append the rank correction of depth `k`.

For a stage certificate `S(k) <= q k + c`, restriction from the next power
of two gives, for every positive `n`,

    D(n) <= (q s + r + 1) ceil(log_2 n) + s c + b.

Thus, provided the stated correctness hypotheses hold,

    limsup D(n)/log_2 n <= q s + r + 1.

Restriction and the logarithmic limit passage are already used in the
[existing bound](../../alternatives/legacy/AKS/Bounds/PatersonTight.lean).
This derivation does not assert that arbitrary networks of depths `s` and `r`
satisfy the hypotheses.

## Certified stages and dependence on error

The current fuel proof shrinks `capacity * A^k` by `nu` per comparison phase.
For positive integers `u,v`, the rational certificate

    (2 A)^v nu^u <= 1

allows `S(k) = u ceil(k/v)` when the initial capacity is at most `2^k`
and minimum capacity is greater than one. Indeed
`(2 A)^k nu^S(k) <= 1` follows by comparison with the next multiple of `v`.
The useful bound is

    S(k) <= (u/v) k + u(v-1)/v.

Hence

    C = (u/v) s + r + 1,
    additive term = s u(v-1)/v + b.

The limiting real stage ratio is `log(2 A)/(-log nu)` (either consistent
logarithm base). With the current parameters it is approximately 6.493026;
the proved rational certificate uses `u=13,v=2`, giving 6.5.
Eliminating the rational rounding alone saves only about `0.006974*s`.

The errors affect `C` through feasible geometry and shrink factor, rather
than through an independent additive error charge. For full-bag tail error
`e`, first split error `beta`, and a certified fresh-stranger cost `F`, the
interior conditions include

    4 delta^2 A^2 < 1,
    nu = 2 lambda A + (1-lambda)/(2 A),
    2 A^2 delta^2 + e < nu A delta,
    2 mu delta A^2 + 2 mu delta A^2/(1-4 delta^2 A^2)
      + 1/(8 A^2-2) + mu + beta/2 < nu mu A,
    2 mu delta A + F + rho/M <= nu mu.

Also `A>1`, `0<nu,delta,lambda<1`, and `0<mu<support`.
Here `rho` is the rounding allowance and `M` the minimum capacity.
The existing conservative fresh-cost certificate is

    F = (1-alpha+beta)/(2 A) + e mu/A.

Consequently any feasible replacement must have `nu` exceeding the tail
and first-stranger lower bounds implied above, while still respecting the
capacity identity and fringe/routing constraints. Increasing error generally
forces weaker shrink or changed geometry; reducing error may permit a smaller
`nu` and hence fewer stages.

These scalar inequalities are necessary parts of the present proof interface,
not a sufficient generic construction theorem. Allocation, padded support,
fresh-cohort availability, phase windows, and the final input-independent rank
arrangement must still be proved. Many existing modules specialize `fastParams`.

## Root error dependence

The present proof uses root ceiling `R = M/nu^2` and vanishing deep strangers
from

    mu delta^5 R A^6 < 1,     delta A <= 1.

The integer stranger count is then zero at and below the required level-six
boundary. The repair region includes a reserve plus shallow-bag capacities;
the implementation proves its total size is below `2^33`. A bitonic repair
therefore has `r=561`. Changing `M`, `nu`, `A`, or `delta` requires rechecking
both purity and this region-size bound. Smaller rounding thresholds can help
repair cost, but they are constrained by the rounded first-stranger and
allocation inequalities.

A different repair may use a different proof of purity or bin control. Its
cost `r` is an independent certified input to the cost theorem once those
postconditions have been established. It is not justified by region size alone.

## Numerical targets with the current stage certificate

| Separator depth `s` | Repair depth `r` | Conditional coefficient `6.5 s + r + 1` |
|---:|---:|---:|
| 989 | 561 | 6990.5 (existing completed proof) |
| 100 | 100 | 751 |
| 60 | 80 | 471 |
| 30 | 4 | 200 |
| 24 | 43 | 200 |

All rows except the first are budgets, not existence results.
With the current repair, even a zero-cost separator leaves coefficient 562.
With zero-cost repair, coefficient 200 requires integer separator depth at
most 30. For coefficient below 1000 the condition is `6.5 s + r < 999`;
retaining `r=561` would require `s <= 67`.

Thus moderate improvements in the stage ratio cannot deliver 200. Within
this scheduler, that target needs a radical reduction of both primitive and
repair cost, or a different accounting/scheduler that amortizes those costs.
