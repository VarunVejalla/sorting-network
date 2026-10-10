# Smaller fringe: a barrier and the required new argument

Research analysis, 2026-10-10. No Lean theorem or improved sorting bound is
claimed. This refines [the two-round plan](chvatal-two-round-separator.md).

**Superseded milestone:** [the stronger fringe obstruction](chvatal-fringe-obstruction.md)
forces at least 43000000 fringe rows for the one-scramble universal contract.
Thus the 131040-row one-round target and the proposed inverse-square error
scale below are impossible. The revised target is a joint two-round F proof.

## 1. Sharper arithmetic is insufficient for the current proof

Write `epsilon = 1/86000000`, `delta = 128/4095`, and `v = j/(f*n)`.
The existing `Lemma62Numerics.xval` equals

`[e^2*(f+2)^2/(4*v*f)]^(2/(epsilon*f))
 * [e/(2*epsilon*v)]^(2/f) * (2*e*v)`.

At `v=delta`, exploratory floating-point roots give:

| Target | Fringe rows f |
| --- | ---: |
| `xval < 1` | approximately 2.496 billion |
| `xval <= 0.32` | approximately 7.280 billion |

The latter rises to approximately 7.667 billion at the proof's looser cap
`v=1/31`. The current sufficient condition is 8.5 billion. Therefore fixing
rounding and sharpening numerical inequalities does not yield the smaller
fringe needed by the two-round bulk construction.

The leading entropy term is approximately `2*ln(f)/(epsilon*f)`.
This majorant needs fringe size on the order of `ln(f)/epsilon` for a
fixed-constant failure bound. The proof already compresses full input profiles
to their portions above the bottom `f/2` rows (`tops`, `topOf`,
`badSetF_card_le`). A new counting argument must improve on that compression,
not simply repeat it.

## 2. A deterministic one-scramble obstruction

Suppose `m >= f+1`. Fix any row scramble and any target output column. In each
of the bottom `f+1` rows, mark the input cell whose scramble image is in that
target column. Close these marks downward in their input columns, so the binary
input is column sorted. If height is counted from the bottom, the closure uses

`j <= 1+2+...+(f+1) = (f+1)*(f+2)/2`

marks: overlaps can only reduce this number. After scrambling, the target has
at least `f+1` marks. Its subsequent column sort therefore leaves at least one
mark outside the bottom `f` rows.

If `n` is sufficiently large that `j <= delta*f*n`, this is a supported rare-rank
threshold. Universal Property F then requires

`epsilon*(f+1)*(f+2)/2 > 1`.

For the current epsilon, this forces `f >= 13114`. The adversarial input is
chosen after the fixed scramble, which is permitted when challenging an
all-input guarantee. It is a binary threshold of a distinct-key permutation,
so it also challenges the semantic rank contract. This is a derived argument,
not a checked Lean theorem.

This lower bound is much smaller than billions. It does not establish that
13114, or any nearby fringe size, is sufficient. It also does not establish
a barrier for several scramble rounds.

## 3. What a new proof should count

The event to certify is actual escaping rank mass, not the stronger auxiliary
half-fringe event whenever it is unnecessary. For selected output columns,
retain only the input cells needed to witness an overflow beyond their bottom
`f` positions, then take the minimal downward closure in the input columns.
This produces a witness with an explicit input mass and escaped mass.

Required modules:

1. **Witness extraction.** Every violation has a reduced monotone witness that
   preserves `escaped >= epsilon*input_mass`, with controlled support and
   heights. Reducing input mass helps this inequality, but deleting cells must
   not erase the escapes.
2. **Witness counting.** Count these reduced objects jointly with output
   columns and their row-hit constraints. Do not multiply independent worst-case
   bounds if they lose the relation between witness complexity and escaped mass.
3. **Probability.** Bound the probability that random row matchings realize
   each witness; sum over ranks without rounding all small ranks to 86000000.
4. **Uniformity.** Show the total failure probability is below the common-witness
   budget for every `n >= 16`, including arbitrarily large `n`.

A possible target is dependence on `epsilon*f^2` rather than `epsilon*f`.
The obstruction above is consistent with that scale, but provides no upper
bound. A claim such as error `O(ln(f)/f^2)` remains a conjectural research lead.
If the one-round counting route fails, use witnesses traced through two rounds;
preservation of an existing F guarantee is different from establishing F across
several rounds.

## 4. Cost implications, including the target 200

At the two-round bulk scale `m≈2^42`, a difficult scheduler template has
`f≈131040`. This is above the deterministic obstruction but far below the
current proof threshold. It is a concrete first test for a new witness lemma.

Even a successful fringe lemma at that size only unlocks the previously
estimated full-sort coefficient around 1400. It does not yield 200.

For a one-scramble pack using the existing bitonic depth budget, the necessary
fringe size 13114 and template ratio `f/m=4095/2^37` require `m` above `2^38`.
Thus that budget must use at least `k=39`, giving coefficient `k*(k+1)/2=780`,
before imposing bulk accuracy. This is a limitation of the specific bitonic
budget and one-round contract, not a sorting-network lower bound.

Reaching 200 therefore needs another structural saving: cheaper local sorting
or repair, improved guarantees across multiple rounds, a less restrictive
scheduler fringe ratio, or fewer scheduler rounds. The new fringe proof is
valuable, but cannot by itself deliver that target within the current budget.

## Recommendation

Work on the reduced escaping-witness lemma first, targeting the explicit
`f≈131040` regime uniformly in `n`. Preserve the four-field NodeSpec interface
initially. Treat 1400 as a conditional milestone; assess 1000 and 200 only after
the local depth and global scheduler can be charged together.
