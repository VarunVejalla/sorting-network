# The positional height barrier

## Result

The positional gap in the previous height-histogram witness can be closed.
There is an explicit comparator schedule on

\[
N_d=\left\lfloor\frac{2^d}{(d+1)F_{d+1}}\right\rfloor
\]

wires with `d` parallel stages whose actual scalar certificate heights satisfy

\[
h_{d-s}(i)\ge s+1\quad\text{whenever }i\ge2^{s+1},
\qquad 0\le s\le d.
\]

The same schedule works for all prefixes. It has
`d/log_2(N_d) -> 3.270559454...`. Thus the positional conditions used in our
current zero-certificate argument cannot force a larger leading coefficient.
This is a comparator schedule satisfying necessary height conditions, not a
construction of a sorting network or a proof of approximate selection.

The asymptotic rate and histogram bound are derived in
[the preceding analysis](kahale-method-barrier.md). The construction below
adds positions to that integral histogram evolution.

## Explicit schedule

Start with height zero on every wire. Maintain heights nondecreasing with
wire position, so each occupied height forms a contiguous block.

For a block of height `a`, starting at position `b`, with `m` wires, put
`u = ceil(m/2)` and compare

```text
(b+k, b+u+k),       0 <= k < floor(m/2).
```

Every pair has its smaller index first, and all pairs in the stage are disjoint.
Since both inputs have equal height `a`, the repository's actual `heightStep`
leaves height `a` at the smaller index and puts height `a+1` at the larger index.
For odd `m`, the unpaired wire is the last wire of the lower segment and stays
at height `a`. The block becomes

```text
height a on its first ceil(m/2) wires;
height a+1 on its last floor(m/2) wires.
```

Each block is internally sorted. If two old block heights are `a < c`, the
first block's new heights are at most `a+1 <= c`, while the second block's new
heights are at least `c`. Thus all heights remain sorted. Merge adjacent equal
blocks and repeat.

This schedule is determined entirely by the initial wire count and the stage
number. It does not inspect the values being compared.

## From histogram counts to positions

This is exactly the integral equal-height pairing process already analyzed.
Let `C_t(s)` count heights at most `s`. Its rounding bound gives, at `t=d-s`,

\[
C_{d-s}(s)\le N_d\,2^{-(d-s)}
 \sum_{j=0}^s\binom{d-s}{j}+s+1
 \le2^s+s+1\le2^{s+1}.
\]

Because the height profile is sorted, these wires occupy precisely the first
`C_(d-s)(s)` positions. All indices at least `2^(s+1)` therefore have height
at least `s+1`, as required.

There is no positional obstruction for this particular necessary condition.
The schedule also carries actual zero certificates, by the existing
`certificateHeights_correct` theorem. What is missing is sufficient control
of certificate sizes and families to establish selection.

## A concrete separation from sorting

The construction need not sort. At `d=40`, the prescribed arity is `161`.
The script finds an explicit Boolean input whose output has a `1` on wire
`85` followed by a `0` on wire `86` (zero-based indices). The network
nevertheless satisfies all of the positional height conditions above.

Reproduce the schedule, positional checks, and counterexample with

```sh
python scripts/kahale_positional_barrier.py 40 --explore-depth 40 --trials 1 --seed 0
```

The command prints the entire input and output, not merely a failure flag.
The witness is a computation over the explicit Boolean comparator execution;
it is not a kernel-checked sorting counterexample.

For large arities, the script stores contiguous blocks and comparator interval
families instead of expanding every wire. Thus it checks the positional
construction at depths `64,128,256,512,1024`, including arities with hundreds
of binary digits, with exact integer arithmetic. These are finite checks;
the argument above supplies the general mathematical construction.

## Formalization status

[`AKS/Kahale/PositionalBarrier.lean`](../lower-bound/experiments/AKS/Kahale/PositionalBarrier.lean)
kernel-checks two ingredients:

- `splitBlockProfile_monotone`: incrementing the upper segment of every
  constant-height block preserves monotonicity;
- `sorted_height_count_implies_position`: for a monotone height profile,
  a low-height cardinality bound implies the positional requirement.

The existing `MethodBarrier` module proves the finite binomial/Fibonacci
estimates. The full block comparator construction, integral rounding recurrence,
and asymptotic witness limit remain mathematical derivations in the notes,
rather than one complete Lean existence theorem. No improved sorting lower
bound or sorting upper bound is claimed.

## What to investigate next

**Follow-up:** [the certificate-family investigation](kahale-certificate-families.md)
extracts disjoint size-77 zero and size-65 one certificates for the central
inversion and formalizes the family-level sorting condition.

Counting heights, integrality, and these zero-certificate boundary positions
all admit the existing exponential rate. A stronger argument must impose
additional constraints.

The most concrete next target is **actual certificate families across multiple
rank thresholds**. Sorting requires output `i` to represent the Boolean
threshold with minimum zero-certificate size `i+1` and minimum one-certificate
size `n-i`. Our scalar height only bounds the size of one available certificate
from above; a large height does not exclude a smaller certificate.

Investigate where the explicit witness loses this threshold structure:
certificate unions can overlap, alternative certificates can be much smaller,
and certificates for different outputs may have incompatible requirements.
This gives a concrete comparator schedule against which to try a new invariant.
Merely imposing the zero-height positional condition again cannot exclude it.
