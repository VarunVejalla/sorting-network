# A moderate-rank tail for the actual column core

2026-10-20. Codex (GPT-6). Fresh-context hand review:
`/root/mass_tail_review`. Local hand lemmas plus outward interval checks;
no Lean or new global coefficient. This is a moderate-cohort interface for
UB-42, not a replacement for UB-34's tiny-rank precision work.

## Rectangular statement

Start with sorted columns on an m-by-n rectangle, n>=2. Apply independent
uniform permutations within rows, then sort each column. Fix eta in (0,1).
For 1<=i<=m write

    g(i) = (i+1) ln(i+1) - i ln i,
    c = ln(2m(n-1)/eta)/n.

For an output-column subset S of relative size p, put X_S equal to the
number of marked cells landing in S. There are at most

    binom(in+n,n) <= exp(n*g(i))

input height profiles of total mass H<=in. For each fixed such profile,
sampling without replacement within a row and independence between rows give

    E exp(theta*X_S) <= (1-p+p*exp(theta))^(in), theta>0.

Let h(p) be binary entropy. For 0<p<1 let x(i,p) be the KL upper root

    i*KL(x/i || p) = g(i)+h(p)+c, x in [ip,i],

clipped at i when the right side exceeds i*ln(1/p). Set x(i,0)=0,
x(i,1)=i. Union over input profiles, S, i and both orientations gives,
with probability at least1-eta, simultaneously for every such input and
every integer fringe width f,

    escape_f <= n * max_{p=s/n, 0<=s<=n} [x(i,p)-fp].

Use <=: clipping does not supply strict inequalities. Empty and full subsets
are included. No union over f is needed, because

    escape_f = max_S (X_S - f*|S|)

is a deterministic identity on the already simultaneous successful event.
The same tail persists through further row permutations (which preserve
fringe mass) and ascending column sorts (which decrease escaping mass).
The existing physical-core relabeling preserves rows and these counts.

## A closed envelope without a p grid

The KL event implies, for any theta>0,

    x(i,p) <= [i ln(1+(exp(theta)-1)p)+g(i)+h(p)+c]/theta.

Choose any tangent point p0 in [0,1], and define

    u = exp(theta)-1,
    v = i*u/(1+u*p0),
    a0 = i ln(1+u*p0) - v*p0.

Concavity of ln(1+up) bounds its contribution by a0+vp. The entropy
identity max_p(h(p)+zp)=ln(1+exp(z)) therefore gives the all-p envelope

    U(i,f;n,m) = [g(i)+c+a0+ln(1+exp(v-f*theta))]/theta.

Every fixed theta,p0 is valid. No optimizer correctness or continuous-grid
coverage is needed. `moderate_tail.py` chooses dyadic parameters numerically,
then evaluates this expression with outward `mpmath.iv` intervals. The upper
dyadic endpoint is converted to an exact Fraction before taking an integer
floor. These are numerical interval checks, not Lean certificates.

## Arbitrary arities without a large padding row

Existing baseline padding needs m*n<=a<=(m+1)*n. At small row exponents this
cannot automatically be arranged for every a while keeping the column-sort
depth fixed. Do not omit this condition.

A different candidate layout has centered ragged columns. For row ceiling
2^q choose n=ceil(a/2^q), L=floor(a/n), and r=a-Ln. There are L full rows
and r extra cells at one middle row. Each column has L or L+1<=2^q cells;
each column sort costs at most S(q). Row permutations preserve each full or
partial row. Let b be the smaller number of full rows on the two sides of
the partial row, and take f<=b.

After the initial sort, a marked extra cell requires at least b+1 marks in
its column, for either orientation. Hence the extra marked population is

    Q <= min(r, floor(H/(b+1))).

Deleting the partial row leaves sorted rectangular profiles on L-by-n with
mass at most H. Apply the preceding bound with i=min(L,ceil(H/n)). Restoring
Q marks changes escape by at most Q. Therefore

    escape_f <= n*U(i,f;n,L) + min(r,floor(H/(b+1))).

Charge Q once. Subsequent row permutations and sorts preserve/improve this
same fringe region, even if the partial row's population changes. A requested
native fringe of size h can use f=floor(h/n); unused partial fringe cells
only improve the bound. This defines a new ragged core, not a free property
of the current padded provider. Its physical embeddings remain to implement.

## Ragged bulk comparison

Compare with the regular L-by-n three-sort core on the same initial full-row
input and the same full-row permutations. Sorting a ragged column and
deleting its extra cell differs from sorting the retained input by at most
one Boolean bit. Column sorting and permutations are Hamming nonexpansive.
The three sorts thus give final retained-word distance at most3r.

For input mass H and native output prefix p, deletion gives H'=H-q and
p'=p-e with q,e in [0,r]. Thus

    min(H,p)-min(H',p') <= max(q,e) <= r.

Extra output marks inside the prefix only help. An all-cut regular deficit
bound E consequently gives ragged deficit at most E+4r, per direction
(8r if a later interface sums both). The same physical row permutations
must be used in the coupling. This is an independently reviewed hand lemma;
no certified uniform bulk constants for these ragged dimensions are claimed.

## What the local check does and does not close

At the saved coarse trace's t4 node(2,4), minority mass1310 and fringe1792,
the centered ragged layout has n130, L4088, f13, Q0. The interval-evaluated
tail gives at most530 escapes, excluding the trace's1099. At t5 node(3,17),
mass1099 and fringe3584, it gives at most132, excluding678. See
`moderate-tail.out` and the script. These bounds concern the new layout's
common successful witness; they do not retroactively change the old oracle.

The depth hypothesis remains3*S(12)=234 at the5/4 stage rate, coefficient
292.5, conditional on the whole construction. Exact local sorts up to2^21
wires cost231 and fit that stage budget. This is a hypothesis, not a theorem.

Open gates: a capacity-compatible global invariant using the full tail
curve; a sufficiently strong tiny-rank guarantee from the same fixed core;
simultaneous local contracts for every sender geometry with a certified
ragged bulk bound;
initial root treatment; exact terminal purity; and fresh review of the
complete construction before Lean. The moderate tail alone can allow a
single rare key to escape, so it cannot be silently used as the tiny-rank
termination guarantee.

## Choose a fixed witness per sender geometry

The local tail statement is already simultaneous over every binary input
profile, output-column subset, rank `i`, fringe width, and both orientations
for one sampled core. That quantifier order changes how witnesses should be
assembled globally. Let `theta` record one finite local geometry (wire
arity, ragged mask, and provider parameters), and let `Good(theta)` be the
conjunction of all local postconditions required at that geometry. If the
local probability calculation proves `Pr(Good(theta))>0`, then a deterministic
core `C_theta` satisfying every input to that geometry exists.

Choose such a core separately for each geometry, and use it at every sender
with that geometry. The global proof uses the universal local postcondition;
it does not require one random sample to succeed simultaneously at distinct
sender occurrences or at distinct geometries. For each fixed input size the
schedule has finitely many senders, and over all sizes the family of finite
integer geometries is countable. Thus there is no union-bound factor for the
number of scheduled senders or stages. In Lean, the local existence theorem
can be turned into a provider function by choice. Its depth bound must be
uniform in `theta`, as in the proposed fixed 13-bit core.

The probability budget is needed only inside `Good(theta)`: union the failures
of the bulk, fringe, both directions, and any other simultaneous local
clauses for that one geometry, with total strictly below one. A fixed local
failure budget such as `eta=1/1000` is therefore appropriate across
geometries; the moderate-tail entropy term is
`ln(2*m*(n-1)/eta)/n`, with no `N` or stage-count factor. For `m=8192`,
`n=3832`, the conditional minimum provider dimension, and `eta=1/1000`, this
term is about `0.00649`. It still must fit the local spill allowance and its
associated tail bound; this argument does not prove that numerical gate.

This removes the need for the proposed `O(ln ln N)` exact-sort cleanup of
small senders, provided the fixed-eta local provider works for every geometry
that occurs. The remaining local task is to prove the simultaneous provider
contract at the minimum dimensions, not to sum random failure probabilities
over sender occurrences. Tiny-rank control and the global rank-transfer
induction remain separate obligations.

### Audit of the proposed small-sender terminal cleanup (2026-10-26)

I counted actual provider-using sender occurrences, expanding interned
flow-state multiplicities, for `FlowDAG(d, scale=8192, p=Par(3,3,2))`.
`botRise` is excluded because it bypasses the local separator, and the
zero-up `topDesc` is excluded as well. The branching factor is `k=8`, so
`N=8192*8^d`; the proposed cleanup cutoff is `a < 8192*(ln N)^2`. The exact
flow has `3d-14` stages. `d2_small_sender_audit.py` checks multiplicities
against explicit address enumeration at small depths. Its finite results are:

| `d` | stages | minimum provider columns `ceil(a/8192)` | cutoff | first small-sender stage | last | occupied stages |
|---:|---:|---:|---:|---:|---:|---:|
| 16 | 34 | 3,983 | 14,645,376 | none | — | 0 |
| 24 | 58 | 3,983 | 28,436,669 | none | — | 0 |
| 32 | 82 | 3,983 | 46,762,084 | 46 | 80 | 7 |
| 48 | 130 | 3,983 | 97,015,286 | 65 | 128 | 22 |
| 64 | 178 | 3,983 | 165,404,983 | 89 | 176 | 45 |
| 96 | 274 | 3,983 | 356,593,857 | 137 | 272 | 92 |
| 128 | 370 | 3,983 | 620,328,707 | 185 | 368 | 154 |

The minimum provider columns over depths 6 through 128 are 3,983 or more
(depth 6 has 4,032; depths 7 and 8 have 4,004 and 3,990). Below-cutoff
ordinary senders do persist across many late stages at larger depths, so
exact-sorting them is not a short terminal cleanup. But their finite minimum
column count is already above the conditional F2 threshold `n>=3832` in
`RAGGED-ALL-SENDERS-GATE.md`; this is evidence for the fixed-eta per-geometry
provider route, not evidence against it. The all-depth dimension theorem and
the small-dimension spill checks remain to be completed.

Run `python d2_small_sender_audit.py --check-small` to verify the DAG
multiplicities against explicit address enumeration before the default depth
audit. This audit is about the unnecessary exact-cleanup alternative; it does
not establish the provider theorem or the global rank recurrence.
