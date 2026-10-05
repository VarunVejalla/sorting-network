# A potential depending on remaining depth

## Outcome

The first finite experiment is encouraging about retaining overlap information,
but **does not improve the asymptotic lower bound 3.270559...**.

On five wires, per-wire exact minimum certificate sizes lose one layer of
remaining-depth information. Adding the exact union costs for every pair of
wires removes that loss in this exhaustive finite catalogue. The universal
numerical union-coupling inequality alone prunes possible short suffixes, but
does not improve the initial depth bound in these experiments.

These are Python enumeration results, not Lean theorems or evidence of an
improved asymptotic coefficient. No Lean source changed for this experiment.

## Candidate potential

Write the rank-indexed certificate signature as

\[
q=((z_i,o_i))_{i=0}^{n-1},
\]

where the minima range over all valid certificates. The sorted terminal
signature is `((i+1,n-i))`. Within actual reachable network states, this terminal
condition characterizes sorting by the certificate-cardinality theorem.

For a chosen transition relaxation, let `B_0` contain only the terminal
signature. Recursively define

\[
B_s=\{q:\exists q'\in B_{s-1},\ q\longrightarrow q'
\text{ by an admissible parallel layer of active width }\le2^s-1\}.
\]

Identity transitions allow idle layers. The depth-dependent potential
`V_s(q)=1` when `q` is outside `B_s`, and zero otherwise, certifies that no
sorting completion of depth `s` exists, provided the relaxation contains every
actual transition. This Bellman construction combines the terminal rank
requirements with the suffix width bound; it does not iterate a uniform stage
multiplier. Its drawback is the lack of a compact analytic formula.

Three transition models were evaluated:

1. The full graph of reachable Boolean wire functions.
2. Its quotient by rank-indexed exact certificate minima. Each quotient edge
   comes from a real transition, but consecutive edges can use different
   representatives, creating optimistic completions.
3. A numerical relaxation on the same set of reachable signatures. For inputs
   `(a,b),(c,d)`, permit outputs `(min(a,c),v),(u,min(b,d))` with
   `max(a,c) <= u <= min(n,a+c)` and
   `max(b,d) <= v <= min(n,b+d)`. Require each output's zero/one minimum sum
   to be at most `n+1`. Optionally impose the active union coupling
   `u+v <= n+2`, and the suffix width constraint. Also permit unchanged pairs
   to cover redundant comparisons.

The per-wire `z+o <= n+1` bound follows from the hitting-set characterization:
if every zero certificate has at least `z` elements, any set of `n-z+1`
elements hits all of them and is a one certificate.

Model 3 additionally restricts all intermediate signatures to those reachable
on these fixed small arities. That is valid for these exhaustive catalogues,
but stronger than a general numerical relaxation available at arbitrary `n`.
In particular, its success cannot be extrapolated to large arity.

## Finite results

| Wires | Actual states | Per-wire signatures | Exact initial depth | Quotient initial depth | Numerical depth with both constraints |
|---|---:|---:|---:|---:|---:|
| 3 | 11 | 7 | 3 | 3 | 3 |
| 4 | 261 | 43 | 3 | 3 | 3 |
| 5 | 43,337 | 506 | 5 | 5 | 5 |

For five wires, the numerical two-layer viability sets contain:

| Numerical constraints | Viable signatures |
|---|---:|
| Neither union coupling nor width | 182 |
| Width only | 172 |
| Union coupling only | 169 |
| Both | 169 |

Thus the coupling has a measurable finite effect, though no improvement in
the starting-state depth. The quotiented actual graph permits 153 signatures
at two layers; even coupling and width do not recover all transition structure.

## What pairwise overlap recovers

There are two reachable five-wire states with the identical signature

```text
((1,3), (1,2), (2,2), (2,2), (5,1)).
```

The first needs three additional layers to sort; the second needs two.
Their prefixes, with zero-based wire indices, are:

```text
Slow: [(0,4)], [(0,3),(1,2)], [(2,3)], [(3,4)]
Fast: [(3,4)], [(0,4),(1,2)], [(0,3),(2,4)]
```

For wires `(0,2)`, the exact pair of union costs
`(minimum zero certificate of OR, minimum one certificate of AND)` is
`(2,4)` in the slow state and `(3,4)` in the fast state.

Enriching every signature by these costs for **all** wire pairs yields 581
signatures on five wires. The resulting quotient has zero remaining-depth
underestimate on every one of the 43,337 actual states, compared with a maximum
underestimate of one for per-wire statistics. The corresponding enriched
signature counts are 7 and 44 on three and four wires, also with zero loss.
This is an observed finite property, not a proof that pairwise data suffice
at arbitrary arity or determine their own next-step updates.

## Next mathematical obligation

Seek an analytic bound on this suffix potential using the pairwise union-cost
matrix, rather than only the upper bound `n+2`. In particular, identify a
quantity that charges repeated reconvergence over many layers and whose
terminal value is forced by all output ranks.

An obstacle is that updating union costs involving a newly compared wire
generally asks for certificates involving three or more old wires. Before
claiming a closed recurrence, either control those higher-order costs by a
universal inequality or retain a hierarchy of union statistics. The finite
result singles out overlap information as useful; it does not establish an
exponential loss or a route past the Kahale coefficient yet.

## Reproduction

```sh
python -B scripts/kahale_suffix_potential.py --wires 3 4 5 --output docs/kahale-suffix-potential-results.json
```

The script enumerates all reachable states until the frontier is exhausted;
a state-limit stop is explicitly reported as incomplete. Truth tables and
certificate minima are evaluated exactly with integer arithmetic. The
[machine-readable results](kahale-suffix-potential-results.json) include the
two prefixes and Boolean functions distinguishing the five-wire states.

This work uses the previously formalized
[joint certificate facts](kahale-joint-potential.md) and
[union coupling and active width bound](kahale-union-coupling.md).
