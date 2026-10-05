# Joint boundary information and exact transfer identities

## Status

The [transfer and charging update](kahale-transfer-charging.md) now proves
the boundary identity and entropy monotonicity in Lean, and identifies where
whole-block coupling can be created.

The asymptotic coefficient remains `3.270559...`. The target preferably exceeds
4. This investigation supplies a kernel-checked single-gate information identity,
a kernel-checked boundary-transfer identity, and finite challenges to a new bank.
It does **not** prove a stronger depth lower bound.

## The missing boundary term

Consider a comparator on positions `i,j` and a set `T` containing neither.
Write `a=Y_i`, `Z=Y_T`, `R_T` for its unordered rank set, and `P_T` for its
relative ordering. Let `A=T union {i}`, `R_A` its rank set, and `L` the insertion
position of `a` within `R_A`. The pair `(R_A,L)` determines `(R_T,a)` and vice
versa. Relative ordering of `A` consists of `L` and `P_T`.

The conditional chain rule therefore gives

```text
H(P_A | R_A) = H(L | R_A) + H(P_T | R_T,a)
             = H(L | R_A) + H(P_T | R_T) - I(P_T;a | R_T).
```

The comparator leaves `Z` unchanged. With `delta` meaning after minus before,

```text
delta H(P_A | R_A)
    = delta H(L | R_A) - delta I(P_T;a | R_T).
```

This is the exact boundary-transfer identity. The conditional mutual
information term describes information that the entering/leaving rank carries
about the other wires' order. It cannot be discarded as an insertion-position
cost. `BoundaryTransfer.boundary_transfer_identity` now proves the identity
with the finite-entropy definitions; `ComparatorTransfer` specializes it to
comparator execution.

The [finite calculation](kahale-boundary-information-results.json) checks the
identity on 64 instances from the prior four-transition obstruction, with
maximum numerical residual about `1.8e-15`. Some instances have zero change
in insertion entropy but nonzero change in relative-order entropy, entirely
accounted for by the conditional-information term. No independence of the
prefix outputs is assumed.

## An exact single-gate interpretation

Take `T` to be **all** positions except `i,j`. On rank permutations its rank
set determines the missing unordered pair, and its full vector determines
the entire sorted comparator output. Thus the gate's information gain is

```text
h_g = H(a | Z)
    = H(a | R_T) - I(P_T;a | R_T).
```

The first term is at most one bit; the second measures coupling with the
untouched ranks. The finite calculation records this identity for eight gates.
For example, one gate has orientation entropy one bit but coupling `1/3`,
so it gains only `2/3` of a bit.

For a parallel layer these identities must be applied in a fixed sequential
order, with the context updated after every gate. Computing all single-gate
terms at the initial prefix would again miss collective ambiguity.

`Kahale.comparator_information_identity` now proves this single-gate identity
in Lean for an arbitrary finite uniform input source and any prefix map whose
outputs are rank permutations. `finiteEntropy` is defined by the input-average
formula

```text
H(f) = log_2(N) - (1/N)*sum_(x in source) log_2(|fiber_f(f(x))|).
```

Thus prefix outputs retain their actual multiplicities. The proof uses
invariance under equal fiber partitions and the checked reconstruction maps.
It does not assume uniform rank images. The Shannon interpretation of this
formula follows by grouping equal output fibers. Entropy monotonicity and
conditional-entropy nonnegativity are now proved; conditional mutual-information
nonnegativity, conditional subadditivity, and the binary entropy upper bound
remain open for these definitions. The kernel theorem proves the displayed identity,
not the still-missing bounds on its terms.

## A joint bank with zero endpoints

For disjoint position sets `A,B` with sizes `k,l`, define

```text
M_(k,l) = (n/k) * average_(A,B) I(P_A;Y_B | R_A).
```

These quantities are zero initially: under uniform input permutations the
relative order inside `A` is independent of the outside ranks conditional on
its rank set. They are zero finally because the relative orders are fixed.
No centering against total information gain is needed. Each term is
nonnegative, although its change under a comparator can have either sign.

A candidate bank combines these `M` terms with the centered `R_k` terms from
[the previous investigation](kahale-layer-bank.md), plus bounded first-use and
absolute-completion credits. Its zero-endpoint components can retain genuine
joint information, rather than only the entropy of each subset separately.

The old four-transition dual obstruction has nonzero drift in the new terms:
approximately `-0.0354964` for `M_(2,1)` and `-0.0383650` for `M_(3,1)` on
five wires. Thus that particular obstruction no longer applies.

## Challenge results and limits

All five-wire calculations cover 7101 reachable rank distributions and 25
nonempty matchings. Exact integer weights are propagated; entropies and LP
solutions are numerical.

| Candidate | Boundary credit | Best local charge / `floor(n/2)` |
|---|---|---:|
| Centered subset averages only | at most `2n` | 0.823394 |
| Add single-outside conditional information | at most `2n` | 0.539476 |
| Add larger outside blocks | at most `2n` | 0.539476 |
| All these joint terms | no preset credit cap | 0.513245 |

The [uncapped fit](kahale-joint-bank-uncapped.json) uses endpoint cost about
`3.317263*n`. It still exceeds the exact half-slot budget in this finite
pointwise formulation. This is not an asymptotic impossibility result: an
explicit subleading exception budget may suffice. In particular, replacing
`floor(n/2)/2` by `n/4` changes the odd-width local budget, and an `O(1)` error
per layer can be subleading. Small odd-width failures alone do not rule out
coefficient 4 or larger.

The added outside-block terms on five wires are redundant with the previous
terms. Given `R_A`, all outside values except one determine the last value.
For complementary blocks, mutual information is symmetric after their rank
sets have been fixed; the `n/k` normalization changes the scaling. In
particular, the averaged five-wire features satisfy

```text
M_(2,2) = M_(2,3) = (3/2)*M_(3,1).
```

This explains why merely enlarging the outside block did not improve that
finite fit. Larger widths permit additional independent terms.

The [six-wire transfer probe](kahale-boundary-transfer-probe.json) embeds the
five-wire witnesses and also completes their matchings using the spare wires.
It evaluates fixed five-wire fits without refitting. Maximum observed charge
fractions are about `1.01874` for the single-outside fit and `0.939881` for
its equivalent-on-five-wires outside-block fit. The probe covers 32 distinct
snapshots and is not exhaustive. This rejects those fixed coefficient choices
as uniform local proofs. It does not reject the joint-bank family, size-dependent
weights, or an explicitly controlled exception scheme.

## Modular formalization

New focused modules build, with guarded axiom audits using only `propext`,
`Classical.choice`, and `Quot.sound`:

- `RelativeOrderCode`: reconstruct a vector from its rank set and relative
  code; recover an inserted rank and then the remaining rank set.
- `PermutationCompletion`: rank permutations agreeing outside one position
  are equal; those agreeing outside two are equal or differ by their swap.
- `ComparatorBoundary`: the untouched ranks determine the comparator output;
  projections outside its endpoints are unchanged.
- `FiniteEntropy`: input-average entropy from fiber counts, invariant under
  equal fiber partitions.
- `ComparatorInformation`: input/output fiber equivalences and the exact
  identity `gain = orientationEntropy - untouchedCoupling`.

These modules are independent of the still-unproved bank transition inequality.
The existing fiber-counting and conditional amortized-accounting modules are
reused, rather than inserting a conjecture into a sorting theorem.

## Next proof obligations

1. Formalize the remaining conditional-information inequalities. Both transfer
   identities, entropy monotonicity, and conditional-entropy nonnegativity are done.
2. For `I(P_A;Y_B|R_A)`, classify comparator positions in `A`, `B`, or outside
   both. Track changes in rank sets as well as relative orders.
3. Determine whether the transfer terms close under these joint statistics
   or create higher-order conditional dependencies. Preserve any signed terms;
   nonnegativity of information does not imply monotonicity of the bank.
4. Develop one uniform local inequality with controlled scale weights or
   explicitly budgeted exceptions. Its endpoint control must be independent
   of the desired depth bound.
   Coefficients on nonzero-endpoint credits must remain uniformly bounded
   across sizes, or have a separately proved subleading endpoint cost.
5. Seek saving fraction `rho>1/2` for a coefficient above 4; accept any proved
   improvement over the existing coefficient. The numerical fits do not
   establish such a saving fraction.

The exact boundary identity is the main new mathematical piece. A quantitative
bound on repeated creation and destruction of these dependencies remains open.

## Reproduction

```text
lake build AKS.Kahale.RelativeOrderCode AKS.Kahale.RelativeOrderCodeAxioms AKS.Kahale.PermutationCompletion AKS.Kahale.PermutationCompletionAxioms AKS.Kahale.ComparatorBoundary AKS.Kahale.ComparatorBoundaryAxioms AKS.Kahale.FiniteEntropy AKS.Kahale.ComparatorInformation AKS.Kahale.ComparatorInformationAxioms
python -B scripts/kahale_boundary_information.py --output docs/kahale-boundary-information-results.json
python -B scripts/kahale_relative_order_challenge.py --joint-boundary --output docs/kahale-joint-boundary-challenge.json
python -B scripts/kahale_relative_order_challenge.py --joint-boundary --joint-blocks --output docs/kahale-joint-block-challenge.json
python -B scripts/kahale_relative_order_challenge.py --joint-boundary --joint-blocks --unbounded-boundary --output docs/kahale-joint-bank-uncapped.json
python -B scripts/kahale_boundary_transfer_probe.py --output docs/kahale-boundary-transfer-probe.json
```
