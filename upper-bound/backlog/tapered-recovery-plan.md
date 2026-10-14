# Recovering the first sub-1000 proof

Source audit: 2026-10-13, including the uncommitted `tapered-945` worktree.
This supersedes the small-provider coverage assessment in the earlier
`roadmap-700-200.md`. Status: source inspection and derived, unaudited
mathematics; exact rational arithmetic was evaluated in Python. No Lean
rebuild, new global theorem, or verified constant improvement is claimed.
The accepted result remains 1419.

## Recommendation

Keep 945 as the first target. Use an exact sorter for small actual registers,
separate the frontier flow types, and prove the nonuniform rank profile of
the routed execution before adding more conditional interface lemmas.
Use 999 only if a complete, correctly typed rank/flow recurrence needs the
extra allowance. A standalone positive scalar margin is not that recurrence.
Treat 700 as a subsequent construction change.

## 1. The local provider can be much simpler

`AKS/Bitonic/Shrink.lean` already supplies an exact sorter at every arity.
For actual bag size `a <= 2^60`, its depth is at most

```text
60*61/2 = 1830 < 1890.
```

Thus the first 945 proof need not use a scramble construction on these bags.
The sorted permutation output has no crossing errors, and every extreme
cohort of size `j` is in a fringe of size `u` whenever `j <= u`.
This is a source-based application of the existing sorter theorem; the new
provider adapter itself has not been formalized here.

Define a local contract in terms of the actual down-port cuts and the two
actual half-up ports. Keep rectangle rows/columns and padding inside the
large-size implementation. Require the cohort support explicitly, rather
than attempting to infer it from total up-flow. The exact branch can then
give zero bulk/fringe error, and has no artificial 8001-rank ceiling.
This does not repair global native-rank distribution: sorting a bag cannot
import missing keys from elsewhere.

### Concrete gaps in the current adaptive interface

* Its existence theorem assumes actual `a >= 2^34`. Under the proposed
  ordinary occupancy identity at reference `C=2^34`, actual size is
  `a=2^34-1024+eta`, `|eta|<=69`, hence lies between `2^34-1093` and
  `2^34-955`. Reference size and actual size cannot be interchanged.
* `lowFits` proves `(f+1)*columns <= flow.up`. But `LocalIntegerFlow.up`
  is the **total** up-port, and `RaggedProfileGeometry` splits it in half.
  The low/high estimates must be installed with the appropriate half-port.
  The tuned `256016`-wire protected fringe exceeds the approximately
  `130560`-wire half-port at minimum reference capacity.
* `maxRank` must cover the cohort used by `fringeSend`. The tuned width-16
  support is at most 8001, while `mu*C` can be much larger in its advertised
  size range. A low-fringe fit theorem alone does not establish support.

`SameBagScale` constructs these minimum-reference bags at `b.l=alpha(t)`.
The fact `alpha+2<=omega` means the band has another active level; it does
**not** make the selected bag a strict interior bag. The corrected plan
must apply the top-frontier mass there, not assume ordinary occupancy.

If the cyclic branch is retained separately, its row floor can plausibly be
lowered from `2^30` to `2^29` without new concentration machinery:
the first-round excess bound 240 is strictly below `m/2^21 >= 256`, and the
second-round rate at the new floor is `1048/9`, whereas the logarithmic
union cost is below 22. The tuned fringe predicates are independent of this
row floor. This is an arithmetic repair plan, not a Lean-checked extension;
the exact small-register branch makes it unnecessary for the first theorem.

## 2. Correct the large ordinary provider's half-port and support together

The large-size existence theorem accepts arbitrary `n>=16`; power-of-two
columns are a choice in `RectanglePadding`, not a hypothesis of
`truncated_fringe_bulk_pair_exists`. With the exact branch covering
`a<=2^60`, choose the large ordinary rectangle in a much narrower row window.
One coherent arithmetic screen is:

```text
mu' = (63/64)*mu = 51/218103808
M   = 2^34 + 2^28 = 17448304640
n   = floor(a/M),     m = ceil(a/n),     a > 2^60.
```

Then `n>=2^25` and `M<=m<=M+1024<2^35`; one-row padding still suffices.
Use the standard `f=131040` witness. At ordinary occupancy
`a=(1-1/2^24)C+eta`, `|eta|<=69`, the slight reduction of `mu` gives room
for **both** `(f+1)n <= up/2` and
`mu'*C <= floor((128/4095)*f*n)`. The common rare-rank coefficient
`1/9000000` can remain a weaker bound on the standard witness.

Conservative exact-rational screens at `C>=2^59` give:

| Quantity | Positive margin |
| --- | ---: |
| Original ordinary scalar screen with `mu'` substituted | about `1.6150e-8` |
| Half-port fit, normalized by C, including one wire of up rounding | about `8.7487e-8` |
| Cohort support, normalized by C, including floor loss | about `9.1697e-10` |

These are parameter screens, not a provider theorem. They preserve the
1890-layer depth ceiling because `m<=2^35`. The full proof must include
padding/aligned-cut errors and instantiate all support bounds on the actual
ports. They concern ordinary occupancy; bottom/frontier registers have
different `a/C` ratios and need their own provider contracts. Larger
frontier fringes may require the existing parameterized F2 construction,
not the fixed standard `f`. Do not silently transfer this ordinary screen.

## 3. The current global flow wrapper has the wrong frontier target

`GlobalFlowStep.candidate_next_actual_flow_nonempty` asks for an ordinary
`LocalIntegerFlow` at **every** current scheduled address and an error of at
most 69 from ordinary next occupancy at frontier addresses. The real flow
modules instead define, with normalized address debt `e`:

```text
interior: (1-1/Q) C
top:      C + (16/15)e C
bottom:   B - C/Q - (16/15)e C,      Q=2^24.
```

These differences are not rounding errors. Even at `e=0`, top and interior
targets differ by `C/Q`. At the stage-two root with `d=14`, this is `2^44`
wires. In contrast, conservation and the error fields of `LocalIntegerFlow`
allow at most `1+64*(1+70/64)=135` wires of total discrepancy from its own
ordinary target. The conditional wrapper cannot be instantiated there.

Introduce one schedule-indexed flow family with separate constructors for
bootstrap, interior, top advance, top retreat, bottom expansion, bottom
contraction, and meeting. Each constructor specifies the appropriate count
target, ports, and discrepancies. Prove coverage, exact routing, and the
receiver's discrepancy relative to **its** next shape. Reuse the existing
`FrontierDebtFlow` conservation identities and local integerizers.
Do not try to prove that exceptional occupancies are within 69 of interior
occupancy. Prove rounding bounds around the correct exceptional formulas.

This is the first scheduler gate, independent of comparator correctness.

## 4. The rank gap needs signed, nonuniform accounting

The old whole-strict-subtree bound at bootstrap leaves a defect of one full
reference capacity. Trying to fit that defect in `reserve*C`, where
`reserve` is about `8.58e-8`, is the wrong accounting problem.

Uniform ancestor localization is also not a valid replacement. In a
perfectly sorted bootstrap level-one interval of size B, the up-fringes
concentrate near its two ends. For a middle level-one address, the exact
bootstrap low half-up width is `4095*B/2^29`. It lies in the first native
level-two child interval. Relative to that child's reference capacity
`C=4B`, its size is `4095*C/2^31`, about 22.24 times the signed reserve.
The nominal uniform root share is about 32 times smaller. This is a
hand-derived counterexample to the proposed uniform localization shape,
not to the sorting algorithm. The port-to-native-interval ownership example
still needs a formal proof; the source's exact bootstrap widths supply its
arithmetic.

For an ordinary bag of reference capacity C and debt e, the ideal complete
child-subtree mass calculation gives the deficit

```text
Delta_j = C/64 + (16/15)C*(q_j + e/64).
```

This follows by summing the fixed-point subtree formula in `SubtreeMass`
under that child. A prefix of j complete children therefore has deficit

```text
j*C/64 + (16/15)C*(sum_{h<j} q_h + j*e/64).
```

For `1<=j<=63`, `sum q_h=(j-32)/2^22`. At `e=0`, the positive extra
term for `j=63` is `31*C/3932160`, about 92 times `reserve*C`.
Thus descendant-only estimates also fail to close the proposed signed-tail
budget. This is a failure of that bound, not a reachable bad execution.

The useful conservation direction is

```text
current native-prefix mass
  <= native-prefix size - descendant native mass - ancestor native mass.
```

To cancel the positive nominal deficit, an ancestor/frontier **lower** bound
in the same prefix is needed. The existing ancestor upper-bound theorem
does not supply it. Derive the correct ideal rank profile before estimating
its error; do not charge its deterministic fringe mass as error.

## 5. First mathematical gate: a signed prefix-count recurrence

Fix a global key threshold x. In one bag, let H be the number of input keys
below x, and P_p the number below x in its first p output positions. The
two-sided local rank crossing bound E_p implies

```text
P_p = min(H,p) - d_p,       0 <= d_p <= E_p.
```

The upper bound `P_p<=min(H,p)` is immediate from capacity and conservation.
For the lower bound, distinguish `H<=p` and `p<=H`, and use the appropriate
subset of the separator's rank-p crossing set. Thus for a port `[p,q)`:

```text
H_port = min(H,q)-min(H,p) + d_p-d_q.
```

This is a derived finite counting lemma, not yet a new Lean theorem. The
deficits at shared endpoints must be shared variables. Adjacent ports
telescope exactly. Two ports separated by a gap do not telescope; charge
each remaining endpoint. For a two-threshold native interval, subtract the
two prefix formulas and retain all four endpoint terms.

Define the ideal full-sort profile on the **same routed ports**, summing
every incoming parent and child contribution at receivers. At each step,
compare the actual counts with the clipped ideal counts. This correctly
retains concentrated fringes. Clipping is 1-Lipschitz, but a naive sum over
all incoming branches can still amplify errors; the outsider taper and
rank-sensitive fringe bounds must be used where required. The recurrence
alone is not a stability proof.

The acceptance gate is an exact bootstrap profile followed by a symbolic
six-stage cycle containing both frontier directions and an interior
transition. The meeting cases remain separate. Require:

1. Correct ideal counts at every native child prefix and suffix used by
   `hL`/`hR`, including endpoint slots and nonuniform up-fringes.
2. Joint conservation of nominal counts, with cancellation before absolute
   error bounds; explicit endpoint counts for disconnected ports.
3. One finite recurrence for the actual approximation/rounding errors that
   reproduces the ordinary `badSend0` and higher-order `fringeSend` budgets.
4. A retirement rule: when an upper level disappears, explain how the needed
   native purity follows. A zero up-port cannot be handled by an ordinary
   fringe-filtering argument with a nonzero outsider allowance.

If this gate fails for 945, identify the offending coefficient and rescreen
it before extending the Lean induction. In particular, never introduce
`AncestorLocalizationProfile` as an unproved global hypothesis in a headline.

## 6. Completion order and cost gates

| Step | Deliverable | Numerical/correctness gate |
| --- | --- | --- |
| A | Exact small-register provider and generic local contract | All a<=2^60; depth<=1830; actual half-up support |
| B | Large ordinary provider with half-port and cohort support | Narrow row window, depth<=1890; all aligned-cut/padding charges included |
| C | Typed finite flow cycle | Correct target at each shape; actual registers form one partition; bounded rounding |
| D | Six-stage signed rank profile | Exact ideal cancellation; errors fit both rank-tail premises; valid upper retirement |
| E | Global induction | Every shape and every outsider order on the same routed execution |
| F | Terminal and asymptotic assembly | Parent-group purity; actual maximum path depth; arbitrary-n restriction |

A and C can proceed independently. D depends on correct port geometry, not
on polishing every local provider. E should start only after D has a
numerically closed induction statement. Existing ownership/execution and
terminal-group lemmas remain useful under these corrected hypotheses.

Under the intended three stages per six bits, a uniform 1890 ceiling gives
945. The exact small branch fits that ceiling; it is not an additional
serial operation. All recurring frontier work must fit the same stage
budget, or be explicitly repriced.

The existing fallback arithmetic gives 999 at a 1998-layer ceiling and
stronger bulk error `3e-7`. It needs different row/provider bounds and the
same rank/scheduler proof. It cannot absorb an extra serial sorting stage
at every frontier visit. Use it if a correctly quantified residual term
fits its extra allowance; it does not cure a nominal capacity-sized defect.

For 700 the repeated-node ceiling is 1400. Exact sorting of small bags still
fits if the cutoff is changed to `2^52` (`52*53/2=1378`), but the large-node
algorithm must also be improved. Keeping two 630-layer column sorts leaves
140 layers for the complete final repair. No uniform repair construction
at that budget is supplied here. Establishing D first will identify the
actual cuts/ranks such a repair must protect.
