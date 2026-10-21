# Fixed inflation removes the repeated small-sort/padding gate

2026-10-20. Codex (GPT-6), independent hand audit by
`/root/baseline_audit`. Construction bookkeeping only; global correctness
and a coefficient improvement remain unproved.

Take the integer D2 flow on4^d' abstract wires. Multiply every allocation,
up/down port, deficit, capacity and native interval length by fixed S=4^L.
This gives a table on N=S*4^d' physical wires, with exactly the same steps.
It scales counts and sets, not input-dependent comparator decisions.

For sufficiently large d' (in particular d'>=10), the (2,3,2) schedule has

    tf=(5d'-kappa)/2,
    kappa=(24,23,28,25), indexed by d' mod4=(0,1,2,3).

Hence tf=5/4*log2(N)+O_S(1). Its terminal native blocks have at most1024S
wires. If terminal purity is proved, sort those blocks exactly in parallel
ONCE, at constant depth S_bitonic(2L+10). There is no need to charge that
large fixed sort to every ordinary stage.

Choose S divisible by4096. Every actual node arity Sa0 is then an exact
4096-by-(Sa0/4096) rectangle. Nonempty bags have at least S wires;
S>=65536 suffices for column width>=16. This eliminates arbitrary-arity
padding/ragged surcharges and the old requirement that every small-node
exact sort fit the ordinary stage depth. Root cost may also be any fixed
constant, separately from the leading coefficient.

Existing placement APIs tie ambient wire count to tree depth. One possible
adaptation is to embed the smaller schedule in depth d'+L and leave the
extra bottom levels unused; alternatively abstract the ambient cardinality.
Neither adaptation has been formalized, and trusted definitions need not be
weakened to accommodate the construction.

## Conditions not removed by inflation

- Child/fringe cuts need not align to rows. For down block b0, alignment is
  a0 |4096*b0, independent of S. Price the existing arbitrary-cut interpolation
  (potentially one column width per direction) or prove a sharper bound.
- Thirteen full fringe rows require pi/(2a)>=13/4096 for every ordinary D2
  sender. Top-descending nodes have no fringe; whole-up nodes need separate
  treatment. Scaling preserves this ratio and does not prove its lower bound.
- Native interval scaling does not prove perfect-flow purity or the actual
  sorting invariant. Those are still end-to-end obligations.
- A terminal bound mu*cap<1 needs mu*S*1024<1. The new preservation
  inequalities must actually admit a sufficiently small mu; it cannot be
  chosen freely if bulk or residual terms impose a lower bound.
- TINY-FRINGE supplies only a reviewed extension of local probability bounds,
  with an extremely small supported rank fraction. Its use in this invariant
  is not established.

The nominal3*S_bitonic(12)=234 ordinary depth still projects to292.5,
conditional on all those gates and a complete global invariant. Padding a
general n to the next power of4 would add only a constant to log2(n), if the
power-of-four family is proved. This is not yet a sorting theorem.

Next mathematical task: derive the ordered spill/profile recurrence on this
scaled flow, including the width of returning child bands. Use a compressed
flow representation if deeper tests are needed; do not enumerate4^d' bags
or interpret an optimistic local-price division as a proof.

## Parameterized D2 cost screen (2026-10-21)

The `(2,3,2)` choice is not forced by the leading stage-count formula. From
`flowsim.Par`, `tf/d -> (x+y)/z` and `log2(N)=x*d+O(1)`, so the stage rate is
`(x+y)/(x*z)`. If a fixed three-column-sort core has row height `m=2^q`, its
depth is at most `3*q*(q+1)/2`. The candidate row height `q=x+y+z+5` is a
scaling heuristic, not a consequence of the uniform Chvatal formulas: this
D2 flow has nonuniform deficits. The script checks every sender in its finite
flow run, but an all-depth lower bound on the fringe ratio remains open.

[`parameter_cost_screen.py`](parameter_cost_screen.py) evaluates the product
and runs the exact integer D2 flow at a finite depth with scale `m`. At depth
30 it reports:

| D2 parameters | Rows | Core depth | Stages / `log2 N` | Conditional coefficient | Minimum sampled fringe rows | Terminal sorter bits |
|---|---:|---:|---:|---:|---:|---:|
| `(2,3,2)` | 4096 | 234 | 5/4 | 292.5 | 13.52 | 22 |
| `(3,3,2)` | 8192 | 273 | 1 | 273 | 14.65 | 25 |
| `(4,4,3)` | 65536 | 408 | 2/3 | 272 | 15.29 | 28 |

The exact finite flows also had integral allocations, even up-port counts,
and sender arities divisible by the proposed row height. These results make
`(3,3,2)` a lower-complexity parameterized candidate than `(4,4,3)`; both
have a little more nominal coefficient slack than 292.5. The cost arithmetic
and finite flow checks are not a sorting bound.

The nominal fringe ratios are measured from the D2 flow itself. For example,
at depth 30 the minimum occurs at a `mid` sender, but its actual allocation is
not the uniform formula `a=(1-1/(A^2*k^2))*c`; that formula must not be used
to infer an all-depth lower bound for D2.

Fresh-context review identified the main compatibility limit: the existing
`TwoRoundHyp`/`NodeGeom` provider requires ordinary arities above `2^42` and,
when the fringe is nonzero, an even `f>=131040` in an exact shape
`m=2f+64b`, `up=2fn`. Neither proposed row height can satisfy that provider.
The thirteen-row test is only a necessary geometric screen; it does not
prove the B2/F2 local rank-tail promises, exact row-aligned sender shapes, or
the global ordered-port recurrence. The displayed nonintegral fringe-row
ratios also do not give the exact `f` required by `NodeGeom`; arbitrary-cut
provider bounds would be needed. Thus the new coefficients are conditional
on a new small-row local provider and a parameterized global proof. No Lean
work should start until those interfaces are stated and their recurrence
closes.
