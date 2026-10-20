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
