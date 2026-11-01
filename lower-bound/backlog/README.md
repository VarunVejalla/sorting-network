# Lower-bound research backlog

This is the ticket index for lower-bound ideas beyond the checked endpoint.

**Current endpoint:** `liminf D(n)/lg n ≥ 1/(1 - lg φ) ≈ 3.2706`, kernel-checked. The finite form is
`n·F_{D(n)+1} ≤ 2^{D(n)+1}(D(n)+1)^2`. See [`../best/README.md`](../best/README.md) and the proof map
[`docs/kahale-lower-bound.md`](../../docs/kahale-lower-bound.md).

Supporting files:
- [`SURVEY.md`](SURVEY.md): what is proved, the literature, a digest of the prior routes, and the ranked directions.
- [`ruled-out.md`](ruled-out.md): barriers. Read it before proposing a new potential or charge.
- [`../notes/INDEX.md`](../notes/INDEX.md): the `docs/kahale-*.md` notes and scripts by topic.

## How to use

- The machine-readable source is [`tickets.json`](tickets.json). Its fields follow
  [`upper-bound/backlog/tickets.schema.md`](../../upper-bound/backlog/tickets.schema.md), with ids `LB-NN`.
- `baseline` and `projected` are lower-bound coefficients of `lg n`, so **larger is better**. `projected` is `null`
  when the effect is unknown or the ticket does not change the constant.
- `scripts/tickets --lb` validates the registry; add `--table`, `--list [status]` or `--show LB-02`.
  `scripts/tickets --all` checks both the UB and LB registries.
- The ticket lifecycle, claim levels, and worktree-per-ticket rules are those of
  [`docs/agent-protocol.md`](../../docs/agent-protocol.md).
- Priorities:
  - **P1**: a near-certain formal result or a cheap direct test.
  - **P2**: a well-posed new argument or formalization with a clear first test.
  - **P3**: exploratory or long.
- Prior routes all carry P2 by convention.
- Each target that is a published result says so in its `notes`. `claim_level` records only what the repository has
  shown.

## Open directions (ranked; SURVEY §d)

| ID | Pri | Idea | Status | First test |
|---|---|---|---|---|
| LB-01 | P1 | Finite bound `max(lg n, lg n!/⌊n/2⌋, Kahale)` in Lean | ready | `n! ≤ 2^G` from trace injectivity |
| LB-02 | P2 | Two-sided (0/1) certificate-height relaxation | ready | exact DP/LP rate of the joint relaxation |
| LB-03 | P3 | Information/certificate tradeoff on extremal schedules | proposed | `Σ(1-h_g)` on the positional barrier family |
| LB-04 | P2 | k-sorter constant-depth bounds (ITCS 2023) | proposed | depth 3 needs `k ≥ ⌈n/2⌉` in Lean |
| LB-05 | P2 | ε-halver / approximate-selector depth bound | proposed | reuse `ApproxSelection` / `SelectionCounting` |
| LB-06 | P2 | Exact `D(n)` for small `n` | proposed | `D(4)=3`, `D(5)=5` by kernel `decide` |
| LB-07 | P3 | KLMPSS size bound `1.12 n lg n` | proposed | lemma map onto existing modules |
| LB-08 | P3 | Scale-compatible signed quadratic witness charge | proposed | 6–7-wire central-baseline LP screen |
| LB-09 | P3 | Plaxton–Suel shuffle-based `Ω(lg² n/lg lg n)` | proposed | model statement and outline |
| LB-10 | P3 | Depth for "usually sorts" networks | proposed | worst-case use in `SelectionCounting` |
| LB-11 | P1 | Liminf headline without the legacy upper bound | ready | `EReal` liminf statement |
| LB-12 | P3 | Merging-network bounds | proposed | fan-in depth bound for merging |

## Prior routes (all keep 3.2706)

| ID | Route | Status |
|---|---|---|
| LB-20 | Scalar binomial recombination | rejected |
| LB-21 | Positional height constraints | rejected |
| LB-22 | Certificate families and union coupling | parked → LB-02 |
| LB-23 | Additive monomial joint potentials | rejected |
| LB-24 | Pairwise union costs and suffix potentials | parked |
| LB-25 | Rank congestion / coalition Hall | parked |
| LB-26 | Information accounting and slot-saving banks | parked |
| LB-27 | Occupation spectra and degree recycling | rejected |
| LB-28 | Activation hypergraphs and preparation charges | rejected |
| LB-29 | Residual image difficulty (dependency charges) | rejected |
| LB-30 | Shared polarity and witness charges | parked → LB-08 |
| LB-31 | Fiber-charge correction chain | rejected |
| LB-32 | Coupled Boolean faces and transport | parked |
| LB-33 | Correlation (Harris/BK/Reimer) potentials | rejected |
| LB-34 | Mixed-polarity restriction families, worst-case inputs of `tr` | rejected (no coefficient; tree family is a test of one network) |
| LB-35 | Amplification kill test | rejected (no proved rate barrier) |
