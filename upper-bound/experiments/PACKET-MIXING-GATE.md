# Packet-mixing depth and rounding gate

2026-10-20. Codex (GPT-6). Paper-level screen of UB-25, not a construction,
network certificate, global recurrence, or sorting bound.

## What the screen tests

For a sorted packet of height `m=2^q`, merging two packets and dealing
alternating outputs costs at most `q+1` comparator layers. On every Boolean
threshold, the two outgoing zero-counts are the floor and ceiling of the
input sum divided by two. Thus a fixed matching schedule of packet pairs
implements rounded averaging.

The UB-25 conditional estimate for a cycle of `s` matchings whose real
averaging product contracts the zero-sum subspace by `rho<1` is

```text
relative L1 deviation after t cycles
    <= rho^t/2 + s/(2*m*(1-rho)).
```

I priced this at the current 789.75 scheduler's stage rate `3/4`. To reach a
coefficient below 300, a stage may spend at most 400 layers. Taking a
hypothetical 3-matching cycle and the optimistic `36x` accepted
`epsilon_B` tolerance as a proxy, `packet-mixing-budget.py` gives the required
maximum `rho` for each packet height. The underlying `1/105000` normalization
is the accepted parameter, but the `36x` allowance was screened at a different
schedule with the fringe idealized away; it is not established for the
789.75 construction or any packet schedule. In particular, `q=14` permits 24
matching rounds in 360 layers (coefficient 270); under that proxy the rounding
bound fits only if the unproved cycle contraction is at most the script's
printed `rho_max`.

This is a useful local numerical screen, but too incomplete to count as a
sub-300 global gate. It does not certify that any 3-matching family has the
required operator contraction for every packet count, establish that the
remainder of the proof tolerates the proxy error, or control rare cohorts.
Even a successful expander screen would leave the global obstruction: row-slab
routing cuts packets into fragments, and repacking those fragments can consume
the saved depth. Do not start Lean before an explicit unbounded packet family,
the actual error budget, rare-cohort control, and a complete priced routing
cycle are established and independently reviewed.

Fresh review (`/root/packet_budget_review`, GPT-6-luna) confirmed the UB-25
rounding inequality and script arithmetic; it identified the schedule-transfer
and tolerance-proxy caveats now stated above.

The same review supplied a necessary contraction floor. A product of `s`
pair-averaging matchings is doubly stochastic, and each row has support at
most `2^s`. For `c` packets, Cauchy gives

```text
rho = ||P - J||_2 >= sqrt(2^-s - 1/c),
```

so for unbounded packet counts `rho >= 2^(-s/2)`. With `s=3`, this floor is
`1/sqrt(8) ~= 0.35355`, only about `0.02164` below the `q=14` proxy gate
`rho_max ~= 0.37519`. This does not rule out the gate, but shows that the
required contraction is close to the best possible from support size alone;
attaining it in every singular direction with a shared unbounded family is a
substantial construction obligation.

Run with:

```sh
python upper-bound/experiments/packet-mixing-budget.py
```
