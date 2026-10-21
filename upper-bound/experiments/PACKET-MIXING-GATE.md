# Packet-mixing depth and rounding gate

2026-10-21. Codex (GPT-6). Paper-level screen of UB-25, not a construction,
network certificate, global recurrence, or sorting bound.

## What the screen tests

For a sorted packet of height `m=2^q`, merging two packets and dealing
alternating outputs costs at most `q+1` comparator layers. On every Boolean
threshold, the two outgoing zero-counts are the floor and ceiling of the
input sum divided by two. Thus a fixed matching schedule of packet pairs
implements rounded averaging.

The stage budget in the current R1 scheduler is 400 layers for coefficient
300 (it charges `3/4` per stage layer). The `36/105000` tolerance used below
is only an optimistic proxy borrowed from a different UB-37 schedule with
the fringe idealized away; it is not established for a packet schedule.

## Rank/Frobenius lower bound and refined bulk screen

There is a stronger bound for perfect matchings on even `c`. Every one-step
pair-average has rank `c/2`, so a product `P` of `s` matchings has rank at
most `c/2`. The constants split off as an invariant rank-one subspace, hence
`rank(P-J)<=c/2-1`, where `J` is the all-mean projection. The row support
bound gives `||P||_F^2 >= c/2^s`, and double stochasticity gives
`||P-J||_F^2=||P||_F^2-1`. Comparing Frobenius and operator norms yields

```text
rho = ||P-J||_2 >= sqrt((c/2^s - 1)/(c/2 - 1))
                  -> 2^((1-s)/2) as c -> infinity.
```

The existing UB-25 worktree (`MIXING-TAIL.md`) has a sharper one-cycle
estimate than the normalized-L1 recurrence above. If `alpha=H/(cm)`, its
bulk excess divided by `cm` is at most

```text
(rho/2)*sqrt(alpha*(1-alpha)) + s/(4m)
    <= rho/4 + s/(4m).
```

The improved variance term follows from
`sum_i (x_i-H/c)^2 <= mH-H^2/c`; the one-sided excess is at most half the
L1 norm. The rank/Frobenius floor above therefore does **not** rule out this
certificate. `packet-mixing-energy-screen.py` shows that at `(q,s)=(16,23)`
the structural lower bound allows a bulk estimate of about `0.0002098`, below
the proxy `36/105000 ~= 0.0003429`. The actual spectral norm must be at most
about `0.0010205` to pass; no unbounded matching family with that norm has
been proved.

Fresh review (`/root/packet_budget_review`, GPT-6-luna) verified the refined
variance estimate and this correction. The bound applies to aligned bulk
excess; nonaligned cuts and partial rows need their extra charges. The
finite random screen observed `rho` around `0.0027` for 23 rounds at packet
counts up to 262144, above the required `0.00102`; this is discovery evidence
only, not a lower bound on optimized families. Reproduce it with
`packet-random-cycle-screen.py`. Rare cohorts, the actual tolerance, packet
repacking, and the full scheduler remain open. The arithmetic gate is viable
but extremely tight; the next local test should seek an explicit structured
schedule or a stronger analytic norm bound before any Lean work.

Run with:

```sh
python upper-bound/experiments/packet-mixing-energy-screen.py
python upper-bound/experiments/packet-random-cycle-screen.py
```

