# Certificate families in the positional barrier schedule

## Concrete findings

We examined the explicit 40-stage, 161-wire positional barrier schedule.
It passes the existing scalar height/position conditions but fails sorting.
The central Boolean inversion is between wires `85` and `86` (zero-based).

Tracking input identities exposes the failure:

| Certificate | Actual valid size | Sorting requires at least |
| --- | ---: | ---: |
| Force wire 86 to zero | 77 | 87 |
| Force wire 85 to one | 65 | 76 |

The two input sets are disjoint. Set the first set to zero and the second to
one: both output conditions hold simultaneously, regardless of the remaining
inputs. This directly witnesses an inversion.

These are **inclusion-minimal certificates obtained by greedy deletion**,
not claims about globally minimum cardinalities. The complete sets are in
[`kahale-certificate-witness.json`](kahale-certificate-witness.json).

### Two distinct losses in the scalar method

1. **Height is only an upper size bound.** The tracked zero height at wire 86
   is `20`, giving a certificate bound of `2^20 = 1048576`. This says nothing
   that excludes the actual size-77 certificate.
2. **Keeping one certificate misses alternative certificates.** A deterministic
   policy that always keeps the smaller available certificate at a min/OR
   branch gives a zero certificate of size `134` at wire 86 and a one certificate
   of size `126` at wire 85. Those chosen certificates do not reveal the central
   size violation. Propagating certificates conditioned on the failed input
   gives sizes `82` and `71`; subsequent greedy deletion gives `77` and `65`.

The second loss matters: merely replacing powers of two by the exact size of
one tracked certificate still need not capture the relevant obstruction.

Among the 3013 comparator events, the single-certificate policy has 2530
events with a nonempty overlap in a zero or one union. In 934 zero-union events
and 967 one-union events, taking the union does not increase cardinality over
the larger input set. These are diagnostics of this policy and example, not
universal overlap lower bounds.

## Exact family-level structure

Let `Z_i` be the upward-closed family of zero certificates at output `i`, and
`O_i` the corresponding one-certificate family. A set `T` belongs to `O_i`
exactly when it intersects **every** set in `Z_i`.

Thus the minimum one-certificate size is the transversal (hitting-set) number
of the zero-certificate family. The two certificate families are not independent
collections of sizes.

For a comparator with incoming families `Z_a,Z_b,O_a,O_b`, the exact rules for
membership of any fixed input set are:

| Output | Zero family | One family |
| --- | --- | --- |
| min | `Z_a union Z_b` | `O_a intersection O_b` |
| max | `Z_a intersection Z_b` | `O_a union O_b` |

Equivalently, minimal certificates for an intersection family are the
inclusion-minimal unions of a certificate from each input family. Choosing just
one pair discards alternative overlaps that can create a smaller union.

### Sorting is an intersection requirement across output ranks

For every pair `i <= j`, every `S in Z_j` must intersect every `T in O_i`.
This condition is **equivalent to sorting**, by the 0–1 principle:

- Disjoint sets allow an input with output `i=1` and output `j=0`.
- Conversely, an actual Boolean inversion supplies disjoint certificates:
  its zero-input support is a certificate at `j`, and its one-input support
  is a certificate at `i`.

There is another equivalent characterization: every zero certificate on wire
`i` must have size at least `i+1`, and every one certificate must have size at
least `n-i`. Necessity follows from threshold behavior of sorted Boolean
outputs. For sufficiency, disjoint `S in Z_j` and `T in O_i` would have

```text
|S|+|T| >= (j+1)+(n-i) >= n+1,
```

which is impossible for disjoint subsets of `n` input positions.

This is an exact characterization, not by itself a stronger lower bound.
It identifies the structure a new quantitative argument must exploit.

## Verification and scope

[`AKS/Kahale/CertificateCompatibility.lean`](../lower-bound/experiments/AKS/Kahale/CertificateCompatibility.lean)
proves the extremal-input certificate criterion, the four comparator family
updates, hitting-set duality, the cross-output intersection characterization,
the two cardinality lower bounds, and their equivalence to sorting.
`lake build AKS.Kahale` passes, including guarded dependency checks for the new
family results: only `propext`, `Classical.choice`, and `Quot.sound` occur.
The focused source gate also passes.

The 161-wire witnesses and overlap statistics are exact finite computations,
not kernel evaluations of that concrete network. Their validity uses the
monotonicity of comparator execution: evaluating the extremal assignment
outside a certificate suffices to verify the certificate. That general
criterion is proved in Lean.

Reproduce the finite witness with

```sh
python -B scripts/kahale_certificate_probe.py --depth 40
```

Greedy deletion gives inclusion-minimal sets because certificate validity is
monotone under adding fixed inputs; a deletion that fails cannot become valid
after other fixed inputs are removed. No SAT optimality claims are involved.

## Next quantitative target

**Follow-up:** [the joint-potential analysis](kahale-joint-potential.md) rules
out the elementary uniform monomial potential class as a route beyond the
existing coefficient. [The shared-universe coupling](kahale-union-coupling.md)
provides a kernel-checked relation between the two union costs at an active
comparator, with their sum at most `n+2`.

Study the joint evolution of a zero family’s smallest set and its transversal
number, or a tractable statistic that retains enough of this relation.
At the sorted endpoint these are respectively `i+1` and `n-i` on every wire.
Comparator updates are explicit union/intersection operations, so candidate
potentials can be checked against exact family evolution on small networks.

A successful lower-bound invariant must show that meeting these demands
simultaneously costs more stages than the scalar binomial model predicts.
In particular, it must force an exponential-rate loss rather than merely
explain a few finite certificate defects. The example does **not** prove that
its many overlap events occur in every shallow sorting network, and we have
not established a new asymptotic coefficient.
