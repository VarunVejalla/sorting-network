# Fresh-context review: the oracle's scope

2026-10-20. Author: Codex (GPT-6). Independent reviewer:
`/root/flux_contract_review`, started without inherited conversation context.
Claim level: reviewed hand arguments and exact-integer Python diagnostics,
not a sorting-network theorem.

The reviewer confirmed the stable two-color rank interpretation of endpoint
deficits and the fringe endpoint reduction, for epsF>0 and deltaF in [0,1].
However, counts alone forget that comparators cannot decrease any input
prefix's zero count. A relaxed oracle can unsort sorted input. Thus its first
failure was insufficient evidence against comparator-aware invariants.

The strengthened `--monotone` mode tracks Boolean words. Each output port is
internally sorted, and its endpoint prefix counts dominate the actual incoming
prefix counts. For an interior position l+t in a port [l,r],

    Yout(l+t) = min(Yout(l)+t,Yout(r)),
    Yin(l+t) <= min(Yin(l)+t,Yin(r)).

Endpoint dominance therefore implies dominance at every position. The script
also checks that property directly with integer cumulative sums. A zero key
is represented by integer1 in these arrays; zero counts are their sums.
Incoming port fragments are concatenated in the declared loop order
(source level, source index, low-up/child/high-up port). This is a fixed
routing layout, not an order chosen to help a particular LP.

The reviewer confirmed that binary prefix dominance is equivalent to
realizability by some sequence of ascending adjacent comparators on that
input. Stable ranks can also be preserved across an execution by first sorting
the actual keys separately on the zero and one positions, then performing
the binary transport. This remains an input-dependent construction, with no
common network or useful depth bound, and no guarantee on other inputs.

Consequently a monotone failing trace rejects terminal-purity proofs using
only the tested bounds, routing, conservation and prefix dominance. It does
not reject a particular universal provider or a richer reachability invariant.

Passing samples are not a worst-case upper bound. The initial root is exact
by default as an optimistic diagnostic; `--approx-root` removes that assumption.
Whole-up bags retain their full word, including odd cardinalities.
