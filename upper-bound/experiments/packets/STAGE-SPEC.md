# UB-25 candidate stage and terminal gate

Status: specification of the best current candidate, not a proved network
stage. The missing physical output-to-next-stage map is called out explicitly;
until it is supplied, the pseudocode below is a packet-level proposal and
cannot be iterated as a sorting network.

## Stage interface

At an interior `flowA7` level, the input is the actual physical register
partition, together with a Boolean threshold value on each wire. The intended
invariant is that each 64-wire packet is physically sorted and has a target
rank interval. A 4096-wire macroblock is 64 consecutive such packets and is
physically sorted in its canonical support order. Targets are the suffix
counts of the corresponding rank intervals. Keep the threshold arbitrary;
the stage must work simultaneously for every Boolean threshold to imply a
sort by the zero-one principle.

The selector decomposition gives each receiver at most 129 regular streams
(the parent stream and two streams per child) and at most 65 endpoint packets.
Each regular stream is divided into consecutive full 4096-wire blocks and a
residue of fewer than 4096 wires. Pool residues and endpoint packets; the
current incidence bound puts this pool below 8192 64-wire packets, hence it
can be grouped into at most 128 full macroblocks plus a residual group. The
exact wire partition is checked, but this bound does not say that the pooled
packets are rank-aligned or profile-balanced.

## Candidate transition

For each level, with the actual active receiver set and actual packet IDs:

```text
STAGE(state):
  1. Advance through the actual scheduled flowA7 port transfer. This is wire
     routing and costs zero comparator layers. The separate checked
     `flowA7_sourcePortRepairStage` costs at most six layers per ordinary
     round when used to repair half-misaligned 64-wire packet boundaries.
     Whether the 78-layer full-block sort later in this stage makes that
     repair unnecessary is unresolved; do not charge it as zero without the
     physical rank-map proof. Retain the 129 regular streams, endpoint
     packets, and each stream's <4096-wire residue as distinct, physically
     supported objects.

  2. Group every regular stream's consecutive 4096-wire blocks by block
     index. Group the pooled endpoint/residue packets in their actual physical
     order into 4096-wire supports, retaining the final partial group.

  3. Reassemble each full macroblock by sorting its 64 constituent 64-wire
     runs with the 57-layer merge tree. The equivalent full-support physical
     bitonic sort costs 78 layers and yields canonical support order. Use one
     of these alternatives, not both; reserve 78 layers in the conservative
     budget. Preserve exact rank-cell support labels.

  4. Local mixing: for each equal block index, regard the at most 129 regular
     streams and one full exception stream as a cohort of size c <= 130.
     Apply the checked 15-round perfect-matching cycle for that c. For every
     matched pair, use the 4096-wire merge-and-deal compare-splitter (13 binary
     layers); carry the two output supports as labeled packet IDs.
     Do not discard unmatched tail packets: the currently screened cycle does
     not cover their target-error effect.

  5. Global mixing (needed for coarse modes): apply R rounds of disjoint pairs
     to the macroblock IDs, with one 13-layer compare-splitter per matched
     pair per round; leave one packet unmatched in a round when the count is
     odd. The proposed sub-200 budget takes R=9. The matching family must be
     fixed and specified for every size; abstract existence and finite random
     screens do not specify one.

  6. Reblock the resulting physical supports into exactly the packet-ID
     partition expected by the next flowA7 level. Explicitly route or repair
     wires whenever a resulting support is not the required next rank interval;
     charge all such comparators. Then define the next target profile from
     those exact physical supports, not from a presumed average.

  7. At startup, bottom/top frontiers, incomplete macroblocks, and the final
     stage, use an explicitly specified frontier/cleanup network and include
     its depth. The current work has local frontier error bounds but no such
     closed schedule.
```

This is a complete list of the intended operations and their required data,
but steps 4-7 do not currently compose into a defined physical transition:
step 4/5 output packet supports have not been mapped to the next `flowA7`
rank-cell supports, and step 7 has no specified cleanup. There is no valid
implementation choice to fill in from the present proofs. In particular,
support equality for a 4096 block does not imply an order-preserving map, and
arbitrary wire renaming can reverse comparators. The first missing research
object is therefore an explicit map

```text
nextSlot(level, outputPacketID, localWire) -> physical wire
```

whose fibers are exactly the next stage's required supports, together with a
proof of its rank-target update and a comparator-depth charge if it is not an
order-preserving embedding. Until that object is defined, a scaled simulation
would simulate an invented scheduler rather than this construction.

## Depth ledger and honest coefficient

The local cycle costs `15 * 13 = 195` layers per stage, and the physical
4096-wire block sort costs 78 layers. Nine global rounds cost `9 * 13 = 117`
layers. Thus the packet-processing subtotal is 390 layers. If this entire
packet transition fits into one ordinary round of the unchanged flow schedule,
its arithmetic coefficient is 195. The original flow timing has three
ordinary rounds per scale-depth increment: `ordinaryRounds(d) = 3*d - 21`
while `log2(64^d) = 6*d`, so two bits per ordinary round is exact, up to
additive endpoints. The unproved assumption is that this full packet
transition fits in each such round. If the six-layer port repair is
required every ordinary round, it adds six layers per round, or 3 to this
coefficient; if the packet redesign changes the flow schedule, its progress
rate must be derived again. This is not a bound: output routing, incomplete
tails, frontiers, startup, and terminal cleanup are unpriced, and the global
matching family remains unspecified. The two-scale recurrence needs the
unproved coarse/fine cross-map bounds of at most `383/1000` in the required
compatible decomposition.

As a conservative conditional comparison, directly composing the checked
factor-65 flow estimate with the abstract global contraction requires 16
global rounds. Together with 15 local rounds and a 78-layer block sort, that
is `(15*13 + 16*13 + 78)/2 = 240.5` if that full packet transition fits one
ordinary round, or 243.5 if the six-layer repair is required per ordinary
round.
This is the current conservative cost screen, not an established limsup
coefficient. The 136.5 local-only subtotal is not viable because
`flowA7` alone does not contract coarse modes. No unconditional improved
coefficient is currently proved; the accepted one remains 1419.

## Terminal criterion

The exact terminal condition is: for every Boolean threshold input, every
adjacent output pair is ordered (`out[i] <= out[i+1]`). By the zero-one
principle, proving this for all Boolean inputs proves that the output is
sorted for arbitrary inputs. A sufficient stronger condition is that every
wire has its exact rank-threshold value at termination, equivalently every
threshold has zero misplaced ones.

The current candidate does not meet or imply that condition. The proposed
centered profile recurrence has a conditional steady-state error around
`0.00639`, not zero. Aggregate L1/L2 control does not rule out even one
misplaced value at a rare rank, and the singleton-tail screen shows that
uniform random compare-split rounds do not repair such a value in bounded
rounds as the packet count grows. No final oblivious cleanup network, outsider
bound accepted by such a cleanup, or rare-rank mechanism has been specified
and depthed.

The proposed rare-key probe has a precise but narrow outcome. For the checked
15-round local cycle on at most 130 streams, `rho <= 1/16`, so

```text
max_j |x_out[j] - H/c| <= H/16 + 15/2.
```

An eight-wire fringe around the target count is certified by this estimate
only when `H <= 8`. Thus a singleton is harmless if packets are already
rank-aligned, but the bound does not control larger rare cohorts. For a fixed
nine-round global matching product, each output depends on at most `2^9`
input packet IDs. If `C > 2^9`, this support bound forces its centered spectral
norm to satisfy

```text
rho >= sqrt((C/2^9 - 1)/(C - 1)),
```

which tends to `1/sqrt(512)`. The corresponding `rho*H + 9/2` estimate cannot
certify a fixed eight-wire fringe for unbounded `H`. This rules out the
proposed fixed-round spectral estimate as a uniform terminal proof; it does
not rule out a rank-aware multiscale schedule or a stronger count invariant.

Therefore the terminal gate is presently **NO-GO for the current candidate**:
before adding routing Lean, specify either (a) a rare-rank-safe cleanup whose
depth is included and whose hypotheses follow from the stage recurrence, or
(b) a pointwise outsider/dirty-interval invariant that contracts to zero and
implies the Boolean terminal condition. If neither is found, the packet
recurrence does not yield a sorting theorem, regardless of its conditional
195 coefficient.
