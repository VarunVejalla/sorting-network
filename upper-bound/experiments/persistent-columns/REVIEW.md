# Independent paper review, 2026-10-20

Fresh-context reviewer `/root/persistent_review` read PLAN, FRINGE-WITNESS,
the two scripts, and relevant promoted R1 material. No edits or Lean build.
The reviewer independently reproduced the model output and checked the
following derived mathematics. This is not kernel verification.

## Valid aligned algebra; invalid small-C uniform inference

For a fixed input independent of the sampled row permutations, the
hypergeometric variance bound, profile-dispersion identity, row-aligned cut
bound and conditional fixed-point exponent check. They do not provide one
fixed schedule that works for all input profiles chosen after that schedule.

In fact the proposed small-C uniform recurrence is false. Take k children
with d*n_v source columns each, where n_v is even. Fix half the receiving
columns S. In each child set height1 precisely for source columns whose
row0 goes to S, and height0 for all others. Set other sources' heights to0.
Then every child has mean height1/2 and dispersion1/2. All zeros are in its
first low-port row. Receiving heights are L=k*d on S and0 outside, so the
receiving dispersion is L/2. Therefore

    e_out <= C*sqrt(D*max_s e_s)

for ALL sorted profiles would require C>=L/sqrt(2D). At the displayed
(3,4,2) point, L=512,D=512.25, hence C>=15.9961 (or16 if only participating
children are counted in D). This is a deterministic obstruction for every
fixed receive routing of the specified kind, not a loose probability bound.

Scope: the witness does not refute a fixed-radius closure theorem at E>=L/2,
nor prove actual global reachability. Those would be different hypotheses
and proofs; the pointwise small-C recurrence cannot supply them.

## Rare-fringe obstruction

The t-row forcing construction in FRINGE-WITNESS is valid if the low port
contains t rows. At the apparent295.167 point it has d=64,f=3968,t=124 and
forces escapes/H>=1/125, versus eps_F~3.125e-8: roughly256000 times too
large. With enough columns the supported-cohort and aggregate-dispersion
promises also hold. Scalar outsider P has no evident mechanism excluding
these finite-mass profiles at unbounded capacity, but a complete embedding
into a reachable R1 execution has not been proved.

## Required wording correction and decision

The script searches a finite grid using sufficient conditional estimates.
It is not a necessary lower bound on any actual network depth. Its reported
minimum must not be described as a universal floor. This correction is applied.

No simple salvage with a priced <=300 proof emerged. The small-C all-profile
route is rejected and the broader representation is parked. Reopen only with
a distinct fixed-radius/reachable-state theorem and a rare-fringe invariant,
not another unsupported parameter sweep. No Lean should be written for the
refuted recurrence.
