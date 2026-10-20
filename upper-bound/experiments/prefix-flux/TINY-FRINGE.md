# A small fringe at a very small supported rank fraction

2026-10-20. Codex (GPT-6). Independent hand review and interval reproduction:
`/root/mass_tail_review`. Probability-envelope check plus reviewed extension
argument; NOT an instantiation of the existing Lean provider or a global bound.

The F2 argument admits a different local price tradeoff when the supported
rank fraction can be made very small:

    f13, g1=5, g2=11, c=1/2, b=5, J17, delta=10^-100.

The intended escape fraction is1/17 for cohorts j<=delta*f*n. The older
scalar invariant couples this extremely small allowance to bulk precision,
which destroys any gain. This point is useful only if a different global
invariant decouples those requirements. Do not retune the old invariant with it.

## Keep the first integer support cap exact

F2ROUND uses kappa_E=ceil(cE). The numerical certificate usually replaces it
by cE+1. At E2 this changes the true value1 to2. For f13 it removes the
negative ln(delta) coefficient and makes the probability bound fail even
though delta is tiny. The optional `exact_small=True` refinement now retains
ceil(2c) at E2, starts the generic closed geometric sum at E3 and adds E2
exactly once. Its cubic moment is the ordinary shifted geometric identity.
All other estimates and the default behavior are preserved.

Outward interval checks give the following log upper bounds (both
orientations already included):

| route | first-scramble failure | second-scramble failure |
|---|---:|---:|
| per-E | -1022.41 | -90.4009 |
| closed | -958.931 | -84.5837 |

Reproduce quietly with `python upper-bound/experiments/prefix-flux/tiny_fringe_certificate.py`.
These are probability-envelope values, not kernel certificates.

## Current formal precondition and its reviewed extension

`F2Pre.hf16` requires1<=delta*f*16, which this point fails. The old Python
script did not check that API guard; it now reports `current_hf16` explicitly.
Thus a passing numerical check must not be described as a ready checked provider.

Source audit found direct uses in `F2DR1.jE_factsd` and
`F2DSR.SRd_fail_card_le`, solely to obtain positive admissible rank. The
reviewed replacement splits by the actual dimension's jmax=floor(delta*f*n):

- If jmax=0, SR/R1 input profiles have mass zero and their bad events are
  empty. Restricted R2nd has no admissible E>=2 because (E-1)J>0.
- If jmax>0,1<=delta*f*n follows directly from the floor definition,
  replacing the positivity supplied by hf16.
- For admissible R2nd ranks, (E-1)J<=jmax itself gives the lower dimension
  n>=(E-1)J/(delta*f) used in the probability envelope.

Unrestricted R2d is not vacuous in the first case. The extension must retain
the current restricted R2nd interface throughout. That split and the exact
E2 numerical bound still require formal proof if the whole candidate succeeds.

## Conditional shifted-tail interface

The following deterministic reduction is a new unaudited derivation;
the independent review above covers the certificate and guard extension.

For sorted rectangular columns c and base row b, write d=(c-b)_+.
Pointwise c<=b+d. A full marked baseline of b rows is preserved by row
scrambles and column sorts. Removing it reduces the two-round process to
the same process on the remaining rows. Monotonicity then gives, conditional
on the corresponding shifted F2 witness,

    sum(d)<=delta*f*n  => escape beyond row(b+f)<sum(d)/J

for positive sum(d); at zero mass escape is zero. Reflection handles holes.
This allows a positional band plus rare far spill, rather than charging all
central disagreement as rare extreme mass. A common witness for all base
rows needs a finite union; up to4096 bases fits comfortably within the above
probability margins. Ragged/padded transfers and the global width recurrence
are separate obligations.

Returning child bands can widen sharply relative to a shrinking parent
capacity. The shifted local lemma alone does not close that recurrence.
Do not treat it as a completed invariant or claim292.5 from it.
