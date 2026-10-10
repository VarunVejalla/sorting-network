# Barrier of the existing lower-bound method

## Result and scope

We can exhibit an abstract, fractional height evolution compatible with **all
prefix counting constraints**, at the same leading depth coefficient
`1/(1-log_2(phi)) = 3.270559454...`. This includes the full weighted binomial
inequalities, not just the single terms used in our sorting proof.

Consequently, recombining these inequalities or restoring their discarded terms
cannot yield a larger leading coefficient. This establishes a barrier for that
inequality system and the fractional height relaxation described below.

It does **not** establish a barrier for every argument using certificate heights.
The population can also be rounded to integral equal-height pairings without
violating any of these prefix counts (see §4). It does not establish the required
locations of low-height wires, actual selection correctness, or sorting.
Those missing realizability conditions are where a stronger bound might enter.

Source context: [Kahale et al., §5, Lemma 5.1 and Theorem 6](https://research.engineering.nyu.edu/~suel/papers/size.pdf).
The saturation and witnesses below are our analysis of the formalized method.

## 1. Every local potential can be saturated simultaneously

The scalar update is

```text
(a,b) -> (min(a,b), max(a,b)+1).
```

If both inputs have height `a`, the outputs have heights `a` and `a+1`.
For our potential `P`, its defining recurrence is

```text
P(r+1,L,a) = P(r,L,a) + P(r,L,a+1).
```

Thus the factor-two pair inequality is an equality, for every `r` and `L`,
when the inputs have equal heights. There is no universally smaller factor
available in that local inequality.

Now allow fractional populations and pair all mass at each height with mass
of the same height. Half stays and half rises. Starting with total mass `n`
at height zero, after `t` layers the population at height `i` is

\[
m_t(i)=n\,2^{-t}\binom ti.
\]

Pascal's identity verifies the recurrence. Total mass remains `n`, and the
same evolution saturates every potential used in the existing argument.
This relaxation ignores wire positions, certificate identities, and integrality.

## 2. The same evolution satisfies every prefix constraint

For total depth `d`, remove a suffix of length `s` and put `t=d-s`.
Approximate selection implies that at most `2^(s+1)` prefix wires can have
height at most `s`. The fractional evolution satisfies this necessary condition
if

\[
nB_{d,s}\le2^{d+1},\qquad
B_{d,s}=\sum_{i=0}^{s}\binom{d-s}{i}.
\]

The full weighted potential inequality is

\[
nA_{d,s}\le2^{d+1}(s+1),\qquad
A_{d,s}=\sum_{i=0}^{s}(s+1-i)\binom{d-s}{i}.
\]

Choose the integer total mass

\[
N_d=\left\lfloor\frac{2^d}{(d+1)F_{d+1}}\right\rfloor.
\]

For `i <= s <= d`, the Fibonacci antidiagonal identity gives

\[
\binom{d-s}{i}\le F_{d-s+i+1}\le F_{d+1}.
\]

Hence

\[
B_{d,s}\le(s+1)F_{d+1}\le(d+1)F_{d+1},
\quad N_dB_{d,s}\le2^d,
\]

and `A_(d,s) <= (s+1) B_(d,s)` gives every full weighted constraint as well.
This is one population evolution satisfying all suffix choices simultaneously,
rather than different hypothetical witnesses for different choices of `s`.

## 3. Why its leading coefficient is exactly the existing one

The checked Fibonacci estimates give

\[
\varphi^{d-1}\le F_{d+1}\le\varphi^d.
\]

The expression inside the floor defining `N_d` therefore lies between
`(2/phi)^d/(d+1)` and `phi*(2/phi)^d/(d+1)`. It tends to infinity, so flooring
does not affect its exponential growth rate. Consequently

\[
\log_2 N_d=d(1-\log_2\varphi)-\log_2(d+1)+O(1),
\qquad
\frac{d}{\log_2 N_d}\longrightarrow
\frac1{1-\log_2\varphi}.
\]

Any purported stronger leading lower bound derived only from the above
inequalities would also apply to `N_d`, contradicting this growth rate.

The critical suffix proportion in the binomial exponent is
`s/d = (1-1/sqrt(5))/2`, approximately `0.2763932`. It corresponds to
`s/log_2(N_d) -> 0.9039604`. This identifies the scale on which a new
constraint must improve the argument; eliminating a few exceptional extreme
wires alone need not change that exponent.

## 4. Integrality alone does not break the barrier

At each height, pair as many equal-height wires as possible and leave the
unpaired wire idle when the population is odd. This is an integral histogram
evolution; every pair uses the actual scalar comparator update.

Write `M_t(h)` for the level population and `C_t(s)` for the population at
heights at most `s`. With `C_t(-1)=0`, the exact update is

\[
C_{t+1}(s)=\tfrac12(C_t(s)+C_t(s-1))
 +\tfrac12(M_t(s)\bmod2).
\]

Indeed, precisely `floor(M_t(s)/2)` wires cross from height `s` to `s+1`.
The ideal binomial cumulative population `I_t(s)` satisfies the same recurrence
without the parity term. Therefore the error `E_t(s)=C_t(s)-I_t(s)` satisfies

\[
E_{t+1}(s)=\tfrac12(E_t(s)+E_t(s-1))
 +\tfrac12(M_t(s)\bmod2).
\]

Starting with zero error, induction gives `0 <= E_t(s) <= s+1` for every
`t,s`. For `s=0`, use `E_t(-1)=0`; for `s>=1`, the upper bound follows from
`((s+1)+s)/2+1/2=s+1`.

For total population `N_d` and prefix `t=d-s`, §2 gives
`I_t(s) <= 2^s`. Thus

\[
C_{d-s}(s)\le2^s+s+1\le2^{s+1}.
\]

So the integral histogram satisfies every necessary prefix counting condition,
simultaneously. Its low-height deficit also satisfies the required weighted
budget, since that deficit is at most `(s+1) C_(d-s)(s)`.

These pairings can be performed on actual labelled wires: group wires by height,
pair within each group, and orient each comparator by its wire indices. The
histogram is independent of that orientation. This establishes the scalar
histogram construction; it does not establish that low-height wires land in
the boundary region required by approximate selection.

The rounding argument is a mathematical derivation here, not yet a Lean theorem.
[`scripts/kahale_height_barrier.py`](../lower-bound/experiments/scripts/kahale_height_barrier.py) implements
the recurrence and checks the rounding bounds and all prefix counts using exact
integer arithmetic for any requested finite depth.

## 5. What has been formalized

[`AKS/Kahale/MethodBarrier.lean`](../lower-bound/experiments/AKS/Kahale/MethodBarrier.lean) proves:

- exact local saturation for equal heights;
- the individual binomial/Fibonacci bound;
- a separate integer witness `scalarWitness d = floor(2^(d+1)/F_(d+1))`
  satisfying every extracted single-term constraint;
- `F_(d+1) <= phi^d`;
- the witness `relaxedArity d = N_d` satisfies every prefix low-height count
  and every full weighted binomial constraint.

These finite statements are kernel checked with `lake build AKS.Kahale.MethodBarrier`.
The fractional evolution and the asymptotic calculation above are mathematical
derivations documented here; their distribution and limit are not additional
Lean theorems in this module. No sorting-network existence is claimed.

## 6. The next useful obstruction

**Update:** [the positional construction](kahale-positional-barrier.md) closes
the positional gap for the zero-height condition considered here. Splitting
contiguous equal-height blocks across their halves preserves a sorted height
profile and realizes all required boundary positions. The discussion below
records the question that led to that construction; positional obstruction for
this particular condition is now ruled out. Actual threshold-certificate
requirements remain a research target.

The next question is whether a single schedule can put its low-height wires in
the **required boundary region at every critical prefix**, while maintaining
compatibility of their actual certificates. Integral histogram counts alone
are compatible with the existing exponential rate.

The comparator orientation fixes which output inherits the lower height.
A useful result must show that positional constraints, or certificate
compatibility across wires, cause an **exponential** loss relative to the
relaxed population. A polynomial loss would leave the coefficient unchanged.

Investigate the positional height process next. If it can satisfy the boundary
requirements at this rate, tracking certificate identities and joint zero/one
requirements becomes the next target. We have not established that positional
construction or an obstruction to it.
