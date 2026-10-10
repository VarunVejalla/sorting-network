# Fringe size f for Property F: one round, and what two rounds must prove

Derived and unaudited. No Lean touched. Scripts in this folder: `fmin.py` (one-round f_min), `tworound.py` (small-rank f_min and heuristic large-rank margin), `run1/2/3.py` (tables). Everything below marked HEURISTIC is a first-moment estimate, not a proof.

## 0. Reconstructed one-round inequality system

Event used by `round_event`/`badSetF`: with g = f/2 (Lean's `f/2`), tops t_c = (c_c - g)_+, escapes E_f <= sum_{v in S}(H_v - (f-g)) where H_v counts marks from rows above g. For j' = J*E (J = 1/eps), E = eps*j', per-E failure is `tops_count * G1(b) <= (90/89)*x^E`, and (with u = j/(f n), theta = g/f)

ln x = [2+2ln(g+1)-ln f-ln u]/(eps(g+1)) + [1+ln(1-theta)-ln eps-ln u]/(f-g) + 1 + ln u - ln(1-theta)

(theta = 1/2 is `xval`, reproduced to 4 digits against the other agent's 2.496e9 / 7.28e9). x is increasing in u, so the sup is at u_max. Total failure = 1.025*x/(1-x) must be < 0.49 (pigeonhole `exists_and_flip` with the 1/100 from Lemma 6.1), i.e. x <= 0.3223.

## 1. Which constants are artifacts (one round)

| Constant | Verdict | Effect on f_min |
|---|---|---|
| J = 1/eps = 86e6 | FORCED: the escape count is an integer, so the grid E -> j'=E/eps is the natural one. A finer or coarser grid does not help. Only its side effect is an artifact: j' can overshoot delta f n by J, which `Lemma62Params` absorbs by loosening 128/4095 to 1/31. Capping j' = min(EJ, delta f n) removes it (needs eps_eff = E/j' >= eps in G1). | 5% |
| -ln eps <= 86e6 (`heps`) | ARTIFACT (true value 18.3). | 4% on f; also `key_right` then needs f >~ 1.6e8, harmless at 8.5e9 but binding below 1e9 |
| x <= 8/25 for every E | MAIN ARTIFACT. Replacing sum_E x_E^E by a geometric series wastes everything: x_E is tiny for small E and the worst n is n=16 (K=ceil(eps*delta*f*n) small). Exact sum over E, worst n >= 16 | factor 2.7 |
| 90/89, (1+e^-5)/(1-e^-5) | slack, <3% in the budget, ~0.3% in f | negligible |
| g = f/2 | free parameter (theta); optimum 0.42 (sup form) / 0.6 (sum form) | 5% / 2% |
| delta_F = 128/4095 | tied to the scheduler: mu = min(nu/(A k^2), (delta_F/2)(A nu k-1)/(A k)^2) has both terms equal at 128/4095, so smaller delta_F shrinks mu | see table |
| the entropy term ~ 2 ln f/(eps f) | FORCED for this proof structure (union over tops profiles). | gives eps*f >~ 20-30 at best |

### f_min (eps = 1/86e6, delta = 128/4095 unless stated)

| Variant | f_min |
|---|---|
| Lean as written (`xval` with 86e6 and u<=1/31, x<=0.3223) | 7.87e9 (hypothesis used: 8.5e9) |
| exact -ln eps, u = 1/31 | 7.57e9 |
| exact -ln eps, u = delta | 7.20e9 |
| + best theta (0.42) | 6.85e9 |
| only x < 1 (necessary for any geometric closure) | 2.50e9 (theta .59: 2.41e9) |
| exact sum over E, worst n=16, cap j', theta=.5 / .6 | 2.65e9 / 2.60e9 |

(eps^-1, delta_F) pairs, theta = .5, columns "x<=.3223 sup form" and "exact sum <= .49":

| 1/eps | delta | f_sup | eps f | f_sum | eps f |
|---|---|---|---|---|---|
| 8.6e7 | .0313 | 7.2e9 | 84 | 2.65e9 | 31 |
| 8.6e7 | .02 | 4.2e9 | 49 | 2.26e9 | 26 |
| 8.6e7 | .01 | 2.6e9 | 30 | 1.92e9 | 22 |
| 1e7 | .0313 | 7.7e8 | 77 | 2.8e8 | 28 |
| 1e6 | .0313 | 6.9e7 | 69 | 2.6e7 | 26 |

Reading: f_min ~ (20..30)/eps for one round with this structure. The hard floor from the adversary (re-derived, correct): E >= f from mass f(2f+1) forces eps(2f+1) > 1, i.e. f >= 43,000,000 for eps=1/86e6 (strictness gives exactly (J-1)/2 -> 43e6). So one round can at best go from 8.5e9 to roughly 2.6e9 (provable by small edits), never below 4.3e7, realistically not below ~1e9. Scheduler (item 4): the proof-mode model (`chvatal_param_search.py --mode proof`) already lets eps_F float with f: (6,12,6) gives L=58 (f=8.6e9, slope 1711); f = m 2^-25 at f=2.6e9 means m = 2^56.3, and the bulk condition (4.2) pins L ~ 58 anyway (coordinator's finding; I did not rerun). So single-round F improvements buy at most the 1770 -> ~1711 already in the model.

## 2. Two rounds: the exact contract at f ~ 2^17

NodeSpec: for all x, all 0<j<=Jmax=floor(delta f n) (up = 2fn), the number of the j largest keys outside the last f rows (resp. j smallest outside the first f rows) is < eps*j, eps=1/86e6. In heights: after sort, scramble1, sort, scramble2, sort, E_final = sum_v (z'_v - f)_+ < eps*j.

Deterministic facts (all easy):
1. Row scramble then ascending column sort never increases the number of marks in a row prefix, so E_final <= E_f(z) of round 1. Round 2 is only useful when round 1 is NOT already good.
2. z'_v <= max_c z_c (v receives at most one cell per row, and only rows 1..z_max are nonempty), and z'_v <= g + H_v with H_v = hits from intermediate rows above g.
3. Mass conservation sum_c z_c = j; j<=f gives no escape at all.

Small ranks, j <= J: zero escapes. Sufficient: round 1 satisfies E_g(z) < eta j for all j <= min(J, delta f n) with eta=(f-g)/J (then max z <= g+E_g < f; zero escapes through both rounds). This is the ONE-round machinery with (f,eps,delta) -> (g, eta, delta f/g). Computed (`tworound.py`, exact sum, worst n over a grid including 16..1e8, budget 0.49):

| quantity | value |
|---|---|
| smallest f, g = 0.6 f | 9.4e4 (budget .3: 9.6e4) |
| same with the crude sup form x<=.3223 | 2.0e5 (g = .8 f) |
| at f = 131072, g=.6f: total failure fraction | 0.017 |

So small ranks at f = 2^17 are supported with a lot of room (needs: new g,eta parameters in `Lemma62Params`/`xval`, the sum-over-E form, and eps(2g+1) > 1-type adversary check: eta*2g ~ 80 >> 1). Caveat: grid of n, not all n; the rounding with cap must be re-proved.

Large ranks, j > J (exist only for n > J/(delta f) ~ 2.1e4): the remaining probability obligation. Both scrambles random; for every input of mass j with E >= eps j escapes. Single-round alone is impossible (adversary mass f(2f+1)~3.4e10, ratio 1/(2f+1) = 3.8e-6 >> eps, reachable for n >= 8e6). Two-round necessary condition (no-collision adversary, column with f+e marks, chain of demanded cells pulled back through both rounds, mass ~ (f+e)^3/6, escapes e): eps >= 0.89/f^2 at e = f/2, i.e. f >= 8.7e3 (8031 in the other note with k=2f). At f = 2^17: eps f^2 = 200, margin ~220x. Collisions (n < f^2) make the pulled-back cost n*f-ish, far above delta f n, so only help the proof.

Obligation (precise): for fixed S (s columns, excess e_v), minimal witness = chain of demanded intermediate cells {(r, sigma2_r^-1(v)) : r > g}; each demanded cell (g+i, c) requires >= i hits at column c from the input marks above g; input has k <= j0/(g+1) top columns with j0 = min(delta f n, E/eps). Then

P_bad <= sum_{s,e} C(n,s) * [#tops profiles of mass j0] * prod_{demanded columns} (e*mu0/i)^i,  mu0 = j0/n,

union both orientations, total < 0.49 uniformly in n >= 16 and all E. Key new term versus one round: the gain is quadratic in f (sum_{i<=A} i ln(i/(e mu0)), A = f+e-g) while entropy is linear in E/(eps g), so the margin improves like eps f^2.

HEURISTIC numeric check (`tworound.py::margin`, ratio gain/entropy over e in [1,1e6], s/n in [1e-20,1e-3], worst over grid, g = f/2 unless stated):

| f | 2^14 | 2^15 | 3*2^14 | 2^16 | 3*2^15 | 2^17 | 2^18 |
|---|---|---|---|---|---|---|---|
| min ratio | 0.66 | 0.87 | 2.4 | 5.2 | 7.3 | 15 | 98 |

Ratio >= 1 holds from ~2^15 (borderline), comfortably from 2^16; 2^17 gives 15x slack for the leading-order exponent. These numbers ignore: (a) the product bound over distinct demanded columns needs negative association (permutation distributions are NA; unproved in Lean), (b) union over which rows carry the hits (checked to cost <= 2^(eps*mu0 e) ~ negligible, not formalised), (c) collisions among sigma2 preimages when n is not >> f (deterministically excluded by sum z_c = j: n*A/2 > j; needs a clean argument for 2e4 < n < 1e9), (d) the 1.025/geometric constants, (e) the contract's two sides and the 1/100 B-event budget, (f) rounding. It also assumes the first round is not required to satisfy anything beyond the input-tops union (so all-input quantifier is handled by union over tops, as in one round).

## 3. Verdict and plan

Belief: the full contract at f ~ 2^17 (131040 for the scheduler template) is true and provable with this two-round union bound, but I have NOT verified the large-rank bound beyond a leading-order exponent; honest smallest f supported by my route:
- small ranks: f >= ~1e5 (g=.6f), robustly at 2^17;
- large ranks: leading-order margin >=1 at ~2^15-2^16, but with the unverified constants/lower-order terms I would not claim below f ~ 2^17 = 131072 (the 131040 template is just under it: margin ~15 so likely fine, but not 'checked').

Lean modules touched (estimates): Lemma62Ratio (Lemma62Params: n-range and f lower bound, g,eta general; ~100 lines), Lemma62Numerics (new xval with exact logs, sum-over-E closure; ~250 new), Lemma62Round (cap rounding, parametrised J; ~80), Lemma62FailE/TopsCount/TopsClosed (g, eta in place of f/2, eps; ~150 edits), FlipSpec/GeneralParams (hfbig, delta; ~30), GeometryScale/NodeGeom (85e8 -> new f bound, ratio 4095/2^37 gives f = 131040 at m=2^42; ~40), plus NEW: two-round witness lemma (NA tail bound, pullback cost, union; ~800-1500 lines) and the deterministic monotonicity/relabeling facts (~200). The new probabilistic lemma is the bulk of the work; the small-rank part is a re-parametrisation (~400 lines).

Unverified: all numerics are floating point; sum form uses a finite grid of n; no check that Lean's tops-count bound survives with k <= j/(g+1) and non-half g.
