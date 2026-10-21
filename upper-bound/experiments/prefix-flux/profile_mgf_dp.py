#!/usr/bin/env python3
"""Finite DP for the profile-weighted row-scramble moment sum.

Exploratory only. It sums Chernoff MGF weights over all labeled column-height
profiles instead of separating profile count from the worst profile MGF.
"""
import argparse
import math
from math import comb


def row_mgf(n, subset, marked, theta):
    """MGF of the intersection of a fixed subset and a uniform marked set."""
    lo = max(0, marked - (n - subset))
    hi = min(marked, subset)
    denom = comb(n, marked)
    return sum(
        comb(subset, x) * comb(n - subset, marked - x)
        * math.exp(theta * x) / denom
        for x in range(lo, hi + 1)
    )


def weighted_profile_sum(rows, columns, mass_cap, subset, theta):
    """Sum_c prod_r MGF(row_marks_r(c)) over labeled height vectors c."""
    max_mass = min(rows * columns, mass_cap)
    # dp[previous row population][mass so far]; binomial transitions select
    # nested labeled subsets and thus count each column-height vector once.
    dp = {(columns, 0): 1.0}
    mgfs = [row_mgf(columns, subset, u, theta)
            for u in range(columns + 1)]
    for _ in range(rows):
        nxt = {}
        for (previous, mass), weight in dp.items():
            for current in range(previous + 1):
                new_mass = mass + current
                if new_mass > max_mass:
                    break
                key = (current, new_mass)
                nxt[key] = nxt.get(key, 0.0) + (
                    weight * comb(previous, current) * mgfs[current]
                )
        dp = nxt
    return sum(dp.values())


def enumerate_profile_sum(rows, columns, mass_cap, subset, theta):
    """Independent check by direct profile enumeration for small dimensions."""
    from itertools import combinations_with_replacement
    from collections import Counter
    total = 0.0
    for heights in combinations_with_replacement(range(rows + 1), columns):
        if sum(heights) > mass_cap:
            continue
        multiplicity = math.factorial(columns)
        for count in Counter(heights).values():
            multiplicity //= math.factorial(count)
        row_marks = [sum(h > r for h in heights) for r in range(rows)]
        product = math.prod(row_mgf(columns, subset, u, theta)
                            for u in row_marks)
        total += multiplicity * product
    return total


def separated_log_bound(i, subset, columns, theta):
    p = subset / columns
    g = (i + 1) * math.log(i + 1) - i * math.log(i)
    return columns * (g + i * math.log1p(p * math.expm1(theta)))


def weighted_mgf_escape(rows, columns, mass_class, fringe, eta=1e-3):
    """Numerical finite Chernoff/union screen using the exact profile sum."""
    from moderate_tail import bound
    mass_cap = min(rows * columns, mass_class * columns)
    thetas = [j / 20 for j in range(1, 401)]
    per_subset = {}
    for subset in range(1, columns + 1):
        per_subset[subset] = []
        for theta in thetas:
            z = weighted_profile_sum(
                rows, columns, mass_cap, subset, theta
            )
            per_subset[subset].append((theta, math.log(z) +
                                       math.log(comb(columns, subset))))

    union_escape = mass_cap
    for escape in range(mass_cap + 1):
        per_size_bounds = []
        for subset in range(1, columns + 1):
            best_log = min(log_mgf - theta * (escape + fringe * subset)
                           for theta, log_mgf in per_subset[subset])
            per_size_bounds.append(math.exp(min(700, best_log)))
        if min(1.0, 2 * sum(per_size_bounds)) <= eta:
            union_escape = escape
            break
    analytic, theta, p0 = bound(
        mass_class, fringe, columns, 1, baseline_factor=1
    )
    return dict(union_mgf_escape=union_escape,
                analytic_fixed_cap=columns * analytic,
                analytic_theta=theta, analytic_p0=p0)


def hypergeom_mgf_rate(marked_fraction, subset_fraction, theta):
    """Limit n^-1 log E exp(theta X) for Hypergeom(n,an,pn)."""
    a, p = marked_fraction, subset_fraction
    if a <= 0:
        return 0.0
    if a < 1e-12:
        return a * math.log1p(p * math.expm1(theta))
    if a >= 1 - 1e-12:
        return p * theta
    A = math.exp(theta)
    B = p * A + 1 - p - a * (A + 1)
    C = A * (1 - a)
    disc = math.sqrt(B * B + 4 * C * a)
    t = math.log(2 * a / (B + disc))
    softplus = lambda z: max(z, 0) + math.log1p(math.exp(-abs(z)))
    entropy = lambda x: -x * math.log(x) - (1 - x) * math.log1p(-x)
    return (p * softplus(t + theta) + (1 - p) * softplus(t) -
            a * t - entropy(a))


def hypergeom_rate_derivative(marked_fraction, subset_fraction, theta):
    """Derivative in a, by the envelope theorem at the saddlepoint."""
    a, p = marked_fraction, subset_fraction
    if a <= 0 or a >= 1 - 1e-12:
        return 0.0
    if a < 1e-12:
        return math.log1p(p * math.expm1(theta))
    A = math.exp(theta)
    B = p * A + 1 - p - a * (A + 1)
    C = A * (1 - a)
    t = math.log(2 * a / (B + math.sqrt(B * B + 4 * C * a)))
    return math.log(a / (1 - a)) - t


def hypergeom_rate_derivative_stable(marked_fraction, subset_fraction, theta):
    """Stable derivative in a, using a bracketed saddle solve."""
    a, p = marked_fraction, subset_fraction
    if a <= 0:
        return math.log1p(p * math.expm1(theta))
    if a >= 1:
        return -math.log1p(p * math.expm1(-theta))
    logit = math.log(a) - math.log1p(-a)
    def logistic(x):
        if x >= 0:
            return 1 / (1 + math.exp(-x))
        e = math.exp(x)
        return e / (1 + e)
    def saddle(t):
        return p * logistic(t + theta) + (1 - p) * logistic(t) - a
    lo, hi = logit - theta, logit
    for _ in range(64):
        mid = (lo + hi) / 2
        if saddle(mid) > 0:
            hi = mid
        else:
            lo = mid
    return logit - (lo + hi) / 2


def profile_rate_gradient(nu, subset_fraction, theta, strict_interior=False,
                          stable_derivatives=False):
    """Variational objective and gradient for one height law nu."""
    import numpy as np
    m = len(nu) - 1
    p = subset_fraction
    nu = np.asarray(nu, dtype=float)
    entropy = -sum(x * math.log(x) for x in nu if x > 0)
    row_rate = 0.0
    tails = np.cumsum(nu[:0:-1])[::-1]
    derivs = []
    derivative = (hypergeom_rate_derivative_stable if stable_derivatives
                  else hypergeom_rate_derivative)
    for a in tails:
        row_rate += hypergeom_mgf_rate(a, p, theta)
        derivs.append(derivative(a, p, theta))
    if strict_interior:
        if np.any(nu <= 0):
            raise ValueError('strict tangent requires positive profile entries')
        grad = -np.log(nu) - 1
    else:
        grad = np.array([-math.log(max(x, 1e-300)) - 1 for x in nu])
    grad[1:] += np.cumsum(derivs)
    return entropy + row_rate, grad


def asymptotic_profile_rate(rows, mass_class, subset_fraction, theta):
    """Numerically maximize the fixed-row-count profile variational rate."""
    import numpy as np
    from scipy.optimize import minimize
    m, i, p = rows, mass_class, subset_fraction
    def rate(nu):
        return profile_rate_gradient(nu, p, theta)[0]
    def gradient(nu):
        return np.array(profile_rate_gradient(nu, p, theta)[1])
    constraints = [
        {'type': 'eq', 'fun': lambda x: sum(x) - 1},
        {'type': 'ineq', 'fun': lambda x: i - sum(j*xj for j, xj in enumerate(x))},
    ]
    lo, hi = 0.0, 100.0
    for _ in range(80):
        lam = (lo + hi) / 2
        weights = np.exp(-lam * np.arange(m + 1))
        mean = float(np.dot(np.arange(m + 1), weights) / weights.sum())
        if mean > i:
            lo = lam
        else:
            hi = lam
    geometric = np.exp(-hi * np.arange(m + 1))
    geometric /= geometric.sum()
    starts = [geometric]
    for center in (max(0, i - 1), min(m, i), min(m, i + 1)):
        seed = np.zeros(m + 1)
        seed[center] = 1
        starts.append(seed)
    solutions = [minimize(lambda x: -rate(x), seed, jac=lambda x: -gradient(x),
                          method='SLSQP',
                          bounds=[(0, 1)] * (m + 1), constraints=constraints,
                          options={'ftol': 1e-11, 'maxiter': 300})
                 for seed in starts]
    best = max(solutions, key=lambda result: rate(result.x))
    # Concavity makes the tangent plane a global upper bound. Maximize it
    # over the same simplex/mean constraints to audit the numerical optimum.
    from scipy.optimize import linprog
    nu0 = (1 - 1e-9) * best.x + 1e-9 * geometric
    val0, grad0 = profile_rate_gradient(nu0, p, theta)
    tangent = linprog(
        c=-np.asarray(grad0),
        A_ub=[list(range(m + 1))], b_ub=[i],
        A_eq=[[1] * (m + 1)], b_eq=[1],
        bounds=[(0, None)] * (m + 1), method='highs'
    )
    tangent_upper = (val0 - float(np.dot(grad0, nu0)) - tangent.fun
                     if tangent.success else math.inf)
    g = (i + 1) * math.log(i + 1) - i * math.log(i)
    separated = g + i * math.log1p(p * math.expm1(theta))
    return dict(rate=rate(best.x), separated=separated,
                mean=sum(j*x for j, x in enumerate(best.x)),
                profile=[round(float(x), 6) for x in best.x],
                optimizer_success=bool(best.success),
                optimizer_message=str(best.message), iterations=int(best.nit),
                tangent_upper=tangent_upper,
                tangent_gap=tangent_upper - float(rate(best.x)))


def asymptotic_profile_fw(rows, mass_class, subset_fraction, theta,
                          iterations=100, tol=1e-7):
    """Frank-Wolfe profile optimizer with a global tangent upper bound."""
    import numpy as np
    from scipy.optimize import linprog, brentq
    m, i, p = rows, mass_class, subset_fraction
    j = np.arange(m + 1, dtype=float)
    tail = 1 / (j + 1) ** 3
    tail /= tail.sum()
    tail_mean = float(np.dot(j, tail))
    delta = 1e-7
    target_mean = (i - delta * tail_mean) / (1 - delta)
    lo, hi = 0.0, 100.0
    for _ in range(80):
        lam = (lo + hi) / 2
        weights = np.exp(-lam * j)
        mean = float(np.dot(j, weights) / weights.sum())
        if mean > target_mean:
            lo = lam
        else:
            hi = lam
    geo = np.exp(-hi * j)
    geo /= geo.sum()
    nu = (1 - delta) * geo + delta * tail

    def oracle(gradient):
        return linprog(-gradient, A_ub=[j], b_ub=[i],
                       A_eq=[np.ones(m + 1)], b_eq=[1],
                       bounds=[(0, None)] * (m + 1), method='highs')

    records = []
    for it in range(iterations + 1):
        value, gradient = profile_rate_gradient(nu, p, theta)
        lp = oracle(np.asarray(gradient))
        if not lp.success:
            raise RuntimeError(lp.message)
        vertex = lp.x
        direction = vertex - nu
        gap = float(np.dot(gradient, direction))
        tangent_upper = value + gap
        records.append((value, tangent_upper, gap, float(np.dot(j, nu))))
        if gap <= tol or it == iterations:
            break
        if gap < 0:
            break

        def directional(alpha):
            _, grad = profile_rate_gradient(nu + alpha * direction, p, theta)
            return float(np.dot(grad, direction))

        right = 1 - 1e-12
        if directional(right) >= 0:
            alpha = right
        else:
            alpha = brentq(directional, 0, right, xtol=1e-10)
        nu = nu + alpha * direction

    value, upper, gap, mean = records[-1]
    return dict(rate=value, tangent_upper=upper, tangent_gap=gap,
                mean=mean, iterations=len(records) - 1,
                profile_head=[round(float(x), 8) for x in nu[:16]],
                profile_tail=[round(float(x), 10) for x in nu[-8:]])


def asymptotic_profile_fixedpoint(rows, mass_class, subset_fraction, theta,
                                  iterations=5000, damping=0.1, tol=1e-9):
    """Solve the interior KKT equations by damped exponential updates."""
    import numpy as np
    from scipy.optimize import linprog
    m, i, p = rows, mass_class, subset_fraction
    j = np.arange(m + 1, dtype=float)
    lo, hi = 0.0, 100.0
    for _ in range(80):
        lam = (lo + hi) / 2
        weights = np.exp(-lam * j)
        mean = float(np.dot(j, weights) / weights.sum())
        if mean > i:
            lo = lam
        else:
            hi = lam
    nu = np.exp(-hi * j)
    nu /= nu.sum()

    for it in range(iterations):
        tails = np.cumsum(nu[:0:-1])[::-1]
        derivs = np.array([hypergeom_rate_derivative(a, p, theta)
                           for a in tails])
        cumulative = np.concatenate(([0.0], np.cumsum(derivs)))
        def candidate(lagrange):
            logits = cumulative - lagrange * j
            logits -= logits.max()
            v = np.exp(logits)
            v /= v.sum()
            return v
        if float(np.dot(j, candidate(0))) <= i:
            v = candidate(0)
        else:
            left, right = 0.0, max(10.0, float(cumulative[-1] / max(1, m)) + 10)
            for _ in range(60):
                mid = (left + right) / 2
                if float(np.dot(j, candidate(mid))) > i:
                    left = mid
                else:
                    right = mid
            v = candidate((left + right) / 2)
        updated = (1 - damping) * nu + damping * v
        if float(np.max(np.abs(updated - nu))) < tol:
            nu = updated
            break
        nu = updated

    # Mix a tiny low-mean polynomial tail into the floating optimizer output.
    # This avoids underflowed zero coordinates in the tangent calculation and
    # keeps the mean constraint feasible for positive integer mass classes.
    tail = 1 / (j + 1) ** 4
    tail /= tail.sum()
    if i <= float(np.dot(j, tail)):
        raise ValueError('positive interior certificate unavailable at this mass')
    nu = 0.9999999999 * nu + 0.0000000001 * tail
    mean = float(np.dot(j, nu))
    if mean >= i - 1e-12:
        alpha = min(0.5, max(1e-12, (mean - i + 1e-9) / mean))
        nu = (1 - alpha) * nu + alpha * np.eye(1, m + 1, 0)[0]
    value, gradient = profile_rate_gradient(
        nu, p, theta, strict_interior=True, stable_derivatives=True
    )
    lp = linprog(-np.asarray(gradient), A_ub=[j], b_ub=[i],
                 A_eq=[np.ones(m + 1)], b_eq=[1],
                 bounds=[(0, None)] * (m + 1), method='highs')
    tangent_upper = value - float(np.dot(gradient, nu)) - lp.fun
    g = (i + 1) * math.log(i + 1) - i * math.log(i)
    separated = g + i * math.log1p(p * math.expm1(theta))
    return dict(rate=value, tangent_upper=tangent_upper,
                separated=separated,
                tangent_gap=tangent_upper-value,
                mean=float(np.dot(j, nu)), iterations=it+1,
                minimum_probability=float(nu.min()),
                zero_probabilities=int(np.count_nonzero(nu == 0)),
                profile_head=[round(float(x), 8) for x in nu[:16]],
                profile_tail=[round(float(x), 10) for x in nu[-8:]])


def asymptotic_escape_grid(rows, mass_class, fringe):
    """Coarse grid for the asymptotic escape fraction at eta=exp(-o(n))."""
    ps = (0.05, 0.1, 0.2, 0.35, 0.5, 0.65, 0.8, 0.9, 0.95)
    thetas = (0.5, 1, 2, 3, 4, 6, 8, 12)
    rows_out = []
    for p in ps:
        h = -p * math.log(p) - (1-p) * math.log1p(-p)
        candidates = []
        for theta in thetas:
            result = asymptotic_profile_rate(rows, mass_class, p, theta)
            weighted = (h + float(result['tangent_upper'])) / theta - fringe * p
            separated = (h + float(result['separated'])) / theta - fringe * p
            candidates.append((weighted, separated, theta,
                               result['optimizer_success']))
        rows_out.append((p, min(candidates, key=lambda v: v[0])))
    return rows_out


def run(rows, columns, mass_class, subset, theta):
    mass_cap = mass_class * columns
    z = weighted_profile_sum(rows, columns, mass_cap, subset, theta)
    check = enumerate_profile_sum(rows, columns, mass_cap, subset, theta)
    return dict(rows=rows, columns=columns, mass_cap=mass_cap, subset=subset,
                theta=theta, log_profile_sum=math.log(z),
                separated_log_bound=separated_log_bound(
                    mass_class, subset, columns, theta),
                direct_enumeration_log=math.log(check),
                dp_error=abs(z - check))


if __name__ == '__main__':
    ap = argparse.ArgumentParser()
    ap.add_argument('--rows', type=int, default=6)
    ap.add_argument('--columns', type=int, default=8)
    ap.add_argument('--mass-class', type=int, default=2)
    ap.add_argument('--subset', type=int, default=4)
    ap.add_argument('--theta', type=float, default=1.0)
    ap.add_argument('--fringe', type=int, default=2)
    ap.add_argument('--screen-escape', action='store_true',
                    help='compare finite weighted-MGF and analytic escape bounds')
    ap.add_argument('--asymptotic-rate', action='store_true',
                    help='optimize the fixed-row-count profile rate')
    ap.add_argument('--asymptotic-escape', action='store_true',
                    help='grid the weighted versus separated escape fraction')
    ap.add_argument('--frank-wolfe', action='store_true',
                    help='run the full-domain tangent-certified profile optimizer')
    ap.add_argument('--fixedpoint', action='store_true',
                    help='run the damped KKT fixed-point profile optimizer')
    args = ap.parse_args()
    print('PROFILE-WEIGHTED MOMENT DP; finite exploratory screen only')
    if args.fixedpoint:
        print('ASYMPTOTIC PROFILE KKT FIXED POINT; floating diagnostic')
        print(asymptotic_profile_fixedpoint(args.rows, args.mass_class,
                                             args.subset / args.columns,
                                             args.theta))
    elif args.frank_wolfe:
        print('ASYMPTOTIC PROFILE FRANK-WOLFE; floating diagnostic')
        print(asymptotic_profile_fw(args.rows, args.mass_class,
                                   args.subset / args.columns, args.theta))
    elif args.asymptotic_escape:
        print('ASYMPTOTIC ESCAPE GRID; numerical exploratory values only')
        print(asymptotic_escape_grid(args.rows, args.mass_class, args.fringe))
    elif args.asymptotic_rate:
        print('ASYMPTOTIC PROFILE RATE; numerical optimizer, not a certificate')
        print(asymptotic_profile_rate(args.rows, args.mass_class,
                                     args.subset / args.columns, args.theta))
    elif args.screen_escape:
        print('Numerical Chernoff grid; not an interval certificate')
        for fringe in range(args.rows // 2 + 1):
            print(fringe, weighted_mgf_escape(
                args.rows, args.columns, args.mass_class, fringe
            ))
    else:
        print(run(args.rows, args.columns, args.mass_class,
                  args.subset, args.theta))
