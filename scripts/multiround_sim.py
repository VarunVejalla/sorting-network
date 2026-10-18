#!/usr/bin/env python3
"""Monte-Carlo test of multi-round scramble separators (sort - scramble - sort - scramble - sort ...).

Question.  A single sort-scramble-sort pack on an m x n matrix has Property-B accuracy
eps_B ~ c / sqrt(m) (for ANY fixed scramble, by a random-input argument).  After the first sort
the columns are exactly monotone and the column sums are flat to +-sqrt(m); a second scramble then
only randomises a band of ~ sqrt(m) rows.  Conjecture: after t scrambles the accuracy is
eps_t ~ m^{-(1 - 2^{-t})}, and the sorts after the first two only have to repair a displacement of
size m^{1/2}, m^{1/4}, ... instead of m.

What is simulated (all with exact uniformly random row permutations, i.e. exact scrambles):
  Part A (0/1 thresholds, "column-sum chain").  A threshold of the input is a monotone 0/1 matrix,
        described by its column sums s_c.  Row rho (counted from the bottom) then has
        n_rho = #{c : s_c >= rho} ones; a scramble puts them on a uniformly random n_rho-subset of
        the n cells; the next column sorting only keeps the new column sums.  We iterate this and
        record  eps_hat_t = sum_j |s'_j - mean| / (m n)  (= 2 * sum_j (s'_j - i)^+ /(m n), the
        statistic of Property B at level i = mean), the standard deviation sigma_t of the column sums
        and the variance proxy V_t = sum_rho p_rho (1 - p_rho) that governs the next round.
        Input families: F3(q) = a fraction q of the columns full, the rest empty (maximal variance at
        q = 1/2), F5 = three equal groups with sums 0, m/2, m, F2 = iid uniform column sums.
  Part B (distinct keys, displacement).  Real keys, exact column sorts: measure how far elements are
        from their sorted position inside a column right after each scramble (this is the amount a
        cheaper "near-sorter" would have to repair).

Reporting: every number is a mean over independent scramble draws with its standard deviation and
standard error; log-log slopes come with bootstrap 95% intervals (resampling the draws); predictions
come from the Gaussian recursion  sigma_{t+1}^2 = sigma_t / sqrt(pi).
Usage:  python scripts/multiround_sim.py --part A [--quick]   |   --part B  |  --part all
"""
import argparse
import math
import time
import zlib

import numpy as np

SQRT_PI = math.sqrt(math.pi)


def tag(name):
    return zlib.crc32(name.encode()) & 0xFFFF



# ----------------------------------------------------------------------------------------------
# Fast sampler (independent columns) and the exact mean-field recursion (n -> infinity)
# ----------------------------------------------------------------------------------------------
def scramble_sums_fast(s, m, rng):
    """Column sums after a scramble when the n columns are treated as independent
       (each row contributes an independent Bernoulli(p_rho), p_rho = n_rho / n):  the marginal law of every
       column sum is then exactly the Poisson-binomial law of the exact scramble.  Cost ~ band * n."""
    n = s.shape[0]
    lo, hi = int(s.min()), int(s.max())
    cnt = np.bincount(s, minlength=m + 2)
    ge = np.cumsum(cnt[::-1])[::-1]
    rho = np.arange(lo + 1, hi + 1)
    p = ge[rho] / n
    out = np.full(n, lo, dtype=np.int64)
    if len(p) == 0:
        return out
    # rows with equal p are contiguous (p is nonincreasing): one binomial draw per group
    change = np.concatenate(([True], p[1:] != p[:-1]))
    starts = np.flatnonzero(change)
    sizes = np.diff(np.concatenate((starts, [len(p)])))
    pg = p[starts]
    big = sizes > 1
    for c, q in zip(sizes[big], pg[big]):
        out += rng.binomial(int(c), float(q), size=n)
    ones = pg[~big]
    B = 256
    for a in range(0, len(ones), B):
        blk = ones[a:a + B]
        out += (rng.random((len(blk), n)) < blk[:, None]).sum(axis=0)
    return out


def pb_pmf(p_groups, counts):
    """pmf of a sum of independent Bernoullis: group g has counts[g] rows with success prob p_groups[g]."""
    total = int(np.sum(counts))
    K = 1
    while K < total + 1:
        K *= 2
    w = np.exp(-2j * np.pi * np.arange(K) / K)
    logf = np.zeros(K, dtype=complex)
    for q, c in zip(p_groups, counts):
        logf += c * np.log((1 - q) + q * w)
    pmf = np.real(np.fft.ifft(np.exp(logf)))
    pmf[pmf < 0] = 0.0
    return pmf[:total + 1] / pmf[:total + 1].sum()


def mf_step(pmf, off, m, tol=1e-15):
    """One exact mean-field scramble step.  pmf[v-off] = P(column sum = v)."""
    ge = np.cumsum(pmf[::-1])[::-1]                 # ge[k] = P(s >= off + k)
    lo, hi = off, off + len(pmf) - 1
    pr = ge[1:]                                     # rows rho = lo+1 .. hi
    # tiny/huge probabilities are rounded to 0/1 (error below tol per row)
    pr = np.where(pr < tol, 0.0, np.where(pr > 1 - tol, 1.0, pr))
    full = int(np.sum(pr == 1.0))
    nz = pr[(pr > 0) & (pr < 1)]
    if len(nz) == 0:
        return np.array([1.0]), lo + full
    uq, inv, cn = np.unique(nz, return_inverse=True, return_counts=True)
    pm = pb_pmf(uq, cn)
    keep = np.flatnonzero(pm > tol * 1e-3)
    pm = pm[keep[0]:keep[-1] + 1]
    return pm / pm.sum(), lo + full + int(keep[0])


def mf_input(family, m):
    if family.startswith("F3"):
        q = float(family[3:]) if len(family) > 2 else 0.5
        pmf = np.zeros(m + 1)
        pmf[0], pmf[m] = 1 - q, q
        return pmf, 0
    if family == "F5":
        pmf = np.zeros(m + 1)
        pmf[0] = pmf[m // 2] = pmf[m] = 1 / 3
        return pmf, 0
    if family == "F2":
        return np.full(m + 1, 1 / (m + 1)), 0
    raise ValueError(family)


def mf_stats(pmf, off):
    v = off + np.arange(len(pmf))
    mean = (pmf * v).sum()
    return float((pmf * np.abs(v - mean)).sum()), float(np.sqrt((pmf * (v - mean) ** 2).sum()))


def meanfield(family, m, rounds):
    """Exact n -> infinity values of (eps_hat_t, sigma_t) for t = 1..rounds."""
    pmf, off = mf_input(family, m)
    out = []
    for _ in range(rounds):
        pmf, off = mf_step(pmf, off, m)
        e, sg = mf_stats(pmf, off)
        out.append((e / m, sg))
    return out

# ----------------------------------------------------------------------------------------------
# Part A: column sums only
# ----------------------------------------------------------------------------------------------
def row_counts(s, m):
    """n_rho for rho = 1..m (rows counted from the bottom) of the monotone matrix with column sums s."""
    cnt = np.bincount(s, minlength=m + 1)
    ge = np.cumsum(cnt[::-1])[::-1]          # ge[v] = #{c : s_c >= v}
    return ge[1:m + 1]


def scramble_sums(s, m, rng):
    """New column sums after a uniformly random permutation inside every row."""
    n = s.shape[0]
    nr = row_counts(s, m)
    tmpl = np.arange(n, dtype=np.int32)[None, :] < nr[:, None]      # m x n bool, first n_rho cells set
    x = rng.permuted(tmpl, axis=1)
    return x.sum(axis=0, dtype=np.int64)


def make_input(family, m, n, rng):
    if family.startswith("F3"):
        q = float(family[3:]) if len(family) > 2 else 0.5
        nfull = int(round(q * n))
        s = np.zeros(n, dtype=np.int64)
        s[:nfull] = m
        return s
    if family == "F5":
        s = np.zeros(n, dtype=np.int64)
        third = n // 3
        s[third:2 * third] = m // 2
        s[2 * third:] = m
        return s
    if family == "F2":
        return rng.integers(0, m + 1, size=n).astype(np.int64)
    raise ValueError(family)


def proxies(s, m):
    """(L1 deviation statistic, std of sums, V = sum p(1-p) for the next round)."""
    n = s.shape[0]
    mean = s.mean()
    eps_hat = np.abs(s - mean).sum() / (m * n)
    p = row_counts(s, m) / n
    return eps_hat, s.std(), float((p * (1 - p)).sum())


def part_a_one(family, m, n, rounds, trials, seed):
    """Returns arrays [rounds, trials] of eps_hat, sigma, V."""
    ss = np.random.SeedSequence([seed, m, n, tag(family)])
    rngs = [np.random.default_rng(c) for c in ss.spawn(trials)]
    E = np.zeros((rounds, trials))
    S = np.zeros((rounds, trials))
    V = np.zeros((rounds, trials))
    for k in range(trials):
        rng = rngs[k]
        s = make_input(family, m, n, rng)
        for t in range(rounds):
            s = scramble_sums(s, m, rng)
            E[t, k], S[t, k], V[t, k] = proxies(s, m)
    return E, S, V


def predict(family, m, rounds):
    """Gaussian continuum prediction of sigma_t and eps_t (L1 statistic)."""
    if family.startswith("F3"):
        q = float(family[3:]) if len(family) > 2 else 0.5
        var0 = m * q * (1 - q)
    elif family == "F5":
        var0 = m * 2 / 9
    else:
        var0 = m / 6                      # F2: p(rho) = 1 - rho/m  ->  sum p(1-p) = m/6
    sig = math.sqrt(var0)
    out = []
    for _ in range(rounds):
        out.append((sig, sig * math.sqrt(2 / math.pi) / m))
        sig = math.sqrt(sig / SQRT_PI)
    return out


def boot_slope(logm, E_by_m, B=2000, seed=1):
    """Slope of log(mean eps) vs log m, bootstrap over the independent draws at every m."""
    rng = np.random.default_rng(seed)
    slopes = []
    for _ in range(B):
        ys = []
        for E in E_by_m:
            idx = rng.integers(0, len(E), size=len(E))
            ys.append(math.log(np.mean(E[idx])))
        slopes.append(np.polyfit(logm, ys, 1)[0])
    slopes = np.array(slopes)
    return slopes.mean(), slopes.std(), np.percentile(slopes, [2.5, 97.5])


def part_a(ms, n, rounds, trials, families, seed, fast=False, mf_max=1 << 22, slope_floor=4.0):
    """MC (exact scramble, or the independent-column sampler when fast) against the exact mean-field recursion."""
    kind = "independent-column sampler" if fast else "exact uniform row permutations"
    print("=" * 108)
    print(f"PART A{'2' if fast else ''}: column-sum chain, {kind}; n = {n}, draws per cell = {trials}, rounds = {rounds}")
    for fam in families:
        print("-" * 108)
        print(f"family {fam}")
        print("      m |t|  MC eps_hat  +- sd     (s.e.)  | mean-field eps  z  | MC sigma  MF sigma | V_t MC   V_t=sig/sqrt(pi)")
        store, sigmf = {}, {}
        for m in ms:
            if fast:
                E = np.zeros((rounds, trials)); S = np.zeros_like(E); V = np.zeros_like(E)
                ssq = np.random.SeedSequence([seed, m, n, tag(fam), 99])
                for k, c in enumerate(ssq.spawn(trials)):
                    rng = np.random.default_rng(c)
                    sv = make_input(fam, m, n, rng)
                    for t in range(rounds):
                        sv = scramble_sums_fast(sv, m, rng)
                        E[t, k], S[t, k], V[t, k] = proxies(sv, m)
            else:
                E, S, V = part_a_one(fam, m, n, rounds, trials, seed)
            mf = meanfield(fam, m, rounds) if m <= mf_max else predict_as_mf(fam, m, rounds)
            store[m], sigmf[m] = E, [x[1] for x in mf]
            for t in range(rounds):
                e, sd = E[t].mean(), E[t].std(ddof=1)
                se = sd / math.sqrt(trials)
                z = (e - mf[t][0]) / se if se > 0 else float("nan")
                vpred = mf[t][1] / SQRT_PI
                print(f"{m:7d} |{t + 1}| {e:.4e} +- {sd:.1e} ({se:.1e}) | {mf[t][0]:.4e} {z:6.1f} | "
                      f"{S[t].mean():8.2f} {mf[t][1]:8.2f} | {V[t].mean():9.2f} {vpred:9.2f}")
        print("   log-log slope of eps_hat vs m, using m with sigma_t >= %.0f (95%% bootstrap CI over draws);" % slope_floor)
        print("   expectation -(1 - 2^-t):")
        for t in range(rounds):
            sel = [m for m in ms if sigmf[m][t] >= slope_floor]
            if len(sel) < 3:
                print(f"     t={t + 1}: fewer than 3 m-values above the floor, skipped")
                continue
            sl, sd, ci = boot_slope(np.log(sel), [store[m][t] for m in sel])
            print(f"     t={t + 1}: m in [{sel[0]}, {sel[-1]}]  slope = {sl:+.3f} +- {sd:.3f}  CI [{ci[0]:+.3f}, "
                  f"{ci[1]:+.3f}]   expected {-(1 - 2.0 ** -(t + 1)):+.3f}")


def predict_as_mf(family, m, rounds):
    return [(e, sg) for (sg, e) in predict(family, m, rounds)]


# ----------------------------------------------------------------------------------------------
# Part B: displacement with real keys
# ----------------------------------------------------------------------------------------------
def make_keys(kind, m, n, rng):
    if kind == "random":
        return rng.permutation(m * n).reshape(m, n).astype(np.int32)
    if kind == "cluster":                       # column c holds the block c: a threshold at every column boundary
        return (np.arange(n, dtype=np.int32)[None, :] * m + np.arange(m, dtype=np.int32)[:, None])
    if kind == "stripe":                        # two interleaved cluster sets
        c = np.arange(n, dtype=np.int32)
        base = (c % 2) * (m * n // 2) + (c // 2) * m
        return base[None, :] + np.arange(m, dtype=np.int32)[:, None]
    raise ValueError(kind)


def displacement(K):
    """|position - rank inside the column| for every element."""
    m = K.shape[0]
    order = np.argsort(K, axis=0)
    rank = np.empty_like(order)
    np.put_along_axis(rank, order, np.arange(m, dtype=order.dtype)[:, None], axis=0)
    return np.abs(rank - np.arange(m, dtype=order.dtype)[:, None])


def part_b_one(kind, m, n, rounds, trials, seed):
    ss = np.random.SeedSequence([seed, m, n, tag(kind), 7])
    rngs = [np.random.default_rng(c) for c in ss.spawn(trials)]
    Dmax = np.zeros((rounds, trials))
    D999 = np.zeros((rounds, trials))
    Dmean = np.zeros((rounds, trials))
    for k in range(trials):
        rng = rngs[k]
        K = np.sort(make_keys(kind, m, n, rng), axis=0)         # first column sort
        for t in range(rounds):
            K = rng.permuted(K, axis=1)                        # scramble t+1
            d = displacement(K)                                # what the next sort has to repair
            Dmax[t, k] = d.max()
            D999[t, k] = np.percentile(d, 99.9)
            Dmean[t, k] = d.mean()
            K = np.sort(K, axis=0)                             # exact sort (to isolate the next round)
    return Dmax, D999, Dmean


def part_b(ms, n, rounds, trials, kinds, seed):
    print("=" * 100)
    print(f"PART B: displacement of keys inside a column right after scramble t (n = {n}, draws = {trials})")
    for kind in kinds:
        print("-" * 100)
        print(f"key family {kind}")
        print("   m  | t | max disp  mean +- sd  (max/sqrt m) | p99.9 mean +- sd | mean disp +- sd")
        for m in ms:
            Dmax, D999, Dmean = part_b_one(kind, m, n, rounds, trials, seed)
            for t in range(rounds):
                print(f"{m:5d} | {t + 1} | {Dmax[t].mean():9.1f} +- {Dmax[t].std(ddof=1):6.1f} "
                      f"({Dmax[t].mean() / math.sqrt(m):5.2f}) | {D999[t].mean():8.1f} +- {D999[t].std(ddof=1):5.1f} |"
                      f" {Dmean[t].mean():8.2f} +- {Dmean[t].std(ddof=1):.2f}")


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--part", choices=["A", "B", "all"], default="all")
    ap.add_argument("--quick", action="store_true")
    ap.add_argument("--seed", type=int, default=20261010)
    ap.add_argument("--trials", type=int, default=0)
    ap.add_argument("--n", type=int, default=0)
    a = ap.parse_args()
    t0 = time.time()
    if a.part in ("A", "all"):
        ms = [64, 128, 256] if a.quick else [64, 128, 256, 512, 1024, 2048, 4096]
        n = a.n or (1024 if a.quick else 8192)
        trials = a.trials or (6 if a.quick else 24)
        part_a(ms, n, 5, trials, ["F3", "F5", "F2"] if not a.quick else ["F3"], a.seed)
    if a.part in ("B", "all"):
        ms = [64, 128, 256] if a.quick else [64, 128, 256, 512, 1024, 2048]
        n = a.n or (512 if a.quick else 4096)
        trials = a.trials or (4 if a.quick else 12)
        part_b(ms, n, 3, trials, ["random", "cluster", "stripe"] if not a.quick else ["cluster"], a.seed)
    print(f"\nelapsed {time.time() - t0:.0f}s")


if __name__ == "__main__":
    main()
