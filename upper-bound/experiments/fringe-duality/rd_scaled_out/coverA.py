"""Regime (A) cover: every j in [1, 1e6 J] (intervals ratio 1.15), every n >= max(2^40, e^{j_a/(100 J)}),
every set size (worst_merged: exact s <= 64, then 1.05 cells, closed by the monotone average). Every
j-dependence of escapes_merged is increasing (lam j, top = sqrt(2j), b0 = j/n0), so evaluating at j_b against
the allowance j_a/J (1 for j_b <= J) covers [j_a, j_b]. Floats."""
import sys, math, time
sys.path.insert(0, '..')
import rd_sparse as A
f, J = 3967.0, 5e5
CJ = 100 * J
part, nparts = int(sys.argv[1]), int(sys.argv[2])
cells = []
ja = 1.0
while ja < 1e6 * J:
    jb = min(1e6 * J, ja * 1.15)
    if ja < J < jb:
        jb = J
    cells.append((ja, jb))
    ja = jb
for idx, (ja, jb) in enumerate(cells):
    if idx % nparts != part:
        continue
    ln0 = max(40 * math.log(2), ja / CJ)
    allowed = 1.0 if jb <= J else ja / J
    t = time.time()
    e, s = A.worst_merged(jb, f, ln0)
    print("j in [%.4g, %.4g] J (n >= e^%.4g): worst %.4g at s2 <= %d  allowed %.4g  %s [%.0fs]" % (
        ja / J, jb / J, ln0, e, s, allowed, "OK" if e < allowed else "FAIL", time.time() - t), flush=True)
