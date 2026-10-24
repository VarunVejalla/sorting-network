"""Per-n route (d) sweep at the 731.25 point (floats; route_d_rigorous_nr evaluator, unchanged).

    python -I sweep731.py k [j_from j_to_cap] [NR]      (k = log2 of the lower n end, may be fractional;
                                                        env JRATIO = j-interval ratio, default 1.15)

covers every n' in [2^k, NR 2^k] (NR = 2 default) and every j in [j_from, min(j_to_cap, jmax)] by
1.15-geometric intervals (split at J), with the class-aware f_eff (params731.f_eff at n_hi = NR 2^k).
j_to_cap may be 'B<C>' meaning C J ln(NR 2^k) (the regime (A)/(B) boundary at the top of the n-interval;
regime (B) needs j >= C J ln n, so the cap at ln n_hi covers every n' <= n_hi up to its own boundary).
Contract: bound < 1 for j_b <= J, bound < j_a/J otherwise.
"""
import math
import os
import sys
import time

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, '..'))
sys.path.insert(0, HERE)
import route_d_rigorous_nr as RD  # noqa: E402
import params731 as P  # noqa: E402


def main():
    k = float(sys.argv[1])
    jfrom = float(sys.argv[2]) if len(sys.argv) > 2 else 1.0
    cap = sys.argv[3] if len(sys.argv) > 3 else 'inf'
    NR = float(sys.argv[4]) if len(sys.argv) > 4 else 2.0
    RD.NR = NR
    n = 2.0 ** k
    jr = float(os.environ.get('JRATIO', '1.15'))
    n_hi = NR * n
    J = P.J
    jto = P.jmax(n_hi)
    if cap.startswith('B'):
        jto = min(jto, float(cap[1:]) * J * math.log(n_hi))
    elif cap != 'inf':
        jto = min(jto, float(cap))
    print(f"sweep731 n in [2^{k:g}, {NR:g} 2^{k:g}], j ratio {jr:g}, J = {J:.0f}, classes {P.CLASSES}, j in [{jfrom:.6g}, {jto:.6g}]"
          f" = [{jfrom / J:.4g}, {jto / J:.4g}] J", flush=True)
    ja = jfrom
    nfail = 0
    worst_rel = -math.inf
    while ja < jto:
        jb = min(jto, ja * jr)
        if ja < J < jb:
            jb = J
        allowed = 1.0 if jb <= J else ja / J
        f = P.f_eff(ja, n_hi)
        t = time.time()
        e, s = RD.worst_interval(ja, jb, n, f)
        ok = e < allowed
        nfail += not ok
        worst_rel = max(worst_rel, e / allowed if allowed > 0 else e)
        print(f"  j in [{ja / J:10.4g}, {jb / J:10.4g}] J f={f:9.1f}: worst {e:12.1f} at s2 <= {s:7d}  allowed {allowed:10.1f}"
              f"  {'OK' if ok else 'FAIL'} [{time.time() - t:.0f}s]", flush=True)
        ja = jb
    print(f"DONE k={k:g}: {'0 FAIL' if nfail == 0 else '%d FAIL' % nfail}, worst esc/allowed {worst_rel:.4g}", flush=True)


if __name__ == "__main__":
    main()
