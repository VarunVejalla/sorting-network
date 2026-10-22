import sys, time, math
sys.path.insert(0, '..')
import route_d_rigorous as R
f, J = 3967, 5e5
b, ln = float(sys.argv[1]), int(sys.argv[2])
n = 2.0 ** ln; j = b * n
t = time.time()
e, s = R.worst_interval(j / 1.15, j, n, f)
print("b=%g n=2^%d: worst escapes %.0f at s2<=%d, allowed %.3g, ratio %.3g [%.0fs]" % (b, ln, e, s, j / 1.15 / J, e / (j / 1.15 / J), time.time() - t), flush=True)
