"""Round-1 tail when every input column height is confined to [H-D, H+D] (inherited balance).
Attack: random target set S (all fractions p), prices +1 / -p/(1-p), climb restricted to the window.
Exact runs -> lower bounds. Also prints the window version of the hand bound, about D/(pi W) rows."""
import sys, math, numpy as np
n, m = int(sys.argv[1]), int(sys.argv[2])  # python window_tail.py 4099 2048
rng = np.random.default_rng(0)
s1 = np.stack([rng.permutation(n) for _ in range(m)])
flat = s1.ravel(); H = m // 2
def tail_rows(D, Ws):
    best = np.zeros(len(Ws)); lo, hi = H - D, H + D
    for p in (0.002, 0.005, 0.01, 0.02, 0.05, 0.1, 0.2, 0.5):
        k = max(1, int(p * n))
        for seed in range(3):
            S = np.random.default_rng(100 + seed).permutation(n) < k
            for neg in (1.0, 0.5, 0.2):
                price = np.where(S, 1.0, -neg * p / (1 - p))
                walk = np.vstack([np.zeros(n), np.cumsum(price[s1], axis=0)])
                h = lo + np.argmax(walk[lo:hi + 1], axis=0)
                filled = (np.arange(m)[:, None] < h[None, :]).ravel()
                mid = np.bincount(flat[filled], minlength=n); dev = mid - mid.mean()
                for i, W in enumerate(Ws):
                    best[i] = max(best[i], float(np.maximum(dev - W, 0).sum()) / n)
    return best
Ws = [4, 8, 16, 32, 64, 128]
print(f'n={n} m={m}; excess rows per column beyond W (attack), W = {Ws}')
for D in (8, 32, 128, 512, m // 2):
    t = tail_rows(D, Ws)
    print(f'D={D:5d}  ' + ' '.join(f'{x:8.3f}' for x in t) + '   D/(pi W): ' + ' '.join(f'{D/(math.pi*W):7.3f}' for W in Ws), flush=True)
