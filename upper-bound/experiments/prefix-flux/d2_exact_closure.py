#!/usr/bin/env python3
"""Exact fixed-threshold closure for a sender-wide stage on the (3,3,2) flow.

Section 4 of D2-SPATIAL-INVARIANT.md gave a crude scalar closure. This replaces it
with the exact routing. Fix a threshold q. For every bag keep the defect

    D_t(v) = #{keys < q in bag v} - #{wires < q in bag v},

which is zero at the root at t = 0 for every input (fact 1). Bags, ports and blocks
come from FlowDAG, so every role, ragged size and conservation law is exact.

The sender is abstract. A sender of a wires is m rows by n = a/m columns, holds i
rows of zeros, and its output obeys

    zeros in slots beyond row y = max(i - y, 0) + X(i, y),

with X the number of wrong pairs at row y. X combines a bulk leak and a capture
curve, which are the inputs under test. Keys are worst-cased inside this contract:
the run measures what a proof from these two contract curves would need. It is not a
simulation of a comparator network, and escapes need not be jointly realizable.

    python d2_capture_curve.py --out curve.json
    python d2_exact_closure.py --depth 40 --attack curve.json --startup-bulk 1 --bisect
    python d2_exact_closure.py --depth 32 --attack curve.json --startup-bulk 1 --bulk 17.7 --bisect-capture
"""
import argparse
import json
import math

from flow_dag import FlowDAG
from oracle import Par
from profile_cut_closure import rank_before

ROWS = 8192
OFF_SPINE_ROLES = ('mid', 'topRise', 'botDesc')
MIN_COLUMNS = 4000      # the curves were measured at this size; smaller bags are T2


class Contract:
    """X(i, y): wrong pairs at row y for a sender holding i rows of zeros."""

    def __init__(self, bulk, escape=None, table=None, sigma=None, sides=(1.0, 1.0),
                 startup_bulk=None, startup_stages=1, capture_scale=1.0):
        self.bulk = bulk
        self.startup_bulk = bulk if startup_bulk is None else startup_bulk
        self.startup_stages = startup_stages
        self.stage = 0
        self.capture_scale = capture_scale
        self.escape = escape
        self.table = table
        self.sigma = sigma if sigma is not None else max(bulk, 1e-9)
        self.sides = sides

    def capture(self, i, y):
        """E(i, y): rows beyond y, for mass i below the end of the sender."""
        if self.escape is not None:
            return self.escape * i + max(i - y, 0.0)
        return self.table.value(i, y)

    def wrong(self, i, y, gap, side):
        """Wrong pairs for end mass i at row y; gap is |y - i|, kept exact."""
        i = max(i, 0.0)
        scale = self.startup_bulk if self.stage < self.startup_stages else self.bulk
        bulk = scale * math.exp(-gap / self.sigma)
        if i <= 40 and y <= 64:
            excess = max(self.capture(i, y) - max(i - y, 0.0), 0.0)
            bulk = min(bulk, excess * self.capture_scale)
        return bulk * (self.sides[side] if side is not None else 1.0)


class Table:
    """Attack values E(i, f), interpolated in i and in f; decays above the grid."""

    def __init__(self, path):
        raw = json.load(open(path))
        self.fringes = sorted(int(f) for f in raw)
        self.curves = {int(f): sorted((float(i), float(v)) for i, v in raw[f].items())
                       for f in raw}

    def curve(self, f, i):
        """Attack value, floored by the pyramid rate that holds for any scramble."""
        pts = self.curves[f]
        floor = i * 6 / ((f + 1) * (f + 2) * (f + 3))
        return max(self.raw(pts, i), floor)

    @staticmethod
    def raw(pts, i):
        if i <= pts[0][0]:
            return pts[0][1] * i / pts[0][0]
        for (a, va), (b, vb) in zip(pts, pts[1:]):
            if i <= b:
                return va + (vb - va) * (i - a) / (b - a)
        return pts[-1][1] + (i - pts[-1][0])

    def value(self, i, y):
        lo, hi = self.fringes[0], self.fringes[-1]
        if y <= lo:
            return self.curve(lo, i) + (lo - y)
        if y >= hi:
            top, below = self.curve(hi, i), self.curve(hi - 1, i)
            ratio = min(top / below, 1.0) if below > 0 else 1.0
            return max(top * ratio ** (y - hi), i - y, 0.0)
        a = int(math.floor(y))
        b = min(a + 1, hi)
        w = y - a
        return (1 - w) * self.curve(a, i) + w * self.curve(b, i)


class Closure:
    def __init__(self, depth, params=(3, 3, 2), scale=ROWS):
        self.p = Par(*params)
        self.d = depth
        self.flow = FlowDAG(depth, scale=scale, p=self.p).build()
        self.T = len(self.flow.rows)
        self.N = self.p.k ** depth * scale

    def active(self, lev, t):
        return lev == 0 if t == 0 else self.p.active(self.d, lev, t)

    def path(self, q):
        """Nodes whose native interval has q strictly inside (or the root)."""
        out = []
        for lev in range(self.d + 1):
            R = self.flow.native(lev)
            idx, rest = divmod(q, R)
            if lev and not rest:
                break
            out.append((lev, idx))
        return out

    def pieces(self, key, t):
        """Slot-ordered output pieces of an active sender: (start, stop, target)."""
        lev, idx = key
        state = self.flow.lookup(t, lev, idx)
        a, pi, blocks = self.flow.rows[t][state]
        up = (lev - 1, idx // self.p.k) if lev else None
        if pi >= a and pi > 0:
            return state, a, pi, [(0, a, up)]
        h = pi // 2
        out = [(0, h, up)] if h else []
        pos = h
        for j, b in enumerate(blocks):
            if b:
                out.append((pos, pos + b, (lev + 1, idx * self.p.k + j)))
            pos += b
        if pi - h:
            out.append((pos, pos + pi - h, up))
        return state, a, pi, out

    def last_visit(self, spine):
        """Last stage at which the deepest spine node can still cross the cut."""
        lev, idx = max(spine)
        last = 0
        for t in range(self.T):
            if self.active(lev, t):
                state = self.flow.lookup(t, lev, idx)
                if self.flow.rows[t][state][0]:
                    last = t
        return last

    def run(self, q, contract, trace=False, stop_ratio=None):
        D = {}
        spine = set(self.path(q))
        last = self.last_visit(spine)
        worst = dict(rows=0.0, ratio=0.0, role=None, t=None, lev=None, f=None,
                     last=last)
        log = []
        for t in range(self.T):
            self.measuring = t <= last + 1
            if stop_ratio and worst['ratio'] > stop_ratio:
                break
            contract.stage = t
            new = {}
            senders = {k for k in spine if self.active(k[0], t)}
            senders |= {k for k, v in D.items() if self.active(k[0], t)}
            for key, value in D.items():
                if key not in senders:
                    new[key] = new.get(key, 0) + value
            for key in senders:
                self.send(key, t, q, D.get(key, 0), spine, contract, new, worst)
            D = {k: v for k, v in new.items() if v}
            assert sum(D.values()) == 0, (t, sum(D.values()))
            if trace:
                log.append((t, dict(D)))
        off = {k: v for k, v in D.items() if k not in spine}
        worst['terminal_off_spine'] = sum(abs(v) for v in off.values())
        worst['terminal_nodes'] = len(off)
        worst['defect_sum'] = sum(D.values())
        return (worst, log) if trace else worst

    def send(self, key, t, q, defect, spine, contract, new, worst):
        lev, idx = key
        state, a, pi, pieces = self.pieces(key, t)
        if a == 0:
            assert abs(defect) < 1e-6, (key, t, defect)
            return
        wires = self.flow.bag_intervals(state, idx)
        ideal = rank_before(wires, q)
        # Defects are exact integers: keys are integers, and the conservation law
        # sum D = 0 must not pick up rounding from wire counts near 2^90.
        assert -ideal <= defect <= a - ideal, (key, t, defect, ideal, a)
        zero_side = 2 * ideal + defect <= a
        low_keys = ideal + defect if zero_side else a - ideal - defect
        n = a / ROWS
        low = low_keys / n
        on_spine = key in spine
        role = 'topDesc' if t == 0 else self.p.role(self.d, lev, t)
        if (self.measuring and not on_spine and role in OFF_SPINE_ROLES and pi < a
                and a >= MIN_COLUMNS * ROWS):
            f = ROWS * pi / (2 * a)
            if low / f > worst['ratio']:
                worst.update(rows=low, ratio=low / f, role=role, t=t, lev=lev, f=f)
        side = None if on_spine else 0 if idx * self.flow.native(lev) >= q else 1

        def excess(slot):
            """Zeros beyond `slot`, minus the same count for the ideal output."""
            if slot <= 0:
                return defect
            if slot >= a:
                return 0
            u = slot - ideal
            exact = max(defect - u, 0) if u >= 0 else max(defect, u)
            gap = abs(u - defect) / n
            if gap > 8 * contract.sigma:
                return exact
            y = (slot if zero_side else a - slot) / n
            wrong = int(min(contract.wrong(low, y, gap, side), low) * n)
            # Wrong pairs need room: zeros past the slot and ones before it.
            room = min(a - slot - max(ideal + defect - slot, 0),
                       slot - max(slot - ideal - defect, 0))
            return exact + min(wrong, max(room, 0))

        for start, stop, target in pieces:
            value = excess(start) - excess(stop)
            if value:
                assert target is not None, (key, t, value)
                new[target] = new.get(target, 0) + value


def thresholds(c):
    """Cuts at low levels, with offsets into the reserved end regions."""
    k, N = c.p.k, c.N
    cuts = []
    for lev in range(0, 4):
        R = c.flow.native(lev + 1)
        for j in (1, 4):
            cuts.append((lev, ((k ** lev // 2) * k + j) * R))
    out = []
    for lev, q in cuts:
        out.append((f'cut lev{lev}', q))
    root = N // 2
    for shift in (-1, 1, 3):
        out.append((f'root cut + {shift}*fringe', root + shift * N // 2000))
    return out


def worst_over(c, contract, qs=None, stop_ratio=None):
    best = None
    for name, q in qs or thresholds(c):
        r = c.run(q, contract, stop_ratio=stop_ratio)
        r['q'] = name
        if best is None or r['ratio'] > best['ratio']:
            best = r
    return best


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--depth', type=int, default=20)
    ap.add_argument('--bulk', type=float, default=17.7, help='wrong rows per sender')
    ap.add_argument('--sigma', type=float)
    ap.add_argument('--startup-bulk', type=float)
    ap.add_argument('--startup-stages', type=int, default=1)
    ap.add_argument('--escape', type=float, help='constant capture E/a')
    ap.add_argument('--attack', help='JSON table {f: {i: E}} of capture values')
    ap.add_argument('--sides', type=float, nargs=2, default=[1.0, 1.0],
                    help='leak multipliers for senders right and left of the cut')
    ap.add_argument('--capture-scale', type=float, default=1.0)
    ap.add_argument('--bisect-capture', action='store_true',
                    help='largest multiple of the capture curve that closes at --bulk')
    ap.add_argument('--bisect', action='store_true',
                    help='largest bulk with every off-spine mass below its fringe')
    args = ap.parse_args()
    c = Closure(args.depth)
    table = Table(args.attack) if args.attack else None
    contract = Contract(args.bulk, escape=args.escape, table=table, sigma=args.sigma,
                        startup_bulk=args.startup_bulk,
                        startup_stages=args.startup_stages, sides=tuple(args.sides))
    if args.bisect_capture:
        lo, hi = 0.0, 16.0
        for _ in range(8):
            mid = (lo + hi) / 2
            trial = Contract(args.bulk, table=table, sigma=args.sigma,
                             startup_bulk=args.startup_bulk,
                             startup_stages=args.startup_stages,
                             sides=tuple(args.sides), capture_scale=mid)
            r = worst_over(c, trial, stop_ratio=1.5)
            print(f"scale {mid:.3f}: mass/f {r['ratio']:.3f} at {r['role']} t={r['t']} "
                  f"lev={r['lev']} ({r['q']})", flush=True)
            if r['ratio'] <= 1:
                lo = mid
            else:
                hi = mid
        print(f"bulk {args.bulk}: largest closing capture scale about {lo:.3f}")
        return
    if args.bisect:
        lo, hi = 2.0, 40.0
        for _ in range(9):
            mid = (lo + hi) / 2
            trial = Contract(mid, escape=args.escape, table=table, sigma=args.sigma,
                             startup_bulk=args.startup_bulk,
                             startup_stages=args.startup_stages,
                             sides=tuple(args.sides))
            r = worst_over(c, trial, stop_ratio=1.5)
            print(f"bulk {mid:.3f}: mass/f {r['ratio']:.3f} at {r['role']} t={r['t']} "
                  f"lev={r['lev']} f={r['f']} ({r['q']})", flush=True)
            if r['ratio'] <= 1:
                lo = mid
            else:
                hi = mid
        print(f'largest closing bulk about {lo:.2f} rows')
        return
    for name, q in thresholds(c):
        r = c.run(q, contract)
        print(f"{name:24s} max mass {r['rows']:9.3f} rows, mass/f {r['ratio']:8.3f}, "
              f"role {r['role']}, t={r['t']}, lev={r['lev']}, f={r['f']}, "
              f"terminal off-spine {r['terminal_off_spine']:.1f} keys in "
              f"{r['terminal_nodes']} nodes, sum D {r['defect_sum']:.2e}", flush=True)


if __name__ == '__main__':
    main()
