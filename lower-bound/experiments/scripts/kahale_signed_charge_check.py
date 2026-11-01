"""Independent checker for the LB-08 certificates (standard library only).

Shares no code with kahale_signed_charge_screen.py and uses no solver. Images
are Python sets of integers, recomputed from the stored comparator lists.

Certificates (see docs/kahale-signed-charge-certificates.json):

* "farkas": nonnegative rationals y_r on layer rows (prefix, layer) with
      sum_r y_r (m(R_r) - m(L_r(R_r))) = m(cube)
  for every monomial m of the family.  If Phi = sum w_m m has unit drop, then
  Phi(cube) = sum_r y_r (Phi(R_r) - Phi(L_r R_r)) <= sum_r y_r.
* "path": layer steps (prefix, layer) where the image after each step has the
  same witness signature as the image the next step starts from, starting at
  the cube and ending at the zero signature.  Any function f of the signature
  with unit drop has f(cube) - f(zero signature) <= number of steps.
* "sorter": a network sorting every input of the listed weights. Any function
  of those rank slices has range at most its depth.
* "primal": rational weights; the unit drop (after scaling) is verified on every
  reachable image and every parallel layer.

Usage: python -B kahale_signed_charge_check.py CERT.json
"""
import json
import sys
from fractions import Fraction
from math import gcd


def run(n, layers, start=None):
    image = set(range(1 << n)) if start is None else set(start)
    for layer in layers:
        out = set()
        for x in image:
            for a, b in layer:
                if (x >> a) & 1 and not (x >> b) & 1:
                    x ^= (1 << a) | (1 << b)
            out.add(x)
        image = out
    return image


def as_layers(prefix):
    """Stored prefixes list one comparator per layer."""
    return [[c] for c in prefix]


def is_matching(layer, n):
    wires = [w for c in layer for w in c]
    return (len(wires) == len(set(wires)) and all(0 <= a < b < n for a, b in layer))


def witnesses(image, ranks):
    out = set()
    for x in image:
        k = bin(x).count("1")
        if k not in ranks:
            continue
        ones = [i for i in range(20) if (x >> i) & 1]
        zeros = [i for i in range(20) if not (x >> i) & 1]
        for a in ones:
            for b in zeros:
                if a < b:
                    out.add((k, a, b))
    return out


def trim(sig, n):
    return {(k, a, b) for k, a, b in sig if b < n}


def monomials(sig, sep):
    """Family monomials present: p <= q with rank separation <= sep (None = any)."""
    s = sorted(sig)
    return [(p, q) for i, p in enumerate(s) for q in s[i:]
            if sep is None or abs(p[0] - q[0]) <= sep]


def check_farkas(c):
    n, ranks, sep = c["n"], set(c["ranks"]), c["rank_separation"]
    total, combo = Fraction(0), {}
    for row in c["rows"]:
        y = Fraction(row["y"])
        assert y > 0
        assert all(is_matching(ly, n) for ly in as_layers(row["prefix"]))
        assert row["layer"] and is_matching(row["layer"], n)
        before = run(n, as_layers(row["prefix"]))
        after = run(n, [row["layer"]], before)
        for m in monomials(trim(witnesses(before, ranks), n), sep):
            combo[m] = combo.get(m, 0) + y
        for m in monomials(trim(witnesses(after, ranks), n), sep):
            combo[m] = combo.get(m, 0) - y
        total += y
    target = {m: Fraction(1) for m in monomials(trim(witnesses(run(n, []), ranks), n), sep)}
    keys = set(combo) | set(target)
    assert all(combo.get(m, 0) == target.get(m, 0) for m in keys), "combination differs from the initial monomials"
    return total


def check_path(c):
    n, ranks = c["n"], set(c["ranks"])
    current = trim(witnesses(run(n, []), ranks), n)
    for step in c["steps"]:
        assert all(is_matching(ly, n) for ly in as_layers(step["prefix"]))
        assert step["layer"] and is_matching(step["layer"], n)
        before = run(n, as_layers(step["prefix"]))
        assert trim(witnesses(before, ranks), n) == current, "signature mismatch at a join"
        current = trim(witnesses(run(n, [step["layer"]], before), ranks), n)
    assert not current, "path does not end at the zero signature"
    return len(c["steps"])


def check_primal(c):
    """Exhaustive: every image reachable by ascending comparators, every layer."""
    n, ranks = c["n"], set(c["ranks"])
    sep = c["rank_separation"]
    weights = {(tuple(p), tuple(q)): Fraction(v) for p, q, v in c["terms"]}
    assert all(p[0] in ranks and q[0] in ranks and p <= q and abs(p[0] - q[0]) <= sep for p, q in weights)
    points = range(1 << n)
    comps = [(a, b) for a in range(n) for b in range(a + 1, n)]
    move = {(a, b): (sum(1 << x for x in points if (x >> a) & 1 and not (x >> b) & 1), (1 << b) - (1 << a))
            for a, b in comps}

    def act(img, a, b):
        m, s = move[a, b]
        hit = img & m
        return (img ^ hit) | (hit << s)

    full = (1 << (1 << n)) - 1
    seen, todo = {full}, [full]
    while todo:
        img = todo.pop()
        for a, b in comps:
            t = act(img, a, b)
            if t not in seen:
                seen.add(t)
                todo.append(t)
    feats = sorted({f for pair in weights for f in pair})
    fmask = {(k, a, b): sum(1 << x for x in points if bin(x).count("1") == k and (x >> a) & 1 and not (x >> b) & 1)
             for k, a, b in feats}
    den = 1
    for v in weights.values():
        den = den * v.denominator // gcd(den, v.denominator)
    terms = [(fmask[p], fmask[q], int(v * den)) for (p, q), v in weights.items()]

    def phi(img):
        return sum(v for mp, mq, v in terms if img & mp and img & mq)

    value = {img: phi(img) for img in seen}

    def layers(free, cur):
        if not free:
            if cur:
                yield cur
            return
        rest = free[1:]
        yield from layers(rest, cur)
        for i, b in enumerate(rest):
            yield from layers(rest[:i] + rest[i + 1:], cur + [(free[0], b)])

    all_layers = list(layers(list(range(n)), []))
    worst = None
    checked = 0
    for img in seen:
        for ly in all_layers:
            t = img
            for a, b in ly:
                t = act(t, a, b)
            d = value[img] - value[t]
            checked += 1
            worst = d if worst is None or d > worst else worst
    start = Fraction(value[full], den)
    drop = Fraction(worst, den)
    return len(seen), checked, start, drop


def check_sorter(c):
    """Every input whose weight is in ranks is sorted by the stored network."""
    n, ranks = c["n"], set(c["ranks"])
    net = c["network"]
    assert all(ly and is_matching(ly, n) for ly in net)
    assert len(net) == c["claimed_bound"]
    inputs = [x for x in range(1 << n) if bin(x).count("1") in ranks]
    out = run(n, net, inputs)
    target = {((1 << n) - 1) ^ ((1 << (n - k)) - 1) for k in ranks}
    assert out == target, "network does not sort the rank slices"
    return len(net)


def main(path):
    with open(path, encoding="utf-8") as handle:
        data = json.load(handle)
    bad = 0
    for name, c in data["certificates"].items():
        if c["kind"] == "farkas":
            v = check_farkas(c)
            ok = v == Fraction(c["claimed_bound"])
            print(f"{name}: farkas n={c['n']} ranks={c['ranks']} rows={len(c['rows'])} bound={v} ({float(v):.6f}) {'OK' if ok else 'MISMATCH'}")
        elif c["kind"] == "primal":
            images, checked, start, drop = check_primal(c)
            ok = drop == Fraction(c["claimed_drop"]) and start == Fraction(c["claimed_start"]) and start / drop > c["needs_above"]
            print(f"{name}: primal n={c['n']} ranks={c['ranks']} images={images} transitions={checked} "
                  f"start={float(start):.6f} worst_drop={float(drop):.8f} start/drop={float(start / drop):.6f} {'OK' if ok else 'MISMATCH'}")
        elif c["kind"] == "sorter":
            v = check_sorter(c)
            ok = True
            print(f"{name}: slice sorter n={c['n']} ranks={c['ranks']} depth={v} OK")
        else:
            v = check_path(c)
            ok = v == c["claimed_bound"]
            print(f"{name}: path n={c['n']} ranks={c['ranks']} steps={v} {'OK' if ok else 'MISMATCH'}")
        bad += not ok
    print("ALL OK" if not bad else f"{bad} FAILED")
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1]))
