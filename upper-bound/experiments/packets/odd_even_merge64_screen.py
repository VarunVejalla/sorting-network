#!/usr/bin/env python3
"""Exhaustive Boolean threshold screen for the 64-wire odd-even merge."""


def layers(n):
    if n == 2:
        return [[(0, 1)]]
    half = n // 2
    sub = layers(half)
    out = []
    for layer in sub:
        out.append([(2*i, 2*j) for i, j in layer] +
                   [(2*i+1, 2*j+1) for i, j in layer])
    out.append([(2*i+1, 2*i+2) for i in range(half-1)])
    return out


def apply(xs, schedule):
    xs = list(xs)
    for layer in schedule:
        used = set()
        for i, j in layer:
            assert i < j and i not in used and j not in used
            used.update((i, j))
        for i, j in layer:
            if xs[i] > xs[j]:
                xs[i], xs[j] = xs[j], xs[i]
    return xs


def main():
    schedule = layers(64)
    checked = 0
    for a in range(33):
        for b in range(33):
            xs = [int(a <= i) for i in range(32)] + [int(b <= i) for i in range(32)]
            out = apply(xs, schedule)
            assert out == sorted(xs), (a, b)
            checked += 1
    print(f"checked {checked} threshold pairs; width=64; depth={len(schedule)}; comparators={sum(map(len, schedule))}")


if __name__ == "__main__":
    main()
