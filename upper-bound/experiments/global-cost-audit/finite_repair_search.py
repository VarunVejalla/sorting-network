"""Search fixed within-row matching layers for a small repair gadget.

This is a finite iid two-row diagnostic. A state is a pair of Boolean vectors
(upper-high defects, lower-hole defects). A C layer applies OR to the lower
index and AND to the higher index in each disjoint pair, independently to both
vectors; a final X layer cancels coincident defects. It does not model the
scheduler's correlated, localized band inputs or prove a network theorem.

The search replaces one perfect matching at a time, using common random
training inputs, and reports an independent validation estimate. A full
matching layer counts as one comparator-depth layer in this idealized model.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path

import numpy as np


def butterfly(wires: int) -> list[np.ndarray]:
    layers = []
    for bit in range(wires.bit_length() - 1):
        stride = 1 << bit
        pairs = []
        for base in range(0, wires, 2 * stride):
            for offset in range(stride):
                pairs.append((base + offset, base + offset + stride))
        layers.append(np.asarray(pairs, dtype=np.int32))
    return layers


def random_matching(rng: np.random.Generator, wires: int) -> np.ndarray:
    p = rng.permutation(wires).reshape(-1, 2)
    return np.sort(p, axis=1).astype(np.int32)


def inputs(rng: np.random.Generator, samples: int, wires: int):
    # Exact quarter-density marginals, sampled independently across rows.
    h = np.zeros((samples, wires), dtype=np.uint8)
    l = np.zeros_like(h)
    for s in range(samples):
        h[s, rng.choice(wires, wires // 4, replace=False)] = 1
        l[s, rng.choice(wires, wires // 4, replace=False)] = 1
    return h, l


def score(layers: list[np.ndarray], data, gap: int) -> float:
    h, l = data[0].copy(), data[1].copy()
    for depth in range(len(layers) + 1):
        if depth == gap:
            both = h & l
            h &= 1 - both
            l &= 1 - both
        if depth == len(layers):
            break
        pairs = layers[depth]
        a, b = pairs[:, 0], pairs[:, 1]
        ha, hb = h[:, a].copy(), h[:, b].copy()
        la, lb = l[:, a].copy(), l[:, b].copy()
        h[:, a], h[:, b] = ha | hb, ha & hb
        l[:, a], l[:, b] = la | lb, la & lb
    # The cross-row comparator layer is scheduled at the selected gap.
    return float(h.mean())


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--wires", type=int, default=64)
    ap.add_argument("--layers", type=int, default=16,
                    help="within-row C layers; final X layer is additional")
    ap.add_argument("--steps", type=int, default=120)
    ap.add_argument("--train", type=int, default=4096)
    ap.add_argument("--validate", type=int, default=32768)
    ap.add_argument("--seed", type=int, default=20261011)
    ap.add_argument("--output", type=Path)
    args = ap.parse_args()
    if args.wires < 4 or args.wires & (args.wires - 1) or args.wires % 4:
        ap.error("--wires must be a power of two divisible by four")
    if args.layers < 1:
        ap.error("--layers must be positive")

    rng = np.random.default_rng(args.seed)
    train = inputs(rng, args.train, args.wires)
    valid = inputs(rng, args.validate, args.wires)
    base = butterfly(args.wires)
    repeated_butterfly = (base * (args.layers // len(base))
                          + base[:args.layers % len(base)])
    current = [x.copy() for x in repeated_butterfly]
    gap = args.layers
    current_score = score(current, train, gap)
    best, best_score = [x.copy() for x in current], current_score
    best_gap = gap
    # Baselines choose the best single X-layer location on training data.
    butterfly_gap = min(range(args.layers + 1), key=lambda g: score(repeated_butterfly, train, g))
    random0 = [random_matching(rng, args.wires) for _ in range(args.layers)]
    random_gap = min(range(args.layers + 1), key=lambda g: score(random0, train, g))
    butterfly_score = score(repeated_butterfly, valid, butterfly_gap)
    random_score = score(random0, valid, random_gap)
    print(f"wires={args.wires}, C_layers={args.layers}, total_depth={args.layers+1}, seed={args.seed}")
    print(f"baseline validation: butterfly={butterfly_score:.6f}; random={random_score:.6f}")

    accepted = 0
    for step in range(args.steps):
        trial = [x.copy() for x in current]
        index = int(rng.integers(args.layers))
        trial[index] = random_matching(rng, args.wires)
        trial_gap = int(rng.integers(args.layers + 1)) if rng.random() < 0.2 else gap
        trial_score = score(trial, train, trial_gap)
        # Mild annealing lets the walk cross noisy local barriers.
        temp = 0.0008 * (1 - step / max(1, args.steps)) + 0.00002
        if trial_score < current_score or rng.random() < np.exp((current_score-trial_score)/temp):
            current, current_score, gap = trial, trial_score, trial_gap
            accepted += 1
        if trial_score < best_score:
            best, best_score, best_gap = [x.copy() for x in trial], trial_score, trial_gap
    validation = score(best, valid, best_gap)
    print(f"search accepted={accepted}/{args.steps}; best train={best_score:.6f}; validation={validation:.6f}; X_after_C={best_gap}")
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(json.dumps({
            "model": "iid two-row defect proxy; not scheduler-certified",
            "wires": args.wires,
            "within_row_layers": args.layers,
            "total_depth_in_proxy": args.layers + 1,
            "cross_layer_gap": best_gap,
            "seed": args.seed,
            "train_residual": best_score,
            "validation_residual": validation,
            "pairs_by_layer": [layer.tolist() for layer in best],
        }, indent=2) + "\n", encoding="utf-8")
        print(f"saved schedule: {args.output}")


if __name__ == "__main__":
    main()
