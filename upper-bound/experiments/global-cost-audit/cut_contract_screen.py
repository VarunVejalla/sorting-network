"""Exhaustively screen the bulk repair count contract on small profiles.

For a fixed row-wise scramble sigma, enumerate monotone pre-scramble columns
with height vector c, exact mass i*n, and optional L1/tail restrictions. Apply
sigma row by row, then a fixed comparator network R. For each cut compute

  Q_* = sum_j (s_j-i)_+,
  Q_R = number of repaired ones above the bottom i rows,
  slack = floor(E_B)-Q_*.

The row-scramble image of each enumerated profile is exact. The profile envelope
is only an over-approximation of profiles the upstream fixed network may reach;
this script does not prove that upstream reachability premise. Use small toy
geometries and treat passing results as finite diagnostics, not asymptotic
claims.

Network JSON format: {"layers": [[[wire_a, wire_b], ...], ...]}, using
row-major wire indices and ascending compare-exchange. `--repair identity` and
`--repair column-sort` provide built-in baselines.
"""

from __future__ import annotations

import argparse
import json
from fractions import Fraction
from pathlib import Path

import numpy as np


def profiles(rows: int, cols: int, cut: int, l1_cap: int | None,
             band: int | None, tail_cap: int | None):
    """Yield exact-mass height vectors satisfying optional profile bounds."""
    target = cut * cols
    prefix: list[int] = []

    def rec(j: int, remaining: int, l1: int, up: int, down: int):
        if j == cols:
            if remaining == 0:
                yield tuple(prefix)
            return
        left = cols - j - 1
        lo = max(0, remaining - rows * left)
        hi = min(rows, remaining)
        for h in range(lo, hi + 1):
            nl1 = l1 + abs(h - cut)
            nu = up + (max(0, h - cut - band) if band is not None else 0)
            nd = down + (max(0, cut - band - h) if band is not None else 0)
            if l1_cap is not None and nl1 > l1_cap:
                continue
            if tail_cap is not None and (nu > tail_cap or nd > tail_cap):
                continue
            # Minimum possible remaining L1 for this remaining mass.
            if l1_cap is not None and left:
                average = remaining - h
                ideal = min(rows, max(0, round(average / left)))
                lower_bound = min(
                    abs(q - cut) * left
                    for q in {0, rows, ideal, max(0, ideal - 1), min(rows, ideal + 1)}
                )
                if nl1 + lower_bound > l1_cap:
                    continue
            prefix.append(h)
            yield from rec(j + 1, remaining - h, nl1, nu, nd)
            prefix.pop()

    yield from rec(0, target, 0, 0, 0)


def make_scramble(rows: int, cols: int, seed: int) -> list[list[int]]:
    rng = np.random.default_rng(seed)
    return [rng.permutation(cols).tolist() for _ in range(rows)]


def scramble_profile(rows: int, cols: int, heights: tuple[int, ...], sigma):
    mat = np.zeros((rows, cols), dtype=np.uint8)
    for c, h in enumerate(heights):
        if h:
            mat[rows - h :, c] = 1
    out = np.zeros_like(mat)
    for r in range(rows):
        for old in range(cols):
            out[r, sigma[r][old]] = mat[r, old]
    return out


def column_sort_network(rows: int, cols: int, row_range=None):
    lo, hi = row_range if row_range is not None else (0, rows)
    layers = []
    for phase in range(hi - lo):
        pairs = []
        parity = phase % 2
        for r in range(lo + parity, hi - 1, 2):
            for c in range(cols):
                pairs.append((r * cols + c, (r + 1) * cols + c))
        layers.append(pairs)
    return layers


def read_network(path: Path, wires: int):
    data = json.loads(path.read_text(encoding="utf-8"))
    layers = data.get("layers")
    if not isinstance(layers, list):
        raise ValueError("network JSON must contain a list field `layers`")
    return validate_layers(layers, wires)


def validate_layers(layers, wires: int):
    result = []
    for depth, layer in enumerate(layers):
        used: set[int] = set()
        normalized = []
        for pair in layer:
            if len(pair) != 2:
                raise ValueError(f"layer {depth}: comparator must have two wire indices")
            a, b = map(int, pair)
            if a == b or min(a, b) < 0 or max(a, b) >= wires:
                raise ValueError(f"layer {depth}: invalid comparator {(a, b)} for {wires} wires")
            if a in used or b in used:
                raise ValueError(f"layer {depth}: comparators are not wire-disjoint")
            used.update((a, b))
            normalized.append((min(a, b), max(a, b)))
        result.append(normalized)
    return result


def apply_network(mat: np.ndarray, layers):
    out = mat.reshape(-1).copy()
    for layer in layers:
        for a, b in layer:
            if out[a] > out[b]:
                out[a], out[b] = out[b], out[a]
    return out.reshape(mat.shape)


def random_matching(rng: np.random.Generator, wires: int, active_wires=None):
    active = np.arange(wires) if active_wires is None else np.asarray(active_wires)
    if len(active) % 2:
        raise ValueError("active repair wire count must be even")
    pairs = rng.permutation(active).reshape(-1, 2)
    return [(min(int(a), int(b)), max(int(a), int(b))) for a, b in pairs]


def batch_max_excess(inputs: np.ndarray, top_masks: np.ndarray, layers, cap: int):
    state = inputs.copy()
    for layer in layers:
        if not layer:
            continue
        a = np.fromiter((p[0] for p in layer), dtype=np.int32)
        b = np.fromiter((p[1] for p in layer), dtype=np.int32)
        x, y = state[:, a].copy(), state[:, b].copy()
        state[:, a], state[:, b] = np.minimum(x, y), np.maximum(x, y)
    q = np.sum(state * top_masks, axis=1, dtype=np.int32)
    return int(np.max(q - cap)), float(np.mean(q)), q


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--rows", type=int, required=True)
    ap.add_argument("--columns", type=int, required=True)
    ap.add_argument("--cuts", help="comma-separated row cuts; default is 1,...,rows-1")
    ap.add_argument("--f", type=int, help="use scheduler-shaped cuts f+k*b, k=0,...,64")
    ap.add_argument("--b", type=int, help="scheduler-shaped block height")
    ap.add_argument("--l1-cap", type=int, help="bound sum_j |c_j-cut| on input profile")
    ap.add_argument("--band", type=int, help="tail band half-width W around cut")
    ap.add_argument("--tail-cap", type=int, help="bound each of U,D by this total")
    ap.add_argument("--cap", type=int, required=True,
                    help="integer target floor(E_B) for this toy geometry")
    ap.add_argument("--seed", type=int, default=20261011)
    ap.add_argument("--repair", choices=["identity", "column-sort"], default="identity")
    ap.add_argument("--network", type=Path, help="JSON fixed comparator network (overrides --repair)")
    ap.add_argument("--save-scramble", type=Path)
    ap.add_argument("--summary", action="store_true", help="omit per-cut witnesses")
    ap.add_argument("--search-depth", type=int, help="also search that many arbitrary perfect-matching layers")
    ap.add_argument("--search-steps", type=int, default=200)
    ap.add_argument("--save-search", type=Path, help="write best searched network in JSON format")
    ap.add_argument("--confine-rows", help="restrict repair/search comparators to row interval lo:hi")
    args = ap.parse_args()
    if args.rows < 2 or args.columns < 1:
        ap.error("rows must be at least two and columns positive")
    if (args.band is None) != (args.tail_cap is None):
        ap.error("--band and --tail-cap must be supplied together")
    if args.network and args.repair != "identity":
        ap.error("choose either --network or a non-default --repair")

    if args.f is not None or args.b is not None:
        if args.f is None or args.b is None or args.rows != 2 * args.f + 64 * args.b:
            ap.error("scheduler-shaped cuts require both --f and --b and rows=2*f+64*b")
        cuts = [args.f + k * args.b for k in range(65)]
    elif args.cuts:
        cuts = [int(x) for x in args.cuts.split(",")]
    else:
        cuts = list(range(1, args.rows))
    if any(i < 0 or i > args.rows for i in cuts):
        ap.error("each cut must lie between zero and rows")

    sigma = make_scramble(args.rows, args.columns, args.seed)
    if args.save_scramble:
        args.save_scramble.parent.mkdir(parents=True, exist_ok=True)
        args.save_scramble.write_text(json.dumps(sigma, indent=2) + "\n", encoding="utf-8")
    wires = args.rows * args.columns
    active_wires = None
    confined = None
    if args.confine_rows:
        try:
            lo, hi = map(int, args.confine_rows.split(":"))
        except ValueError:
            ap.error("--confine-rows must have form lo:hi")
        if lo < 0 or hi > args.rows or lo >= hi:
            ap.error("invalid confined row interval")
        confined = (lo, hi)
        active_wires = [r * args.columns + c for r in range(lo, hi) for c in range(args.columns)]
        if len(active_wires) % 2:
            ap.error("confined repair rectangle must contain an even number of wires")
    if args.network:
        layers = read_network(args.network, wires)
        name = str(args.network)
        if confined:
            if any(not (confined[0] <= a // args.columns < confined[1]
                        and confined[0] <= b // args.columns < confined[1])
                   for layer in layers for a, b in layer):
                ap.error("network has a comparator outside --confine-rows")
    elif args.repair == "column-sort":
        layers = column_sort_network(args.rows, args.columns, confined)
        name = "column-sort reference" if not confined else f"column-sort reference in rows {confined}"
    else:
        layers, name = [], "identity"

    print(f"geometry={args.rows}x{args.columns}; wires={wires}; repair={name}; depth={len(layers)}; "
          f"confined_rows={confined or 'none'}; sigma_seed={args.seed}")
    print(f"profile envelope: L1<={args.l1_cap if args.l1_cap is not None else 'unrestricted'}; "
          f"tail W/A={args.band}/{args.tail_cap}; integer target cap={args.cap}")
    all_pass = True
    total_profiles = 0
    failures = []
    cut_summaries = []
    case_inputs, case_masks = [], []
    for cut in cuts:
        count = 0
        min_slack = None
        max_defect = None
        max_required = -1
        worst = None
        worst_post = None
        for heights in profiles(args.rows, args.columns, cut, args.l1_cap,
                                args.band, args.tail_cap):
            count += 1
            pre = scramble_profile(args.rows, args.columns, heights, sigma)
            qstar = sum(max(int(s) - cut, 0) for s in pre.sum(axis=0))
            case_inputs.append(pre.reshape(-1))
            mask = np.zeros_like(pre)
            mask[: args.rows - cut, :] = 1
            case_masks.append(mask.reshape(-1))
            post = apply_network(pre, layers)
            qr = int(post[: args.rows - cut, :].sum())
            slack = args.cap - qstar
            defect = qr - qstar
            violation = qr - args.cap
            min_slack = slack if min_slack is None else min(min_slack, slack)
            max_defect = defect if max_defect is None else max(max_defect, defect)
            if worst is None or violation > max_required:
                max_required = violation
                worst, worst_post = heights, (qstar, qr, slack, defect)
        total_profiles += count
        if count == 0:
            if not args.summary:
                print(f"cut={cut}: EMPTY profile envelope")
            continue
        passed = max_required <= 0
        all_pass &= passed
        if not passed:
            failures.append((cut, max_required, worst))
        qstar, qr, slack, defect = worst_post
        cut_summaries.append((cut, count, min_slack, max_defect, max_required, passed))
        if not args.summary:
            print(f"cut={cut}: profiles={count}; min_slack={min_slack}; max_defect={max_defect}; "
                  f"worst(Q*={qstar}, QR={qr}, slack={slack}, defect={defect}, "
                  f"excess_over_cap={max_required}); pass={passed}; witness={worst}")
    if args.summary:
        fail_cuts = [cut for cut, _, _, _, excess, _ in cut_summaries if excess > 0]
        min_slack = min((s for _, _, s, _, _, _ in cut_summaries if s is not None), default=None)
        max_defect = max((d for _, _, _, d, _, _ in cut_summaries if d is not None), default=None)
        max_excess = max((e for _, _, _, _, e, _ in cut_summaries), default=None)
        print(f"cuts={len(cut_summaries)}; cut-profile cases={total_profiles}; all pass={all_pass}; "
              f"min slack={min_slack}; max defect={max_defect}; max excess={max_excess}; "
              f"failing cuts={fail_cuts}")
    else:
        print(f"total cut-profile cases={total_profiles}; all requested cuts pass={all_pass}")
        if failures:
            print(f"first failure={failures[0]}; failing cuts={len(failures)}")
    print("Reachability note: each tested row-scrambled matrix is exact for its listed height profile and fixed sigma. "
          "The L1/tail envelope is not itself a theorem about profiles reached by the upstream fixed network.")

    if args.search_depth is not None:
        if args.search_depth < 1 or args.search_steps < 0:
            ap.error("search depth must be positive and search steps nonnegative")
        inputs_array = np.asarray(case_inputs, dtype=np.uint8)
        masks_array = np.asarray(case_masks, dtype=np.uint8)
        if not len(inputs_array):
            ap.error("cannot search an empty profile envelope")
        rng = np.random.default_rng(args.seed + 1)
        current = [random_matching(rng, wires, active_wires) for _ in range(args.search_depth)]
        current_score = batch_max_excess(inputs_array, masks_array, current, args.cap)[0]
        best = [layer[:] for layer in current]
        best_score = current_score
        accepted = 0
        for step in range(args.search_steps):
            trial = [layer[:] for layer in current]
            at = int(rng.integers(args.search_depth))
            trial[at] = random_matching(rng, wires, active_wires)
            score = batch_max_excess(inputs_array, masks_array, trial, args.cap)[0]
            temp = 1.0 * (1 - step / max(1, args.search_steps)) + 0.05
            if score <= current_score or rng.random() < np.exp((current_score - score) / temp):
                current, current_score = trial, score
                accepted += 1
            if score < best_score:
                best, best_score = [layer[:] for layer in trial], score
        final_score, mean_q, _ = batch_max_excess(inputs_array, masks_array, best, args.cap)
        print(f"search: depth={args.search_depth}; steps={args.search_steps}; accepted={accepted}; "
              f"best max_excess_over_cap={final_score}; mean_QR={mean_q:.4f}; "
              f"all_enumerated_profiles_pass={final_score <= 0}")
        if args.save_search:
            args.save_search.parent.mkdir(parents=True, exist_ok=True)
            args.save_search.write_text(json.dumps({
                "description": "fixed perfect-matching comparator layers; toy profile-envelope search",
                "rows": args.rows,
                "columns": args.columns,
                "seed": args.seed,
                "depth": len(best),
                "confined_rows": confined,
                "max_excess_over_cap": final_score,
                "layers": best,
            }, indent=2) + "\n", encoding="utf-8")
            print(f"saved searched network: {args.save_search}")


if __name__ == "__main__":
    main()
