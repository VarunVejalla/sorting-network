#!/usr/bin/env python3
"""Check exact D2-flow compression by threshold shell and address suffix.

This is a finite flow-state audit, not a sorting or rank-transfer theorem.
For each stage and level, addresses are grouped by their first base-k digit
where they differ from the threshold spine, the side/digit of that split, and
their final ``suffix_digits`` address digits. Every member must have the same
interned FlowDAG node ID (hence the same complete recursive flow state).
"""
import argparse
from fractions import Fraction as F

from flow_dag import FlowDAG
from oracle import Par
from rank_recurrence import run as run_rank_history


def audit(depth, scale=1, suffix_digits=2, params=(3, 3, 2)):
    flow = FlowDAG(depth, scale=scale, p=Par(*params)).build()
    k = flow.p.k
    total = classes = state_shell_classes = 0
    mismatch = None
    for stage in range(len(flow.rows) + 1):
        # Propagate the quotient tree from its root. Each class stores its
        # exact interned node and multiplicity; children are generated from
        # the shell and rolling suffix. This checks every address without
        # expanding the k**depth tree.
        classes_here = {(('spine',), 0): (flow.roots[stage], 1)}
        for level in range(depth + 1):
            total += sum(count for _, count in classes_here.values())
            classes += len(classes_here)
            state_shell_classes += len({(shell, node)
                                         for (shell, _suffix), (node, _count)
                                         in classes_here.items()})
            if level == depth:
                break
            next_classes = {}
            spine_digit = (flow.native(0) // 3 // flow.native(level + 1)) % k
            for (shell, suffix), (node, multiplicity) in classes_here.items():
                children = flow.nodes[node][4]
                for digit, child in enumerate(children):
                    if shell == ('spine',):
                        if digit == spine_digit:
                            child_shell = ('spine',)
                        else:
                            child_shell = (level, -1 if digit < spine_digit else 1,
                                           digit - spine_digit)
                    else:
                        child_shell = shell
                    child_suffix = (suffix * k + digit) % (k**suffix_digits)
                    key = (child_shell, child_suffix)
                    if key in next_classes:
                        old_node, old_count = next_classes[key]
                        if old_node != child and mismatch is None:
                            mismatch = (stage, level + 1, child_shell,
                                        child_suffix, old_node, child)
                        next_classes[key] = (old_node, old_count + multiplicity)
                    else:
                        next_classes[key] = (child, multiplicity)
            classes_here = next_classes
    return {"depth": depth, "scale": scale, "suffix_digits": suffix_digits,
            "stages": len(flow.rows), "address_states": total,
            "compressed_classes": classes,
            "compression_ratio": total / classes,
            "state_shell_classes": state_shell_classes,
            "state_shell_ratio": total / state_shell_classes,
            "node_id_mismatch": mismatch}


def audit_history(depth, scale=8192, row_count=8192, params=(3, 3, 2)):
    """Check whether flow/shell classes preserve the scalar rank-history bounds."""
    flow = FlowDAG(depth, scale=scale, p=Par(*params)).build()
    _, history, *_ = run_rank_history(
        depth, scale, threshold=F(1, 3), include_history=True,
        params=params, row_count=row_count)
    k = flow.p.k
    q = flow.native(0) // 3
    by_state_shell = {}
    by_exact_margin = {}
    by_native_gap = {}
    total = 0
    for stage, history_at_stage in enumerate(history):
        for level in range(depth + 1):
            spine = q // flow.native(level)
            for index in range(k**level):
                node = flow.lookup(stage, level, index)
                shell = _address_shell(index, spine, k, level)
                bounds = history_at_stage.get((level, index), (0, 0))
                intervals = flow.bag_intervals(node, index)
                margins = [0 if lo <= q <= hi else q - hi if hi <= q else lo - q
                           for lo, hi in intervals]
                margin = min(margins) if margins else None
                native_lo = index * flow.native(level)
                native_hi = native_lo + flow.native(level)
                native_gap = (native_lo - q if q <= native_lo else
                              q - native_hi if q >= native_hi else 0)
                by_state_shell.setdefault((stage, level, node, shell), set()).add(bounds)
                by_exact_margin.setdefault(
                    (stage, level, node, shell, margin), set()).add(bounds)
                by_native_gap.setdefault(
                    (stage, level, node, shell, native_gap), set()).add(bounds)
                total += 1

    star_classes = 0
    star_mismatches = 0
    max_star_classes = 0
    for stage in range(len(history) - 1):
        for level in range(depth + 1):
            spine = q // flow.native(level)
            seen = {}
            for index in range(k**level):
                node = flow.lookup(stage, level, index)
                shell = _address_shell(index, spine, k, level)
                own = (node, shell, history[stage].get((level, index), (0, 0)))
                if level:
                    parent_index = index // k
                    parent = (flow.lookup(stage, level - 1, parent_index),
                              _address_shell(parent_index,
                                             q // flow.native(level - 1),
                                             k, level - 1),
                              history[stage].get((level - 1, parent_index), (0, 0)),
                              index % k)
                else:
                    parent = None
                if level < depth:
                    children = tuple(
                        (flow.lookup(stage, level + 1, index * k + digit),
                         _address_shell(index * k + digit,
                                        q // flow.native(level + 1), k, level + 1),
                         history[stage].get((level + 1, index * k + digit), (0, 0)))
                        for digit in range(k))
                else:
                    children = ()
                star = (stage, level, own, parent, children)
                next_label = (flow.lookup(stage + 1, level, index),
                              history[stage + 1].get((level, index), (0, 0)))
                if star in seen:
                    star_mismatches += seen[star] != next_label
                else:
                    seen[star] = next_label
            star_classes += len(seen)
            max_star_classes = max(max_star_classes, len(seen))
    def summarize(groups):
        return {"classes": len(groups),
                "varying_history_classes": sum(len(values) > 1
                                               for values in groups.values()),
                "max_distinct_intervals": max(map(len, groups.values()))}
    return {"depth": depth, "scale": scale, "row_count": row_count,
            "address_states": total, "state_shell": summarize(by_state_shell),
            "state_shell_exact_margin": summarize(by_exact_margin),
            "state_shell_native_gap": summarize(by_native_gap),
            "star_transition_classes": star_classes,
            "max_star_classes_at_one_stage_level": max_star_classes,
            "star_transition_mismatches": star_mismatches}


def _address_shell(index, spine, k, level):
    if index == spine:
        return ("spine",)
    digits = [(index // k**p) % k for p in range(level - 1, -1, -1)]
    spine_digits = [(spine // k**p) % k for p in range(level - 1, -1, -1)]
    split = next(i for i, (a, b) in enumerate(zip(digits, spine_digits)) if a != b)
    return (split, -1 if index < spine else 1,
            digits[split] - spine_digits[split])


if __name__ == "__main__":
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--depths", type=int, nargs="+", default=[3, 4, 5, 6])
    ap.add_argument("--scale", type=int, default=1)
    ap.add_argument("--suffix-digits", type=int, default=2)
    ap.add_argument("--params", type=int, nargs=3, default=(3, 3, 2))
    ap.add_argument("--check-history", action="store_true",
                    help="also test scalar history homogeneity by explicit address enumeration")
    ap.add_argument("--row-count", type=int, default=8192)
    args = ap.parse_args()
    for depth in args.depths:
        result = audit(depth, args.scale, args.suffix_digits, tuple(args.params))
        print(result, flush=True)
        if result["node_id_mismatch"] is not None:
            raise SystemExit("shell compression is not exact for this depth")
        if args.check_history:
            print(audit_history(depth, args.scale, args.row_count,
                                tuple(args.params)), flush=True)
