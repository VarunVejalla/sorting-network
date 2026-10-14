#!/usr/bin/env python3
"""Exact finite screen for 64-wire packet repair across ordinary ports.

At m=64, the schedule formulas predict all bag sizes/down blocks aligned;
up half-fringes are aligned or 32 mod 64. Each receiver then gets 0/2
half-packets from its parent and 0/128 from its 64 children. This script checks
those claims and flow conservation for d=7..40, 2<=t<tf7(d). It is a finite
exact-rational model, not a Lean theorem or a proof of packet labels.
"""

from __future__ import annotations

import json
import sys
from collections import Counter
from pathlib import Path

sys.path.insert(0, str(Path(__file__).parent))
import frontier_alignment_screen as schedule  # noqa: E402


K = 64
M = 64


def exact_int(value, label: str) -> int:
    if value.denominator != 1:
        raise AssertionError(f"{label} is not integral: {value}")
    return value.numerator


def main() -> None:
    schedule.M = M
    depth_counts: Counter[str] = Counter()
    stages = 0
    receives = 0
    max_half_packets = 0
    max_repair_packets = 0
    examples = []

    for d in range(7, 41):
        tf = 3 * d - 20
        for t in range(2, tf):
            stages += 1
            for level in range(1, d):
                receives += 1
                receiver_size = exact_int(schedule.allocation(d, level, t + 1), "receiver size")
                parent_level = level - 1
                child_level = level + 1
                parent_size = exact_int(schedule.allocation(d, parent_level, t), "parent size")
                child_size = exact_int(schedule.allocation(d, child_level, t), "child size")
                parent_down = exact_int(schedule.down(d, parent_level, t), "parent down")
                parent_half = exact_int(schedule.up(d, parent_level, t), "parent up") // 2
                child_half = exact_int(schedule.up(d, child_level, t), "child up") // 2
                child_up = 2 * child_half

                if (
                    receiver_size % M
                    or parent_size % M
                    or child_size % M
                    or parent_down % M
                    or parent_half % 32
                    or child_half % 32
                ):
                    raise AssertionError(
                        f"packet divisibility failed d={d},t={t},level={level}"
                    )
                if parent_half % M not in (0, 32) or child_half % M not in (0, 32):
                    raise AssertionError(
                        f"unexpected half-fringe residue d={d},t={t},level={level}"
                    )

                # Parent down interval starts at parent_half+j*parent_down.
                # All 64 possible children have the same residue, and a
                # nonzero interval with offset 32 cuts two 32-wire runs.
                parent_fragments = 2 if parent_down and parent_half % M == 32 else 0
                # Each child upSet has a prefix and suffix; each contributes
                # one 32-wire piece exactly when its half-fringe is 32 mod 64.
                child_fragments = 2 * K if child_up and child_half % M == 32 else 0
                fragments = parent_fragments + child_fragments
                if fragments % 2:
                    raise AssertionError(f"odd fragment count {fragments}")
                if fragments > 130:
                    raise AssertionError(f"too many fragments: {fragments}")

                incoming = parent_down + K * child_up
                if incoming != receiver_size:
                    raise AssertionError(
                        f"flow identity fails d={d},t={t},level={level}: "
                        f"{incoming} != {receiver_size}"
                    )
                repair_packets = fragments // 2
                untouched_packets = (incoming - 32 * fragments) // M
                if (incoming - 32 * fragments) % M:
                    raise AssertionError("unrepaired wire count is not a whole number of packets")
                if untouched_packets + repair_packets != receiver_size // M:
                    raise AssertionError("repaired packet count does not match receiver capacity")
                if (receiver_size - repair_packets * M) < 0:
                    raise AssertionError("repair fragments exceed receiver capacity")
                max_half_packets = max(max_half_packets, fragments)
                max_repair_packets = max(max_repair_packets, repair_packets)
                depth_counts[str(fragments)] += 1
                if fragments and len(examples) < 12:
                    examples.append(
                        {
                            "d": d,
                            "t": t,
                            "receiver_level": level,
                            "parent_fragments": parent_fragments,
                            "child_fragments": child_fragments,
                            "repair_pairs": repair_packets,
                        }
                    )

    result = {
        "claim_level": "finite exact-rational schedule model; not a Lean theorem",
        "packet_wires": M,
        "depths": [7, 40],
        "ordinary_stages_checked": stages,
        "receiver_instances_checked": receives,
        "half_packet_fragment_count_by_receiver": dict(sorted(depth_counts.items(), key=lambda kv: int(kv[0]))),
        "max_half_packet_fragments_per_receiver": max_half_packets,
        "max_repair_pairs_per_receiver": max_repair_packets,
        "repair_merge_depth_candidate": 6,
        "sample_receivers_requiring_repair": examples,
    }
    Path(__file__).with_name("packet64-repair-screen.json").write_text(
        json.dumps(result, indent=2) + "\n", encoding="utf-8"
    )
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
