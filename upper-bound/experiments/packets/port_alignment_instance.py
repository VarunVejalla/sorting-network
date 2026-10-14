#!/usr/bin/env python3
"""Exact arithmetic screen for one ordinary Chvatal packet-port instance.

Mirrors the NodeShape formulas in FlowSizes7.lean for d=20, t=20:
level 6 is a mid parent, level 8 are botDesc children, and level 7 is the
receiving node at t+1. This checks packet divisibility and flow conservation,
not the packet-order invariant or a Lean theorem.
"""

from __future__ import annotations

import json
from pathlib import Path


BR = 64
PACKET = 4096
D = 20
T = 20
PARENT_LEVEL = 6
RECEIVER_LEVEL = 7
CHILD_LEVEL = 8


def main() -> None:
    # NodeShape.mid at the parent: d + 2*i = t + 9 + g.
    g = D + 2 * PARENT_LEVEL - T - 9
    assert g == 3
    parent_down = (BR**4 - 1) * BR ** (g + 2)

    # NodeShape.botDesc at each child: h = d + 2*i - t - 9.
    h = D + 2 * CHILD_LEVEL - T - 9
    child_g = D - CHILD_LEVEL - 1
    assert (h, child_g) == (7, 11)
    child_up_half = 4095 * 32 * BR**h
    child_up = 2 * child_up_half

    # Receiver is NodeShape.mid at t+1, with g' = d + 2*i - (t+1) - 9.
    receiver_g = D + 2 * RECEIVER_LEVEL - (T + 1) - 9
    assert receiver_g == 4
    receiver_size = BR ** (7 + receiver_g) - BR ** (1 + receiver_g)

    assert parent_down % PACKET == 0
    assert child_up_half % PACKET == 0
    assert receiver_size % PACKET == 0
    assert parent_down + BR * child_up == receiver_size

    parent_packets = parent_down // PACKET
    child_packets_each = child_up // PACKET
    received_packets = parent_packets + BR * child_packets_each
    assert received_packets == receiver_size // PACKET

    result = {
        "claim_level": "exact integer model of source NodeShape formulas",
        "parameters": {
            "branching": BR,
            "packet_wires": PACKET,
            "d": D,
            "t": T,
            "parent_level": PARENT_LEVEL,
            "receiver_level_at_t_plus_1": RECEIVER_LEVEL,
            "child_level": CHILD_LEVEL,
            "parent_mid_g": g,
            "child_botdesc_h": h,
            "child_botdesc_g": child_g,
            "receiver_mid_g": receiver_g,
        },
        "wires": {
            "parent_down_block": parent_down,
            "child_up_half_interval": child_up_half,
            "child_up_total_each": child_up,
            "receiver_total": receiver_size,
        },
        "packets": {
            "parent_down_block": parent_packets,
            "each_child_up_total": child_packets_each,
            "all_64_children_up": BR * child_packets_each,
            "receiver_total": received_packets,
        },
        "aligned_intervals": 1 + 2 * BR,
        "flow_conservation": True,
    }
    output = Path(__file__).with_name("port-alignment-instance.json")
    output.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
