#!/usr/bin/env python3
"""Exact mass screen for the UB-28 width-4 universal-safe terminal gate.

For n=32, run randomized matching passes at widths 16 and 8, split the
exchangeable width-8 blocks into width-4 count profiles, and measure the mass
outside the gate from ub28-terminal-profile-screen.py. Exact Fractions are
used throughout. This asks whether universal safety of the tail is a useful
first-moment certificate; it does not count actual tail failures.
"""

import argparse
import importlib.util
from fractions import Fraction
from math import comb
from pathlib import Path


HERE = Path(__file__).resolve().parent


def load_module(name, filename):
    spec = importlib.util.spec_from_file_location(name, HERE / filename)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


count_process = load_module("ub28_count_process", "ub28-count-process.py")


def terminal_safe(profile):
    if any(profile[i] > profile[i + 1] for i in range(len(profile) - 1)):
        return False
    partial = [i for i, count in enumerate(profile) if count not in (0, 4)]
    return not partial or partial[-1] - partial[0] + 1 <= 3


def unsafe_mass(n, rounds):
    if n != 32:
        raise ValueError("the screened terminal gate is specific to n=32")
    h = n // 2
    dist = {
        (a, b): Fraction(comb(h, a) * comb(h, b), 2**n)
        for a in range(h + 1)
        for b in range(h + 1)
    }
    dist = count_process.apply_pass(dist, h, 0, rounds, 0)
    dist = count_process.apply_pass(dist, h, 1, rounds, 0)
    dist = count_process.split_blocks(dist, h)
    h //= 2
    dist = count_process.apply_pass(dist, h, 0, rounds, 0)
    dist = count_process.apply_pass(dist, h, 1, rounds, 0)
    dist = count_process.split_blocks(dist, h)
    return sum(mass for profile, mass in dist.items() if not terminal_safe(profile)), len(dist)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--rounds", nargs="+", type=int, default=[16, 70])
    args = parser.parse_args()
    for rounds in args.rounds:
        mass, states = unsafe_mass(32, rounds)
        print(
            f"n=32 rounds={rounds} profiles={states} "
            f"P[outside_gate]={float(mass):.12g} "
            f"E[outside_gate_inputs]={float(mass * 2**32):.12g}"
        )


if __name__ == "__main__":
    main()
