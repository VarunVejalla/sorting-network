#!/usr/bin/env python3
"""Cutting-plane search for a phase-weighted D2 alignment potential.

Each adversarial LP gives a valid affine lower cut for the worst drift as a
function of the source/destination level weights. The master LP minimizes the
worst drift over normalized nonnegative phase weights. This is a model gate,
not a sorting-network proof.
"""
from fractions import Fraction as F
import argparse
import importlib.util
import json
from pathlib import Path
import sys

import numpy as np
from scipy.optimize import linprog

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
spec = importlib.util.spec_from_file_location("coupled_rank_lp", HERE / "coupled_rank_lp.py")
lp = importlib.util.module_from_spec(spec)
sys.modules[spec.name] = lp
spec.loader.exec_module(lp)

PROFILE = tuple((r, F(v)) for r, v in [
    (64, "103/10000"), (128, "78/10000"), (256, "47/10000"),
    (512, "151/100000"), (1024, "319/500000"),
    (2048, "31/100000"), (4096, "7/40000"), (8192, "117/1000000")])


def stage_gate(args, stage, source, destination):
    return lp.solve(
        depth=args.depth, scale=args.scale, threshold=F(1, 3),
        ordered_prefix=True, root_tail=True, row_stride=args.row_stride,
        params=(3, 3, 2), row_count=args.rows, time_limit=args.time_limit,
        distance_tail_profile=PROFILE,
        alignment_drift_stage=stage, alignment_drift_span=1,
        alignment_weight=F(1, 4), alignment_drift_rho=F(str(args.rho)),
        alignment_prev_floor=args.alignment_floor,
        alignment_prev_floor_unweighted=True,
        alignment_error_weight=F(args.error_weight),
        rank_profile_weight=F(str(args.rank_profile_weight)),
        rank_profile_exact=args.rank_profile_exact,
        alignment_level_weights=tuple(F(str(x)) for x in source),
        alignment_next_level_weights=tuple(F(str(x)) for x in destination))


def cut_from_result(out, stage, levels, error_weight, rho, spatial,
                    rank_profile_weight, rank_profile_exact):
    if out.get("solver_fun") is None:
        raise RuntimeError(out.get("message", out.get("solver_message")))
    residual = max(out.get(key, float("inf")) for key in
                   ("solution_eq_error", "solution_ub_error", "solution_bound_error"))
    if residual > 1e-4:
        raise RuntimeError(f"infeasible adversarial witness: max residual={residual}")
    if out.get("solution_integrality_error", 0) > 1e-6:
        raise RuntimeError(f"nonintegral adversarial selectors: {out['solution_integrality_error']}")
    if not out.get("success"):
        print(f"using feasible incumbent from nonoptimal solve: {out.get('solver_message')}")
    trace = {entry["stage"]: entry for entry in out["alignment_partition_trace"]}
    defect = {entry["stage"]: entry["within_bag_defect"]
              for entry in out["threshold_flux_trace"]}
    def split_features(entry):
        if spatial == "spine":
            return dict(entry["spine_level_l1"]), dict(entry["off_spine_level_l1"])
        return (dict(entry["level_l1"]),)
    src = split_features(trace[stage])
    dst = split_features(trace[stage + 1])
    es = defect[stage]
    ed = defect[stage + 1]
    features = levels * (2 if spatial == "spine" else 1)
    coeff = np.zeros(2 * features + 1)
    src_values = [src[0].get(lev, 0.0) for lev in range(levels)]
    dst_values = [dst[0].get(lev, 0.0) for lev in range(levels)]
    if spatial == "spine":
        src_values += [src[1].get(lev, 0.0) for lev in range(levels)]
        dst_values += [dst[1].get(lev, 0.0) for lev in range(levels)]
    coeff[:features] = -rho * np.asarray(src_values)
    coeff[features:2 * features] = np.asarray(dst_values)
    profile = out.get("rank_profile_values") or {stage: 0.0, stage + 1: 0.0}
    intercept = (error_weight * (ed - rho * es)
                 + rank_profile_weight
                 * (profile[stage + 1] - rho * profile[stage]))
    return coeff, intercept, -float(out["solver_fun"]), residual


def master(cuts, phases, levels, lower_weight):
    # Variables are phase-major normalized weights followed by the epigraph z.
    nweights = len(phases) * levels
    c = np.zeros(nweights + 1)
    c[-1] = 1.0
    a_ub, b_ub = [], []
    for phase_index, coeff, intercept, _, _ in cuts:
        row = np.zeros(nweights + 1)
        row[phase_index * levels:(phase_index + 1) * levels] = coeff[:levels]
        row[(phase_index + 1) * levels:(phase_index + 2) * levels] = coeff[levels:2 * levels]
        row[-1] = -1.0
        a_ub.append(row)
        b_ub.append(-intercept)
    a_eq, b_eq = [], []
    for phase_index in range(len(phases)):
        row = np.zeros(nweights + 1)
        row[phase_index * levels:(phase_index + 1) * levels] = 1.0
        a_eq.append(row)
        b_eq.append(1.0)
    bounds = [(lower_weight, 1.0)] * nweights + [(None, None)]
    res = linprog(c, A_ub=np.asarray(a_ub), b_ub=np.asarray(b_ub),
                  A_eq=np.asarray(a_eq), b_eq=np.asarray(b_eq),
                  bounds=bounds, method="highs")
    if not res.success:
        raise RuntimeError(res.message)
    return res.x[:-1].reshape(len(phases), levels), float(res.fun)


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--depth", type=int, default=5)
    ap.add_argument("--scale", type=int, default=8192)
    ap.add_argument("--rows", type=int, default=8192)
    ap.add_argument("--row-stride", type=int, default=64)
    ap.add_argument("--time-limit", type=float, default=120)
    ap.add_argument("--alignment-floor", type=float, default=100)
    ap.add_argument("--error-weight", type=float, default=0.125)
    ap.add_argument("--rho", type=float, default=1.0)
    ap.add_argument("--spatial", choices=("level", "spine"), default="level",
                    help="use level totals or separate spine/off-spine alignment")
    ap.add_argument("--rank-profile-weight", type=float, default=0.0,
                    help="coefficient on total local prefix defect at retained port cuts")
    ap.add_argument("--rank-profile-exact", action="store_true",
                    help="use exact binary encoding for min(H,s) in the port profile")
    ap.add_argument("--iterations", type=int, default=8)
    ap.add_argument("--lower-weight", type=float, default=1e-6)
    ap.add_argument("--start-weights", default="",
                    help="comma-separated phase-major weights (three vectors of depth+1 entries)")
    ap.add_argument("--save-cuts", default="",
                    help="write the accumulated valid adversarial cuts as JSON")
    ap.add_argument("--load-cuts", default="",
                    help="resume from a compatible JSON cut file")
    args = ap.parse_args()

    phases = (2, 3, 4)
    transitions = (2, 3)
    levels = args.depth + 1
    features = levels * (2 if args.spatial == "spine" else 1)
    if args.start_weights:
        weights = np.asarray([float(x) for x in args.start_weights.split(",")])
        if weights.size != len(phases) * features:
            raise ValueError("start-weights must contain 3*features values")
        weights = weights.reshape(len(phases), features)
        if np.any(weights < args.lower_weight) or not np.allclose(weights.sum(axis=1), 1):
            raise ValueError("each start-weight phase must sum to 1 and respect lower-weight")
    else:
        weights = np.full((len(phases), features), 1 / features)
    cuts = []
    if args.load_cuts:
        prior = json.loads(Path(args.load_cuts).read_text())
        if (prior.get("depth") != args.depth or prior.get("scale") != args.scale
                or prior.get("rows") != args.rows
                or prior.get("row_stride") != args.row_stride
                or prior.get("rho") != args.rho
                or prior.get("error_weight") != args.error_weight
                or prior.get("rank_profile_weight", 0.0) != args.rank_profile_weight
                or prior.get("rank_profile_exact", False) != args.rank_profile_exact
                or prior.get("alignment_floor_unweighted") != args.alignment_floor
                or prior.get("spatial_features", "level") != args.spatial):
            raise ValueError("incompatible saved cuts")
        cuts = [(cut["source_phase_index"], np.asarray(cut["coefficients"]),
                 cut["intercept"], cut["witness_value"],
                 cut["max_feasibility_residual"])
                for cut in prior["cuts"]]
    for iteration in range(args.iterations):
        observed = []
        upper = -np.inf
        for stage in transitions:
            out = stage_gate(args, stage, weights[stage - 2], weights[stage - 1])
            coeff, intercept, value, residual = cut_from_result(
                out, stage, levels, args.error_weight, args.rho, args.spatial,
                args.rank_profile_weight, args.rank_profile_exact)
            reconstructed = (coeff[:features] @ weights[stage - 2]
                             + coeff[features:2 * features] @ weights[stage - 1]
                             + intercept)
            if abs(reconstructed - value) > max(1e-3, abs(value) * 1e-7):
                raise AssertionError((stage, reconstructed, value))
            phase_index = stage - 2
            cuts.append((phase_index, coeff, intercept, value, residual))
            observed.append((stage, value, residual, out.get("solver_message")))
            upper = max(upper, value)
        new_weights, lower = master(cuts, phases, features, args.lower_weight)
        print(f"iteration={iteration} lower={lower:.6g} upper={upper:.6g} "
              f"gap={upper-lower:.6g} gates={observed}")
        print("weights=" + repr(new_weights.tolist()))
        if args.save_cuts:
            payload = {
                "claim_level": "finite selected-cut model only",
                "depth": args.depth, "scale": args.scale, "rows": args.rows,
                "row_stride": args.row_stride, "rho": args.rho,
                "error_weight": args.error_weight,
                "rank_profile_weight": args.rank_profile_weight,
                "rank_profile_exact": args.rank_profile_exact,
                "alignment_floor_unweighted": args.alignment_floor,
                "spatial_features": args.spatial,
                "max_witness_feasibility_residual": max(cut[4] for cut in cuts),
                "witness_residual_tolerance": 1e-4,
                "lower_weight": args.lower_weight,
                "phases": phases, "levels": levels, "features": features,
                "master_lower_bound": lower,
                "master_weights": new_weights.tolist(),
                "cuts": [{"source_phase_index": phase, "coefficients": coeff.tolist(),
                          "intercept": intercept, "witness_value": value,
                          "max_feasibility_residual": residual}
                         for phase, coeff, intercept, value, residual in cuts],
            }
            Path(args.save_cuts).write_text(json.dumps(payload, indent=2) + "\n")
        weights = new_weights
        if upper - lower <= max(1.0, abs(upper) * 1e-4):
            break


if __name__ == "__main__":
    main()
