#!/usr/bin/env python3
"""Generate and exactly verify rational PSD certificates for the D2 spectral screen.

The certificate proves B >= 0 and M - B^2 >= 0, hence
    tr(sqrt(M)) >= tr(B).
All final checks use Fraction arithmetic; floating point is used only to propose B
and the dual prefix distribution.
"""
import argparse
from fractions import Fraction
import json
from math import isqrt, lcm
from pathlib import Path

import numpy as np

import d2_spectral_floor as screen


def parse_fraction(value):
    return Fraction(str(value))


def make_matrix(g, b, rho):
    L = len(g)
    tail = [sum((rho[k] * g[k] for k in range(i, L)), Fraction(0))
            for i in range(L)]
    return [[b * tail[max(i, j)] for j in range(L)] for i in range(L)]


def integer_matrix(A):
    n = len(A)
    denominator = 1
    for row in A:
        for value in row:
            denominator = lcm(denominator, value.denominator)
    return ([[value.numerator * (denominator // value.denominator)
              for value in row] for row in A], denominator)


def matmul(A, B):
    return [[sum(A[i][k] * B[k][j] for k in range(len(B)))
             for j in range(len(B[0]))] for i in range(len(A))]


def congruence(P, A):
    """Return integer-scaled P^T A P; the omitted scale is positive."""
    Ai, _ = integer_matrix(A)
    AP = matmul(Ai, P)
    return matmul([list(row) for row in zip(*P)], AP)


def strictly_diagonally_dominant_positive(A):
    return all(A[i][i] > sum(abs(A[i][j]) for j in range(len(A)) if j != i)
               for i in range(len(A)))


def rational_sqrt_certificate(M, scale=Fraction(95, 100), denominator=10**12):
    """Approximate sqrt(M), then exact-check B>0 and M-B^2>0."""
    n = len(M)
    M_float = np.array([[float(x) for x in row] for row in M])
    values, vectors = np.linalg.eigh(M_float)
    if values.min() <= 0:
        raise ValueError("covariance matrix was not numerically positive definite")
    root = (vectors * np.sqrt(values)) @ vectors.T
    pden = 10**12
    P = [[int(round(float(vectors[i, j]) * pden)) for j in range(n)]
         for i in range(n)]
    if not strictly_diagonally_dominant_positive(
            congruence(P, [[Fraction(int(i == j)) for j in range(n)]
                           for i in range(n)])):
        raise ValueError("could not certify the rational eigenbasis is invertible")
    for percent in range(int(scale * 100), 40, -1):
        alpha = Fraction(percent, 100)
        C = [[int(round(float(alpha) * root[i, j] * denominator))
              for j in range(n)] for i in range(n)]
        C = [[(C[i][j] + C[j][i]) // 2 for j in range(n)] for i in range(n)]
        if not strictly_diagonally_dominant_positive(
                congruence(P, [[Fraction(x) for x in row] for row in C])):
            continue
        C2 = [[sum(C[i][k] * C[k][j] for k in range(n))
               for j in range(n)] for i in range(n)]
        remainder = [[M[i][j] - Fraction(C2[i][j], denominator**2)
                      for j in range(n)] for i in range(n)]
        if strictly_diagonally_dominant_positive(congruence(P, remainder)):
            traceB = Fraction(sum(C[i][i] for i in range(n)), denominator)
            return C, P, percent, traceB
    raise ValueError("could not find a rational PSD square-root minorant")


def make_entry(rows, block, kind, mu=None, c0=None, spread=None):
    K = rows // 2
    L = K // block
    k = [block * (i + 1) for i in range(L)]
    if kind == "round1":
        g = [Fraction(1) for _ in k]
        _, rho_float = screen.min_trace_floor(np.ones(L), block, 400)
        muq = c0q = spreadq = None
    else:
        muq, c0q, spreadq = map(parse_fraction, (mu, c0, spread))
        g = [1 / (4 * (muq * ki + c0q)) for ki in k]
        _, rho_float = screen.min_trace_floor(
            np.array([float(x) for x in g]), block, 200)
    rho = screen.rational_distribution(rho_float)
    M = make_matrix(g, block, rho)
    C, P, percent, traceB = rational_sqrt_certificate(M)
    result = {
        "kind": kind,
        "rows": rows,
        "block": block,
        "rho": [str(x) for x in rho],
        "B_numerator": C,
        "B_denominator": 10**12,
        "eigenbasis_numerator": P,
        "eigenbasis_denominator": 10**12,
        "B_scale_percent": percent,
        "trace_B": str(traceB),
        "unit_lower_bound": str(traceB * traceB),
    }
    if kind == "round2":
        result.update({
            "mu": str(muq), "c0": str(c0q), "spread": str(spreadq),
            "base_mu": str(muq), "base_c0": str(c0q),
        })
        result["leak_lower_bound"] = str(
            muq * spreadq + c0q + traceB * traceB / 2)
    return result


def verify_entry(entry):
    rows, block = int(entry["rows"]), int(entry["block"])
    K, L = rows // 2, (rows // 2) // block
    rho = [Fraction(x) for x in entry["rho"]]
    if len(rho) != L or sum(rho, Fraction(0)) != 1 or any(x < 0 for x in rho):
        raise ValueError("invalid rational prefix distribution")
    k = [block * (i + 1) for i in range(L)]
    if entry["kind"] == "round1":
        g = [Fraction(1) for _ in k]
    else:
        mu, c0 = Fraction(entry["mu"]), Fraction(entry["c0"])
        g = [1 / (4 * (mu * ki + c0)) for ki in k]
    M = make_matrix(g, block, rho)
    C, denominator = entry["B_numerator"], int(entry["B_denominator"])
    n = len(M)
    if len(C) != n or any(len(row) != n for row in C):
        raise ValueError("wrong B dimensions")
    if any(C[i][j] != C[j][i] for i in range(n) for j in range(n)):
        raise ValueError("B numerator is not symmetric")
    P = entry["eigenbasis_numerator"]
    if len(P) != n or any(len(row) != n for row in P):
        raise ValueError("wrong eigenbasis dimensions")
    if not strictly_diagonally_dominant_positive(
            congruence(P, [[Fraction(int(i == j)) for j in range(n)]
                           for i in range(n)])):
        raise ValueError("eigenbasis is not certified invertible")
    if not strictly_diagonally_dominant_positive(
            congruence(P, [[Fraction(x) for x in row] for row in C])):
        raise ValueError("B is not certified positive definite")
    C2 = [[sum(C[i][k] * C[k][j] for k in range(n))
           for j in range(n)] for i in range(n)]
    remainder = [[M[i][j] - Fraction(C2[i][j], denominator**2)
                  for j in range(n)] for i in range(n)]
    if not strictly_diagonally_dominant_positive(congruence(P, remainder)):
        raise ValueError("M - B^2 is not certified positive definite")
    traceB = Fraction(sum(C[i][i] for i in range(n)), denominator)
    if traceB != Fraction(entry["trace_B"]):
        raise ValueError("trace mismatch")
    unit = traceB * traceB
    if unit != Fraction(entry["unit_lower_bound"]):
        raise ValueError("unit lower bound mismatch")
    if entry["kind"] == "round2":
        leak = (Fraction(entry["base_mu"]) * Fraction(entry["spread"]) +
                Fraction(entry["base_c0"]) + unit / 2)
        if leak != Fraction(entry["leak_lower_bound"]):
            raise ValueError("leak lower bound mismatch")
    return unit


def generate(args):
    entries = [make_entry(args.rows, args.block, "round1")]
    for mu in args.mus:
        for c0 in args.c0s:
            entries.append(make_entry(
                args.rows, args.block, "round2", mu, c0, args.spread))
    document = {
        "description": "Exact rational certificates for the sampled spectral grid.",
        "parameters": {
            "spread": str(parse_fraction(args.spread)),
            "mus": [str(parse_fraction(x)) for x in args.mus],
            "c0s": [str(parse_fraction(x)) for x in args.c0s],
        },
        "entries": entries,
    }
    Path(args.output).write_text(json.dumps(document, separators=(",", ":")) + "\n")
    print(f"wrote {len(entries)} exact certificates to {args.output}")
    verify_document(document)


def generate_continuous(args):
    if args.spread != 90 or args.rows != 8192 or args.block != 64:
        raise ValueError("the checked continuous cover is fixed at rows=8192, "
                         "block=64, spread=90")
    entries = [make_entry(args.rows, args.block, "round1")]
    boxes = [
        (Fraction(0), Fraction(1, 15), Fraction(0), Fraction(12)),
        (Fraction(1, 15), Fraction(2, 15), Fraction(0), Fraction(12)),
    ]
    for mu_lo, mu_hi, c0_lo, c0_hi in boxes:
        item = make_entry(args.rows, args.block, "round2",
                          str(mu_hi), str(c0_hi), str(args.spread))
        item["box"] = [str(mu_lo), str(mu_hi), str(c0_lo), str(c0_hi)]
        item["base_mu"], item["base_c0"] = str(mu_lo), str(c0_lo)
        item["leak_lower_bound"] = str(
            mu_lo * args.spread + c0_lo +
            Fraction(item["unit_lower_bound"]) / 2)
        entries.append(item)
    document = {
        "description": "Exact rational PSD cover of the continuous parameter domain.",
        "coverage": "continuous-parameter-cover",
        "parameters": {
            "spread_lower_bound": str(args.spread),
            "target": "12",
            "mu_domain": ["0", "2/15"],
            "c0_domain": ["0", "12"],
        },
        "entries": entries,
    }
    Path(args.output).write_text(json.dumps(document, separators=(",", ":")) + "\n")
    print(f"wrote {len(entries)} exact certificates to {args.output}")
    verify_document(document)


def verify_document(document):
    units = []
    leaks = []
    for item in document["entries"]:
        unit = verify_entry(item)
        if item["kind"] == "round1":
            units.append(unit)
        else:
            leaks.append((Fraction(item["leak_lower_bound"]), item["mu"], item["c0"]))
    if len(units) != 1:
        raise ValueError("expected one round-one certificate")
    D2 = units[0] / 2
    Dfloor = isqrt(D2.numerator // D2.denominator)
    print(f"verified round-one unit floor; per-side spread >= {Dfloor}")
    print("minimum exact round-two lower bound:",
          min(leaks, key=lambda x: x[0]))
    if document.get("coverage") == "continuous-parameter-cover":
        if document["parameters"] != {
                "spread_lower_bound": "90",
                "target": "12",
                "mu_domain": ["0", "2/15"],
                "c0_domain": ["0", "12"]}:
            raise ValueError("unexpected continuous-cover parameters")
        spread_floor = Fraction(document["parameters"]["spread_lower_bound"])
        if Dfloor < spread_floor:
            raise ValueError("round-one certificate does not prove the claimed spread floor")
        expected = [
            (Fraction(0), Fraction(1, 15), Fraction(0), Fraction(12)),
            (Fraction(1, 15), Fraction(2, 15), Fraction(0), Fraction(12)),
        ]
        actual = []
        for item in document["entries"]:
            if item["kind"] == "round2":
                if "box" not in item:
                    raise ValueError("continuous certificate entry has no parameter box")
                box = tuple(Fraction(x) for x in item["box"])
                actual.append(box)
                if int(item["rows"]) != 8192 or int(item["block"]) != 64:
                    raise ValueError("continuous certificate is not for rows=8192, block=64")
                mu_lo, mu_hi, c0_lo, c0_hi = box
                if (Fraction(item["mu"]), Fraction(item["c0"])) != (mu_hi, c0_hi):
                    raise ValueError("certificate matrix is not for the box upper corner")
                if (Fraction(item["base_mu"]), Fraction(item["base_c0"])) != (mu_lo, c0_lo):
                    raise ValueError("objective lower bound is not for the box lower corner")
                if Fraction(item["spread"]) != spread_floor:
                    raise ValueError("round-two entry uses a different spread floor")
        if actual != expected:
            raise ValueError(f"continuous boxes do not match the audited partition: {actual}")
        if any(value <= 12 for value, _, _ in leaks):
            raise ValueError("continuous spectral bound did not clear 12 rows")
        print("verified complete cover of 0<=mu<=2/15, 0<=c0<=12; "
              f"the spectral objective is >= {float(min(x[0] for x in leaks)):.6f} rows")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest="command", required=True)
    gen = sub.add_parser("generate")
    gen.add_argument("--rows", type=int, default=8192)
    gen.add_argument("--block", type=int, default=64)
    gen.add_argument("--spread", default="90")
    gen.add_argument("--mus", nargs="+",
                     default=["0.1", "0.12", "0.14", "0.17", "0.2", "0.25"])
    gen.add_argument("--c0s", nargs="+",
                     default=["0", "0.02", "0.05", "0.1", "0.2"])
    gen.add_argument("--output", required=True)
    gen.set_defaults(func=generate)
    cont = sub.add_parser("continuous")
    cont.add_argument("--rows", type=int, default=8192)
    cont.add_argument("--block", type=int, default=64)
    cont.add_argument("--spread", type=Fraction, default=Fraction(90))
    cont.add_argument("--output", required=True)
    cont.set_defaults(func=generate_continuous)
    ver = sub.add_parser("verify")
    ver.add_argument("certificate")
    def verify(args):
        document = json.loads(Path(args.certificate).read_text())
        verify_document(document)
    ver.set_defaults(func=verify)
    args = parser.parse_args()
    args.func(args)


if __name__ == "__main__":
    main()
