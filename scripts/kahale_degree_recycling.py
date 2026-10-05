"""Exact Johnson-slice spectrum of equal-height median coalescence.

Rational spectral weights are recovered from integer Laplacian moments.
The prefixes are actual ordered comparator networks, not relaxed states.
"""
import argparse
from fractions import Fraction
from itertools import combinations
import json
from math import comb


def insertion_prefix(m):
    return [(j, j + 1) for end in range(1, m) for j in range(end - 1, -1, -1)]


def spectral_weights(eigenvalues, moments):
    weights = []
    for r, eigenvalue in enumerate(eigenvalues):
        coefficients = [1]
        denominator = 1
        for other in eigenvalues:
            if other == eigenvalue:
                continue
            updated = [0] * (len(coefficients) + 1)
            for j, coefficient in enumerate(coefficients):
                updated[j] -= other * coefficient
                updated[j + 1] += coefficient
            coefficients = updated
            denominator *= eigenvalue - other
        norm = Fraction(sum(a * b for a, b in zip(coefficients, moments)), denominator)
        assert norm >= 0
        weights.append(norm)
    assert sum(weights) == moments[0]
    assert sum(e * a for e, a in zip(eigenvalues, weights)) == moments[1]
    return weights


def spectrum(n, w, inputs, index, values):
    eigenvalues = [r * (n + 1 - r) for r in range(min(w, n - w) + 1)]
    degree = w * (n - w)
    neighbors = []
    for x in inputs:
        ones = [i for i in range(n) if x & (1 << i)]
        zeros = [i for i in range(n) if not x & (1 << i)]
        neighbors.append([index[x ^ (1 << i) ^ (1 << j)] for i in ones for j in zeros])
    power = values[:]
    moments = []
    for _ in eigenvalues:
        moments.append(sum(a * b for a, b in zip(values, power)))
        power = [degree * power[i] - sum(power[j] for j in adjacent)
                 for i, adjacent in enumerate(neighbors)]
    weights = spectral_weights(eigenvalues, moments)
    assert weights[0] == Fraction(sum(values) ** 2, len(inputs))
    return eigenvalues, weights


def quotient_spectrum(m):
    # On the central slice a=#ones in the first block is a sufficient
    # coordinate. Its multiplicity is binom(m,a)^2, not a uniform measure.
    eigenvalues = [r * (2 * m + 1 - r) for r in range(m + 1)]
    multiplicities = [comb(m, a) ** 2 for a in range(m + 1)]
    values = [int(a >= (m + 1) // 2) for a in range(m + 1)]
    power = values[:]
    moments = []
    for _ in eigenvalues:
        moments.append(sum(c * v * p for c, v, p in zip(multiplicities, values, power)))
        power = [((a * a * (power[a] - power[a - 1])) if a else 0) +
                 (((m - a) ** 2 * (power[a] - power[a + 1])) if a < m else 0)
                 for a in range(m + 1)]
    mass = comb(2 * m, m)
    assert sum(multiplicities) == mass
    weights = spectral_weights(eigenvalues, moments)
    assert weights[0] == Fraction(mass, 4)
    return eigenvalues, weights


def quotient_probe(m):
    if m < 3 or m % 2 == 0:
        raise ValueError("The block size must be odd and at least three")
    eigenvalues, norms = quotient_spectrum(m)
    mass = comb(2 * m, m)
    reserve = [(e - 2 * m) * v if r else Fraction(0)
               for r, (e, v) in enumerate(zip(eigenvalues, norms))]
    total = sum(reserve)
    high_share = sum(reserve[(m + 1) // 2:]) / total
    zero_locations = []
    for a in range(m):
        b = m - 1 - a
        v = [0] * (m - a) + [1] * a + [0] * (m - b) + [1] * b
        for i in range(m):
            j = 2 * m - 1 - i
            v[i], v[j] = min(v[i], v[j]), max(v[i], v[j])
        assert v[:m] == [0] * m
        locations = [i for i in range(m, 2 * m) if not v[i]]
        assert locations == [m + a]
        zero_locations.extend(locations)
    return dict(block_size=m, wires=2 * m, quotient_states=m + 1,
                highest_degree=m, highest_degree_variance_fraction=str(norms[-1] / mass),
                variance_degree_ge_three=str(sum(norms[3:]) / mass),
                reserve_share_degree_ge_half_block=str(high_share),
                approximate_high_degree_reserve_share=float(high_share),
                all_nonconstant_degrees_removed_by_median_gate=True,
                neighbor_weight_zero_locations=zero_locations,
                required_neighbor_slice_suffix_depth=(m - 1).bit_length(),
                method="Exact weighted block-count quotient; no input enumeration or floating eigensolver")


def conditional_height_probe(power):
    block = 1 << power
    n = block + 1
    layers = [[(start + (1 << stage) - 1, start + (1 << (stage + 1)) - 1)
               for start in range(0, block, 1 << (stage + 1))]
              for stage in range(power)] + [[(block - 1, block)]]
    h = [0] * n
    for layer in layers:
        for a, b in layer:
            h[a], h[b] = min(h[a], h[b]), max(h[a], h[b]) + 1

    def execute(mask):
        v = [(mask >> i) & 1 for i in range(n)]
        for layer in layers:
            for a, b in layer:
                v[a], v[b] = min(v[a], v[b]), max(v[a], v[b])
        return v

    baseline = execute(1 << block)
    groups = [0] * n
    for p in range(block):
        upper = execute((1 << block) | (1 << p))
        delta = [i for i in range(n) if baseline[i] != upper[i]]
        assert delta == [block - 1]
        groups[delta[0]] += 1
    assert h[block - 1] == 0 and groups[block - 1] == block
    return dict(wires=n, layer_depth=len(layers), baseline_one_positions=[block],
                output_wire=block - 1, output_scalar_height=0,
                routed_addition_group_size=groups[block - 1],
                global_minimum_zero_certificate_size=1,
                baseline_conditional_minimum_zero_certificate_size=block,
                target_function="AND(OR(first block), last input)",
                scope="Actual logarithmic-depth prefix; certificate sizes follow directly from the displayed function")


def probe(m):
    if m < 3 or m % 2 == 0:
        raise ValueError("The block size must be odd and at least three")
    n, w = 2 * m, m
    median = m // 2
    prefix = insertion_prefix(m)
    # Validate the actual block sorter on all Boolean inputs, including its
    # scalar-height trace. Two identical copies have identical traces.
    h = [0] * m
    for a, b in prefix:
        h[a], h[b] = min(h[a], h[b]), max(h[a], h[b]) + 1
    for x in range(1 << m):
        v = [(x >> i) & 1 for i in range(m)]
        for a, b in prefix:
            v[a], v[b] = min(v[a], v[b]), max(v[a], v[b])
        assert v == sorted(v)

    inputs = [sum(1 << i for i in chosen) for chosen in combinations(range(n), w)]
    index = {x: i for i, x in enumerate(inputs)}
    first, second = [], []
    central_after_all_pairs = True
    other_weight_unsorted = None
    for x in inputs:
        a = (x & ((1 << m) - 1)).bit_count()
        b = w - a
        left = [0] * (m - a) + [1] * a
        right = [0] * (m - b) + [1] * b
        first.append(left[median])
        second.append(right[median])
        assert first[-1] + second[-1] == 1
        for i in range(m):
            j = m - 1 - i
            assert left[i] + right[j] == 1
        v = left + right
        for i in range(m):
            j = 2 * m - 1 - i
            v[i], v[j] = min(v[i], v[j]), max(v[i], v[j])
        assert v == [0] * m + [1] * m
    # The same mirror matching sorts every central-slice input, but can fail
    # at a neighboring weight. Keep an exact witness to avoid overstating it.
    for x in range(1 << n):
        if x.bit_count() != m - 1:
            continue
        a = (x & ((1 << m) - 1)).bit_count()
        b = x.bit_count() - a
        v = [0] * (m - a) + [1] * a + [0] * (m - b) + [1] * b
        for i in range(m):
            j = 2 * m - 1 - i
            v[i], v[j] = min(v[i], v[j]), max(v[i], v[j])
        if v != sorted(v):
            other_weight_unsorted = dict(input_mask=x, weight=x.bit_count(), output=v)
            break
    assert other_weight_unsorted is not None

    eigenvalues, norms = spectrum(n, w, inputs, index, first)
    assert (eigenvalues, norms) == quotient_spectrum(m)
    mass = len(inputs)
    nonconstant_variance = sum(norms[1:]) / mass
    # The paired median signals are complements, so both have the same
    # nonconstant norms, and their AND/OR outputs are constant.
    rows = [dict(degree=r, eigenvalue=eigenvalue,
                 one_wire_variance_fraction=str(norm / mass),
                 approximate_variance=float(norm / mass),
                 pair_after_nonconstant_variance="0" if r else None)
            for r, (eigenvalue, norm) in enumerate(zip(eigenvalues, norms))]
    r = (m + 1) // 2
    boundary_vertices = comb(m, r) ** 2
    killed = boundary_vertices * r * r
    assert sum(e * a for e, a in zip(eigenvalues, norms)) == killed
    energy_before = 2 * mass * killed - n * mass * mass * Fraction(1, 2)
    products = (mass // 2) ** 2
    assert energy_before - 2 * mass * killed + 2 * n * products == 0
    return dict(block_size=m, wires=n, middle_weight=w, slice_inputs=mass,
                block_prefix=prefix, block_prefix_depth=len(prefix),
                paired_block_layer_depth=len(prefix), median_gate=[median, m + median],
                median_gate_input_scalar_heights=[h[median], h[median]],
                paired_median_nonconstant_variance=str(2 * nonconstant_variance),
                killed_faces=killed, killed_faces_per_slice_input=str(Fraction(killed, mass)),
                paired_median_reserve_before=str(energy_before),
                paired_median_reserve_after="0", spectrum=rows,
                mirror_matching_sorts_entire_central_slice=central_after_all_pairs,
                mirror_matching_neighboring_weight_failure=other_weight_unsorted,
                scope="Actual prefixes; median gate removes all nonconstant degrees at equal heights. The prefixes are not depth-efficient witnesses.")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--block-sizes", type=int, nargs="+", default=[3, 5, 7])
    parser.add_argument("--quotient-block-sizes", type=int, nargs="+", default=[3, 5, 7, 15, 31, 63])
    parser.add_argument("--output", required=True)
    args = parser.parse_args()
    result = dict(method="Integer Johnson-Laplacian moments and rational spectral projectors",
                  probes=[probe(m) for m in args.block_sizes],
                  quotient_probes=[quotient_probe(m) for m in args.quotient_block_sizes],
                  conditional_height_probes=[conditional_height_probe(h) for h in range(2, 8)],
                  status="Exact finite experiments and an elementary general construction; no improved lower bound")
    with open(args.output, "w", encoding="utf-8") as handle:
        json.dump(result, handle, indent=2)
        handle.write("\n")
    print(json.dumps({"actual_prefix_probes": len(result["probes"]),
                      "high_degree_reserve_shares": [
                          {"wires": p["wires"], "share": p["approximate_high_degree_reserve_share"]}
                          for p in result["quotient_probes"]],
                      "conditional_height_probes": result["conditional_height_probes"]}, indent=2))
