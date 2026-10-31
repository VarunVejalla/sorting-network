#!/usr/bin/env python3
"""Exhaustive small check of the ragged column-variance port inequality.

This is a sanity check for D2-PORT-VARIANCE-TRANSFER.md, not its proof.
"""
from fractions import Fraction as F
from itertools import product


def clip(x, lo, hi):
    return min(max(x - lo, 0), hi - lo)


def check(max_columns=3, max_length=3):
    checked = 0
    for n in range(1, max_columns + 1):
        length_vectors = product(range(max_length + 1), repeat=n)
        for lengths in length_vectors:
            total_length = sum(lengths)
            if not total_length:
                continue
            bands = [tuple((u, v) for u in range(length + 1)
                           for v in range(u, length + 1))
                     for length in lengths]
            for marks in product(*(range(length + 1) for length in lengths)):
                total_marks = sum(marks)
                theta = F(total_marks, total_length)
                deviations = [F(mark) - theta * length
                              for mark, length in zip(marks, lengths)]
                squared_radius = n * sum((d * d for d in deviations), F(0))
                for port in product(*bands):
                    actual = sum(clip(mark, u, v)
                                 for mark, (u, v) in zip(marks, port))
                    ideal = sum((clip(theta * length, u, v)
                                 for length, (u, v) in zip(lengths, port)), F(0))
                    assert (F(actual) - ideal) ** 2 <= squared_radius, (
                        lengths, marks, port, actual, ideal, squared_radius
                    )
                    checked += 1
    return checked


def check_rectangular_prefix_bound(max_rows=4, max_columns=4):
    """Exhaustively check the sharper one-sided rectangular prefix bound."""
    checked = 0
    for rows in range(1, max_rows + 1):
        for columns in range(1, max_columns + 1):
            for heights in product(range(rows + 1), repeat=columns):
                total = sum(heights)
                mean = F(total, columns)
                deviations = [F(x) - mean for x in heights]
                variance = sum((e * e for e in deviations), F(0)) / 2
                positive_mass = sum((max(e, F(0)) for e in deviations), F(0))
                assert positive_mass ** 2 <= F(columns, 2) * variance
                area = F(0)
                for r in range(rows + 1):
                    ideal = min(total, r * columns)
                    actual = sum(min(x, r) for x in heights)
                    defect = ideal - actual
                    assert 0 <= defect <= positive_mass
                    assert F(defect * defect) <= F(columns, 2) * variance
                    if 0 < r < rows:
                        area += defect
                for u in range(rows + 1):
                    for v in range(u, rows + 1):
                        actual_band = sum(clip(F(x), u, v)
                                          for x in heights)
                        ideal_band = sum((clip(mean, u, v)
                                          for _ in heights), F(0))
                        assert abs(F(actual_band) - ideal_band) <= positive_mass
                assert area <= variance + positive_mass / 2
                checked += 1
    return checked


def check_disjoint_area_cones(rows=18, max_columns=3, stride=9, radius=4):
    """Check sampled Lipschitz cones fit inside total prefix-defect area."""
    assert rows % stride == 0 and stride > 2 * radius
    checked = 0
    for columns in range(1, max_columns + 1):
        for heights in product(range(rows + 1), repeat=columns):
            total = sum(heights)
            defect = [min(total, r * columns)
                      - sum(min(x, r) for x in heights)
                      for r in range(rows + 1)]
            area = sum(defect[1:rows])
            cone_sum = F(0)
            for r in range(stride, rows, stride):
                center = defect[r]
                cone_sum += center + 2 * sum(
                    max(0, center - offset * columns)
                    for offset in range(1, radius + 1)
                )
            assert cone_sum <= area, (rows, columns, heights,
                                      cone_sum, area)
            checked += 1
    return checked


def compositions(length):
    """All contiguous partitions of [0,length), represented by boundaries."""
    if length == 0:
        return ((0, 0),)
    return tuple((0, *cuts, length)
                 for mask in range(1 << max(0, length - 1))
                 for cuts in ([i + 1 for i in range(length - 1)
                              if mask & (1 << i)],))


def check_port_partition_l1(max_columns=3, max_length=3):
    """Check partition-uniform l1 error aggregation for ragged columns."""
    checked = 0
    for n in range(1, max_columns + 1):
        for lengths in product(range(max_length + 1), repeat=n):
            total_length = sum(lengths)
            if not total_length:
                continue
            choices = [compositions(length) for length in lengths]
            for marks in product(*(range(length + 1) for length in lengths)):
                total_marks = sum(marks)
                theta = F(total_marks, total_length)
                deviations = [F(x) - theta * length
                              for x, length in zip(marks, lengths)]
                rhs = n * sum((d * d for d in deviations), F(0))
                for parts in product(*choices):
                    port_count = len(parts[0]) - 1
                    if any(len(boundaries) - 1 != port_count
                           for boundaries in parts):
                        continue
                    actual = [F(0) for _ in range(port_count)]
                    ideal = [F(0) for _ in range(port_count)]
                    for length, x, boundaries in zip(lengths, marks, parts):
                        for i, (u, v) in enumerate(zip(boundaries, boundaries[1:])):
                            actual[i] += F(clip(F(x), u, v))
                            ideal[i] += F(clip(theta * length, u, v))
                    errors = [a - b for a, b in zip(actual, ideal)]
                    l1 = sum(map(abs, errors), F(0))
                    assert sum(errors, F(0)) == 0
                    assert l1 * l1 <= rhs, (
                        lengths, marks, parts, errors, l1, rhs)
                    assert sum((max(e, F(0)) for e in errors), F(0)) == l1 / 2
                    checked += 1
    return checked


if __name__ == '__main__':
    print(f'exact ragged port-variance cases={check()}')
    print(f'exact rectangular prefix-variance cases='
          f'{check_rectangular_prefix_bound()}')
    print(f'exact disjoint-area-cone cases='
          f'{check_disjoint_area_cones()}')
    print(f'exact partition-l1 cases={check_port_partition_l1()}')
