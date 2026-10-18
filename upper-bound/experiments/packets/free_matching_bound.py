#!/usr/bin/env python3
"""Exact arithmetic for free-product matching norm estimates.

The mathematical inputs are the homogeneous Haagerup inequality and strong
asymptotic freeness for independent random matchings; this script checks only
the finite coefficient sum and the resulting depth budget.
"""

from fractions import Fraction
from math import comb, isqrt


def ceil_sqrt(n: int) -> int:
    root = isqrt(n)
    return root if root * root == n else root + 1


def haagerup_bound(rounds: int) -> Fraction:
    numerator = sum(
        (length + 1) * ceil_sqrt(comb(rounds, length))
        for length in range(rounds + 1)
    )
    return Fraction(numerator, 2**rounds)


def fixed_point_error(
    gamma: Fraction,
    lam: Fraction,
    eta: Fraction,
    b_coarse: Fraction,
    b_fine: Fraction,
) -> tuple[Fraction, Fraction]:
    """Fixed point for an assumed two-mode affine recurrence."""
    determinant = (1 - gamma) * (1 - lam) - eta**2
    if determinant <= 0:
        raise ValueError("the assumed two-mode recurrence is not contractive")
    coarse = ((1 - lam) * b_coarse + eta * b_fine) / determinant
    fine = (eta * b_coarse + (1 - gamma) * b_fine) / determinant
    return coarse, fine


def eta_interval_for_error(
    gamma: Fraction,
    lam: Fraction,
    fresh: Fraction,
    target: Fraction,
    upper: Fraction,
) -> tuple[Fraction, Fraction]:
    """Rational bracket for the largest cross norm meeting an error target."""
    lo, hi = Fraction(0), upper
    for _ in range(40):
        mid = (lo + hi) / 2
        coarse, fine = fixed_point_error(gamma, lam, mid, fresh, fresh)
        if coarse + fine <= target:
            lo = mid
        else:
            hi = mid
    return lo, hi


def antipodal_rank_step_drift(packet_count: int) -> Fraction:
    """L1 profile error after pairing each rank with its antipodal rank."""
    if packet_count < 2 or packet_count % 2:
        raise ValueError("packet_count must be positive and even")
    span_sum = sum(
        packet_count - 1 - 2 * i for i in range(packet_count // 2)
    )
    # One packet has m equal keys at each rank; each crossed threshold adds
    # m count error. Normalize by (C*m)*(C-1) threshold-wire units.
    return Fraction(span_sum, packet_count * (packet_count - 1))


def rank_step_drift_lower_bound(
    packet_count: int,
    packet_size: int,
    rounds: int,
    centered_norm: Fraction,
) -> Fraction:
    """Pre-rebin L1 drift forced by global L2 contraction on a sorted step."""
    spectral = (1 - centered_norm) ** 2 * Fraction(packet_count + 1, 6 * packet_count)
    rounding = Fraction(rounds, 2 * packet_size)
    return max(Fraction(0), spectral - rounding)


def rank_drift_variance_lower_bound(
    packet_count: int,
    packet_size: int,
    rounds: int,
    centered_norm: Fraction,
) -> Fraction:
    """W1 rank drift forced by contraction, via the centered rank ramp.

    For a doubly stochastic product P, its row distributions have summed
    conditional variance ||r||_2^2 - ||P r||_2^2, where r_i=i-mean(i).
    Since |j-i| >= (j-i)^2/(C-1), this forces the displayed normalized W1
    drift. Integer merge-deal rounding is charged by rounds/(2*m).
    """
    if packet_count < 2 or packet_size <= 0:
        raise ValueError("packet_count must be at least two and packet_size positive")
    variance_drift = (1 - centered_norm**2) * Fraction(
        packet_count + 1, 12 * (packet_count - 1)
    )
    rounding = Fraction(rounds, 2 * packet_size)
    return max(Fraction(0), variance_drift - rounding)


def rank_drift_permutation_lower_bound(
    packet_count: int,
    packet_size: int,
    rounds: int,
    centered_norm: Fraction,
) -> Fraction:
    """Drift lower bound even after arbitrary whole-packet relabeling.

    For each rank step with h high packets, P contracts its centered L2 norm.
    Cauchy bounds the largest mass any h labels can receive, hence bounds the
    best possible permutation of the output packet counts. Rounding is then
    charged as for rank_drift_variance_lower_bound.
    """
    if packet_count < 2 or packet_size <= 0:
        raise ValueError("packet_count must be at least two and packet_size positive")
    permutation_drift = (1 - centered_norm) * Fraction(
        packet_count + 1, 3 * packet_count
    )
    rounding = Fraction(rounds, 2 * packet_size)
    return max(Fraction(0), permutation_drift - rounding)


def main() -> None:
    eight_round_bound = haagerup_bound(8)
    assert eight_round_bound == Fraction(225, 256)
    eight_round_finite = eight_round_bound + Fraction(1, 64)
    assert eight_round_finite == Fraction(229, 256)
    seven_round_bound = haagerup_bound(7)
    assert seven_round_bound == Fraction(135, 128)

    nine_round_bound = haagerup_bound(9)
    assert nine_round_bound == Fraction(11, 16)
    nine_round_finite = nine_round_bound + Fraction(1, 64)
    assert nine_round_finite == Fraction(45, 64)

    ten_round_bound = haagerup_bound(10)
    assert ten_round_bound == Fraction(69, 128)
    ten_round_finite = ten_round_bound + Fraction(1, 64)
    assert ten_round_finite == Fraction(71, 128)

    flow_energy_factor = 65
    naive_composition_rounds = next(
        r for r in range(1, 100)
        if flow_energy_factor * haagerup_bound(r) ** 2 < 1
    )
    assert naive_composition_rounds == 16
    naive_composition_budget = Fraction(
        (15 + naive_composition_rounds) * 13 + 78, 2
    )
    assert naive_composition_budget == Fraction(481, 2)

    # Conditional two-scale benchmark for nine global rounds: coarse block
    # <=45/64, fine block <=sqrt(65)/16. The coarse diagonal term dominates.
    coarse_factor = nine_round_finite
    fine_factor_sq = Fraction(65, 256)
    assert fine_factor_sq < coarse_factor**2
    cross_term_margin = 1 - coarse_factor
    assert cross_term_margin == Fraction(19, 64)

    eight_round_layers = (15 + 8) * 13 + 78
    eight_round_coefficient = Fraction(eight_round_layers, 2)
    assert eight_round_coefficient == Fraction(377, 2)
    nine_round_layers = (15 + 9) * 13 + 78
    nine_round_coefficient = Fraction(nine_round_layers, 2)
    assert nine_round_coefficient == 195

    # A sharper two-scale gate: if the coarse/fine diagonal blocks are bounded
    # by gamma and lam, and each off-diagonal block by eta, the full block
    # operator is dominated in norm by [[gamma, eta], [eta, lam]]. Its norm is
    # < 1 when eta^2 < (1-gamma)*(1-lam). Use rational upper bounds on lam.
    nine_lam = Fraction(63, 125)  # sqrt(65)/16 < 63/125
    nine_eta = Fraction(383, 1000)
    nine_margin_sq = (1 - coarse_factor) * (1 - nine_lam)
    assert nine_eta**2 < nine_margin_sq
    # More generally, different coarse->fine and fine->coarse bounds b,c are
    # admissible when bc is below this determinant margin.
    nine_cross_product = Fraction(147, 1000)
    assert nine_cross_product < nine_margin_sq

    fourteen_gamma = ten_round_finite
    fourteen_lam = Fraction(646, 1000)  # sqrt(52/125) < 646/1000
    fourteen_eta = Fraction(397, 1000)
    fourteen_margin_sq = (1 - fourteen_gamma) * (1 - fourteen_lam)
    assert fourteen_eta**2 < fourteen_margin_sq
    fourteen_cross_product = Fraction(157, 1000)
    assert fourteen_cross_product < fourteen_margin_sq

    # Conditional 14-local + 10-global split. The exact finite fan-in screen
    # gives rho <= 2/25; compare its factor-65 fine term with the global bound.
    local_prefix_rho = Fraction(2, 25)
    fourteen_ten_fine_sq = flow_energy_factor * local_prefix_rho**2
    assert fourteen_ten_fine_sq == Fraction(52, 125)
    assert ten_round_finite**2 < fourteen_ten_fine_sq
    fourteen_ten_fine_factor = float(local_prefix_rho) * 65**0.5
    fourteen_ten_cross_margin = 1 - fourteen_ten_fine_factor
    assert fourteen_ten_fine_sq < Fraction(169, 400)  # fine factor < 13/20
    fourteen_ten_layers = (14 + 10) * 13 + 78
    fourteen_ten_coefficient = Fraction(fourteen_ten_layers, 2)
    assert fourteen_ten_coefficient == 195

    # Use one normalized L2 state throughout. Each odd-count compare-split pair
    # contributes squared residual 1/2 across its two outputs. With at most
    # C/2 pairs and K thresholds, ||r||_2^2 <= C*K/4. Normalize by
    # m*sqrt(C*K), giving 1/(2*m) per round. Each mode projection may receive
    # the full residual norm, so charge all 24 rounds to both coordinates.
    # This remains conditional on the proposed recurrence.
    fresh_l2_per_round = Fraction(1, 2 * 4096)
    assert fresh_l2_per_round == Fraction(1, 8192)
    assert fresh_l2_per_round * 24 == Fraction(3, 1024)
    nine_zero = fixed_point_error(
        nine_round_finite,
        nine_lam,
        Fraction(0),
        Fraction(3, 1024),
        Fraction(3, 1024),
    )
    assert sum(nine_zero) == Fraction(19029, 1206272)
    nine_cross = fixed_point_error(
        nine_round_finite,
        nine_lam,
        Fraction(1, 5),
        Fraction(3, 1024),
        Fraction(3, 1024),
    )
    assert sum(nine_cross) == Fraction(9543, 292864)
    assert sum(fixed_point_error(
        nine_round_finite, nine_lam, Fraction(383, 1000),
        Fraction(3, 1024), Fraction(3, 1024),
    )) == Fraction(1558875, 191488)
    assert antipodal_rank_step_drift(64) == Fraction(16, 63)
    nine_rank_drift_limit = Fraction(167, 12288)
    ten_rank_drift_limit = Fraction(1043, 32768)
    assert (1 - nine_round_finite) ** 2 / 6 - Fraction(9, 8192) == nine_rank_drift_limit
    assert (1 - ten_round_finite) ** 2 / 6 - Fraction(10, 8192) == ten_rank_drift_limit
    assert rank_step_drift_lower_bound(
        65536, 4096, 9, nine_round_finite
    ) == Fraction(21889385, 1610612736)
    assert rank_step_drift_lower_bound(
        65536, 4096, 10, ten_round_finite
    ) == Fraction(68355131, 2147483648)
    nine_variance_drift_limit = (1 - nine_round_finite**2) / 12
    ten_variance_drift_limit = (1 - ten_round_finite**2) / 12
    assert nine_variance_drift_limit == Fraction(2071, 49152)
    assert ten_variance_drift_limit == Fraction(3781, 65536)
    assert rank_drift_variance_lower_bound(
        65536, 4096, 9, nine_round_finite
    ) == Fraction(132188237, 3221176320)
    assert rank_drift_variance_lower_bound(
        65536, 4096, 10, ten_round_finite
    ) == Fraction(242552597, 4294901760)
    nine_permutation_drift_limit = (1 - nine_round_finite) / 3
    ten_permutation_drift_limit = (1 - ten_round_finite) / 3
    assert nine_permutation_drift_limit == Fraction(19, 192)
    assert ten_permutation_drift_limit == Fraction(19, 128)
    assert rank_drift_permutation_lower_bound(
        65536, 4096, 9, nine_round_finite
    ) == Fraction(1231379, 12582912)
    assert rank_drift_permutation_lower_bound(
        65536, 4096, 10, ten_round_finite
    ) == Fraction(1234963, 8388608)
    sensitivity = {}
    cross_allowance = {}
    for label, gamma, lam, rounds_global, rounds_local, eta_gate in (
        ("nine_global_fifteen_local", nine_round_finite, nine_lam, 9, 15, Fraction(383, 1000)),
        ("ten_global_fourteen_local", ten_round_finite, Fraction(646, 1000), 10, 14, Fraction(397, 1000)),
    ):
        samples = {}
        fresh_per_mode = fresh_l2_per_round * (rounds_global + rounds_local)
        for eta in (Fraction(0), Fraction(1, 10), Fraction(1, 5), eta_gate):
            coarse, fine = fixed_point_error(
                gamma,
                lam,
                eta,
                fresh_per_mode,
                fresh_per_mode,
            )
            samples[str(eta)] = {
                "coarse": str(coarse),
                "fine": str(fine),
                "total": str(coarse + fine),
                "total_decimal": float(coarse + fine),
            }
        sensitivity[label] = samples
        cross_allowance[label] = {}
        for target in (Fraction(1, 50), Fraction(3, 100)):
            lo, hi = eta_interval_for_error(
                gamma, lam, fresh_per_mode, target, eta_gate
            )
            cross_allowance[label][str(target)] = {
                "lower": str(lo),
                "upper": str(hi),
                "upper_decimal": float(hi),
            }
    print({
        "eight_round_haagerup_bound": str(eight_round_bound),
        "nine_round_haagerup_bound": str(nine_round_bound),
        "seven_round_bound": str(seven_round_bound),
        "first_round_count_beating_1_over_sqrt65": naive_composition_rounds,
        "naive_factor65_composition_coefficient": str(naive_composition_budget),
        "eight_round_existential_bound": str(eight_round_finite),
        "eight_round_conditional_coefficient": str(eight_round_coefficient),
        "nine_round_existential_bound": str(nine_round_finite),
        "nine_round_two_scale_cross_term_margin": str(cross_term_margin),
        "nine_round_symmetric_block_cross_term_sufficient_bound": str(nine_eta),
        "nine_round_cross_term_margin_squared": str(nine_margin_sq),
        "nine_round_asymmetric_cross_product_bound": str(nine_cross_product),
        "nine_round_layers_per_two_bits": nine_round_layers,
        "nine_round_conditional_coefficient": str(nine_round_coefficient),
        "ten_round_haagerup_bound": str(ten_round_bound),
        "ten_round_existential_bound": str(ten_round_finite),
        "14_local_10_global_fine_factor_squared": str(fourteen_ten_fine_sq),
        "14_local_10_global_cross_term_margin": fourteen_ten_cross_margin,
        "14_local_10_global_cross_term_margin_lower_bound": "7/20",
        "14_local_10_global_symmetric_block_cross_term_sufficient_bound": str(fourteen_eta),
        "14_local_10_global_cross_term_margin_squared": str(fourteen_margin_sq),
        "14_local_10_global_asymmetric_cross_product_bound": str(fourteen_cross_product),
        "14_local_10_global_layers_per_two_bits": fourteen_ten_layers,
        "14_local_10_global_conditional_coefficient": str(fourteen_ten_coefficient),
        "conditional_two_mode_fixed_point_error": sensitivity,
        "conditional_max_cross_norm_by_error_target": cross_allowance,
        "rank_agnostic_matching_sorted_step_drift_at_64_packets": str(
            antipodal_rank_step_drift(64)
        ),
        "rank_step_drift_lower_bound_before_rebin": {
            "nine_global_rounds_at_C_65536": str(rank_step_drift_lower_bound(
                65536, 4096, 9, nine_round_finite
            )),
            "nine_global_rounds_asymptotic": str(nine_rank_drift_limit),
            "ten_global_rounds_at_C_65536": str(rank_step_drift_lower_bound(
                65536, 4096, 10, ten_round_finite
            )),
            "ten_global_rounds_asymptotic": str(ten_rank_drift_limit),
        },
        "rank_ramp_variance_drift_lower_bound_before_rebin": {
            "nine_global_rounds_at_C_65536": str(rank_drift_variance_lower_bound(
                65536, 4096, 9, nine_round_finite
            )),
            "nine_global_rounds_asymptotic": str(nine_variance_drift_limit),
            "ten_global_rounds_at_C_65536": str(rank_drift_variance_lower_bound(
                65536, 4096, 10, ten_round_finite
            )),
            "ten_global_rounds_asymptotic": str(ten_variance_drift_limit),
        },
        "rank_drift_lower_bound_after_best_packet_permutation": {
            "nine_global_rounds_at_C_65536": str(rank_drift_permutation_lower_bound(
                65536, 4096, 9, nine_round_finite
            )),
            "nine_global_rounds_asymptotic": str(nine_permutation_drift_limit),
            "ten_global_rounds_at_C_65536": str(rank_drift_permutation_lower_bound(
                65536, 4096, 10, ten_round_finite
            )),
            "ten_global_rounds_asymptotic": str(ten_permutation_drift_limit),
        },
        "conservative_normalized_l2_fresh_error_per_mode_per_stage": str(
            fresh_l2_per_round * 24
        ),
    })


if __name__ == "__main__":
    main()
