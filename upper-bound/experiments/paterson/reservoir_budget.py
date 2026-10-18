"""Exact reservoir and directional prefix bounds at root-window endpoints.

Pool-slot bounds use the original allocation without extracted level-4 cores.
Zero certified window does not mean actual native pool keys are absent.
"""
from fractions import Fraction as F


def crossing_bound(boundary, side, K, delta):
    total = F(0)
    for leaf in range(16):
        if (leaf < boundary) != (side == "left"):
            continue
        h = 0
        for size in (2,4,8,16):
            start = leaf//size*size
            if side == "left" and start+size <= boundary:
                h = size.bit_length()-1
            elif side == "right" and start >= boundary:
                h = size.bit_length()-1
        # Whole-domain membership cannot be violated. Half purity is exact
        # in the proposed first-split variant, eliminating whole-half blocks.
        if h >= 3:
            continue
        total += K*delta**h
    return total


def main():
    A, mu, delta, nu = F(19,4), F(199,10000), F(1,57), F(707,1000)
    for C in (F(300000), F(300000)/nu**2):
        K = mu*C*A**4
        T = F(16,35)*K
        # Exact allocation upper bound, including the known rounding allowances.
        Q = (C*A*A+32)/4 + (C+32+C/(4*A*A-1))/16
        print(f"C={float(C):.6f}: finest stranger budget={float(K):.6f}, "
              f"original pool slots per leaf<={float(Q):.6f}, ratio<={float(Q/K):.8f}")
        print(f"To leave <=3/35 of saturated local strangers needs >={float(F(32,35)*K):.6f} native replacements")
        positive = []
        for q in range(16):
            left = crossing_bound(q, "left", K, delta)
            right = crossing_bound(q+1, "right", K, delta)
            # Endpoint discrepancy is zero; other finest cuts use T.
            deep = (T if q not in (0,8) else 0)+(T if q+1 not in (8,16) else 0)
            margin = Q-left-right-deep
            positive.append(max(F(0),margin))
        print(f"Certified sorted native-probe windows using original pool-slot upper bound: {[int(x) for x in positive]}")
        print(f"Full-capacity direct-exchange coverage requirement: ceil(C*A^4/Q)={-((-C*A**4/Q).numerator//(-C*A**4/Q).denominator)}")


if __name__ == "__main__":
    main()
