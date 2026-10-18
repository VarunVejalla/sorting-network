"""Exact aggregate crossing contraction and separator capacity constraints."""
from fractions import Fraction as F


def main():
    mu, A = F(199,10000), F(19,4)
    e = sum((F(1,d) for d in (199,110,109,106,90)), F(0))
    sigma_limit = F(1,32)/(1-e)
    print(f"Existing full-bag fringe capacity permits support at most {float(sigma_limit):.10f}")
    print(f"Existing certified support / mu = {float(F(1,50)/mu):.10f}")
    max_lambda = 1/(2*A+1)
    print(f"Ideal capacity identity nu<1 requires lambda<{float(max_lambda):.10f}")
    print(f"Ideal support/fringe cardinality ceiling amplification < {float(max_lambda/(2*(1-e)*mu)):.10f}")
    for factor in (1,2,4,16):
        sigma = factor*mu
        fringe = (1-e)*sigma
        lam = 2*fringe
        nu = 2*lam*A+(1-lam)/(2*A)
        print(f"concentration factor={factor}: ideal required fringe per side>={float(fringe):.8f}, "
              f"lambda>={float(lam):.8f}, resulting nu>={float(nu):.8f}")
    print("Relative residual examples, epsilon=1/4 (rational upper-bound model):")
    eps = F(1,4)
    for H,L in ((8,8),(4,12),(12,4),(0,8)):
        delta = L-H
        left = max(eps*H, eps*L-delta)
        right = max(eps*L, eps*H+delta)
        before = H+L-abs(delta)
        after = left+right-abs(delta)
        print(f"  H={H},L={L}: excess {before} -> at most {after}; epsilon*before={eps*before}")


if __name__ == "__main__":
    main()
