"""Exact scalar constraints for global circulation and temporary root slack.

The temporary-slack model assumes the same linear rounded source estimate
continues to apply; its integration into the transition proof is unproved.
"""
from fractions import Fraction as F
from math import log


def main():
    A, mu, delta, nu = F(19,4), F(199,10000), F(1,57), F(707,1000)
    tail = sum((F(1,d) for d in (199,110,109,106,90)), F(0))
    fixed = (1-F(81773,89250)+F(1,62))/(2*A)+F(10,300000)
    inherited = 2*delta*A+tail/A
    gamma = (nu*mu-fixed)/(mu*inherited)
    print(f"Fixed primitive support: new mu / old mu must be < {float(F(1,50)/mu):.12g}")
    print(f"One-step rounded source-model temporary factor <= {float(gamma):.12g}")
    new_nu = 2*inherited+fixed/mu
    print(f"For temporary factor 2, rounded source model needs nu >= {float(new_nu):.12g}")
    print(f"Its stage ratio would be >= {log(float(2*A))/-log(float(new_nu)):.9f} (floating-point interpretation)")
    for C in (F(300000), F(300000)/nu**2):
        K = mu*C*A**4
        Q = (C*A*A+32)/4+(C+32+C/(4*A*A-1))/16
        cut_deficit = max(F(0), F(32,35)*K-Q)
        print(f"C={float(C):.6f}: protected count reduction sufficient at a two-error-boundary leaf >= {float(cut_deficit):.6f}")
    print("This is a count-feasibility reserve, not an extraction algorithm or an adversarial necessity theorem.")


if __name__ == "__main__":
    main()
