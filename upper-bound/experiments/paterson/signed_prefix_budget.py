"""Exact scalar constraints for protected/pool prefix balancing.

These bounds assume per-leaf residual contraction at every ancestor threshold.
They are sufficient worst-case requirements, not lower bounds for all repairs.
"""
from fractions import Fraction as F


def main():
    used = F(32,35)
    slack = 1-used
    residual = slack/33  # one local leaf plus two boundaries, each <=16 leaves
    tail = sum((F(1,d) for d in (199,110,109,106,90)), F(0))
    print(f"Rebuild slack after deep errors: {slack}")
    print(f"Sufficient independent allocation: beta+2*gamma <= {slack}")
    print(f"Crude per-leaf contraction sufficient: epsilon <= {residual} = {float(residual):.10g}")
    print(f"Existing separator error: {float(tail):.10g}; two multiplicative passes: {float(tail*tail):.10g}")
    print(f"Two-pass scalar error meets target: {tail*tail <= residual}")
    print("Two passes cost 1978 with the existing separator, before pool sorting/layout.")
    print("The multiplication requires protected-core removal, support/fringe checks, and all-threshold contracts.")


if __name__ == "__main__":
    main()
