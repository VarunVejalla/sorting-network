"""Rational-certified entropy costs for cascaded extreme half cores.

The scalar costs are conditional on the all-supported-rank cascade adapter;
there is no proof that these cores replace the complete root repair.
"""
from fractions import Fraction as F
from uniform_concentration import certified_depth


def main():
    sigma = F(199,5000)  # twice the nominal local mu
    eps = F(1,8)
    maximum = 305532147
    for levels in (1,2,3,4):
        stage_error = eps/levels
        alphas = [2**(i+1)*sigma for i in range(levels)]
        costs = [certified_depth(alpha,stage_error) for alpha in alphas]
        # Original block sizes are multiples of 32 in the proposed arity model.
        core_total = 2*(maximum//2**levels)
        h = (core_total-1).bit_length()
        sorting = h*(h+1)//2
        pair = sum(costs)+sorting
        print(f"levels={levels}, per-stage error={stage_error}, stage depths={costs}, "
              f"concentration={sum(costs)}, core-total<={core_total}, "
              f"joint-sort<={sorting}, pair<={pair}, epoch<={3*pair}")
    print(f"Unchanged Paterson comparison contribution: {F(13,2)*989+1}")
    print("With hypothetical root cost 300: coefficient", F(13,2)*989+301)
    print("With zero root cost: coefficient", F(13,2)*989+1)


if __name__ == "__main__":
    main()
