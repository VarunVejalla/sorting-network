"""Exact paired-core error identities and conditional uniform depth budgets."""
from uniform_concentration import envelope


def main():
    print("Error identity examples: a,b,Delta -> left highs,right lows")
    for a,b,delta in ((3,1,0),(1,3,0),(0,0,2),(2,1,-2)):
        left = max(a,b-delta)
        right = max(b,a+delta)
        print(f"  {a},{b},{delta} -> {left},{right}")
    print("Conditional equal-block core costs, maximal block size 305532147:")
    maximum = 305532147
    for k in (1,32,4727,6080089):
        core, depth = envelope(1,maximum,k)
        combined = 2*core
        h = (combined-1).bit_length()
        sorting = h*(h+1)//2
        if k == 1:
            sorting = 1
        print(f"  K={k}: core per side<={core}, concentration<={depth}, "
              f"joint sort<={sorting}, pair depth<={depth+sorting}")
    print("These are pair-interface bounds, not actual root pair balance or a sixteen-bin schedule.")


if __name__ == "__main__":
    main()
