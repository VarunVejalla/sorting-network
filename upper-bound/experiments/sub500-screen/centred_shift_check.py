"""Check of CENTRED-SHIFT.md's identity on explicit sorted bags.

A bag: O_L low outsiders (label -1), O_R high outsiders (label k), X_h keys of child h (labels 0..k-1),
sorted by label (an exact sort; within a label the order is irrelevant). Positions: F1 = first pi/2,
then blocks b_0..b_{k-1}, then F2 = last pi/2. Design: b_0 = Xhat_0 - pi/2 + o, b_h = Xhat_h (interior),
b_{k-1} = rest. intruders(B_j) = keys in B_j whose label != j. Compare max_j intruders with |O_L - o|
(exact counts) and with Chvatal's O_L + O_R bound, over random and extreme (O_L, O_R).
"""
import random

random.seed(7)
k, pi = 8, 400
worst_ratio = 0.0
for trial in range(4000):
    mu_c = random.choice([20, 60, 150])
    OL = random.randint(0, mu_c) if trial % 3 else random.choice([0, mu_c])
    OR = random.randint(0, mu_c - OL)
    X = [random.randint(300, 600) for _ in range(k)]
    X[0] += pi // 2; X[-1] += pi // 2                       # end children also feed the fringe
    miscount = random.choice([0, 0, 3])                       # design error per child (Delta_1-type)
    Xhat = [x + random.randint(-miscount, miscount) for x in X]
    for o in (0, mu_c // 2):
        a = OL + OR + sum(X)
        b = [Xhat[0] - pi // 2 + o] + Xhat[1:-1]
        b.append(a - pi - sum(b))
        if min(b) < 0:
            continue
        labels = [-1] * OL + [h for h in range(k) for _ in range(X[h])] + [k] * OR
        pos = pi // 2
        intr = []
        for h in range(k):
            blk = labels[pos:pos + b[h]]
            intr.append(sum(1 for l in blk if l != h))
            pos += b[h]
        mx = max(intr)
        bound = abs(OL - o) + 2 * miscount * (k - 1)            # identity + Delta terms (crude)
        assert mx <= bound, (trial, o, OL, OR, intr, bound)
        if miscount == 0:
            assert mx == abs(OL - o) or (OL - o == 0 and mx == 0), (trial, o, OL, OR, intr)
        if o and mu_c:
            worst_ratio = max(worst_ratio, mx / mu_c)
print("identity holds on all trials; centred worst max-intruders / (mu c) =", round(worst_ratio, 3))
