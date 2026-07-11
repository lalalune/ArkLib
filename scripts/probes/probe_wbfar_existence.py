#!/usr/bin/env python3
"""Red-team WB-1: fraction of WB-solvable directions u1 at (p,n,k,w)=(17,8,2,2).
WBSolvable u1 <=> the 8x7 matrix [x_i^t u1_i | -x_i^s] has nontrivial kernel
<=> rank < 7. Theory: solvable set is a <= (2w+k)-dim variety => fraction ~ q^{2w+k-n} = 17^{-2}."""
import random
random.seed(371)
p, n, k, g, w = 17, 8, 2, 2, 2
dom = [pow(g, i, p) for i in range(n)]
m = (w+1) + (w+k)   # 7 columns

def rank_mod(M):
    M = [row[:] for row in M]
    rows, cols = len(M), len(M[0])
    r = 0
    for c in range(cols):
        piv = next((i for i in range(r, rows) if M[i][c] % p), None)
        if piv is None: continue
        M[r], M[piv] = M[piv], M[r]
        inv = pow(M[r][c], p-2, p)
        M[r] = [(x*inv) % p for x in M[r]]
        for i in range(rows):
            if i != r and M[i][c] % p:
                f = M[i][c]
                M[i] = [(M[i][j] - f*M[r][j]) % p for j in range(cols)]
        r += 1
        if r == rows: break
    return r

def solvable(u1):
    M = []
    for i in range(n):
        row = [pow(dom[i], t, p) * u1[i] % p for t in range(w+1)] + \
              [(-pow(dom[i], s, p)) % p for s in range(w+k)]
        M.append(row)
    return rank_mod(M) < m

trials = 4000
cnt = sum(1 for _ in range(trials) if solvable([random.randrange(p) for _ in range(n)]))
print(f"(p,n,k,w)=({p},{n},{k},{w}): solvable {cnt}/{trials} = {cnt/trials:.4f}  (theory ~ 17^-2 = {17**-2:.4f})")
# also w=1 (deeper below UDR) and w at the boundary n=2w+k (w=3: always solvable)
for w2 in (1, 3):
    m2 = (w2+1)+(w2+k)
    def solv2(u1, w2=w2, m2=m2):
        M = []
        for i in range(n):
            row = [pow(dom[i], t, p)*u1[i] % p for t in range(w2+1)] + \
                  [(-pow(dom[i], s, p)) % p for s in range(w2+k)]
            M.append(row)
        return rank_mod(M) < m2
    c2 = sum(1 for _ in range(2000) if solv2([random.randrange(p) for _ in range(n)]))
    print(f"w={w2} (m={m2}, n−m={n-m2}): solvable {c2}/2000 = {c2/2000:.4f}  (theory ~ 17^{m2-1-n})")
