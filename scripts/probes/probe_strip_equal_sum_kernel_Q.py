# Their exact experiment over Q, domain {1..8}, n=8, k=3 (m=5), d=6, b=3:
# disjoint blocks -- but at the EQUAL-SUM partition {1,8},{2,7},{3,6},{4,5}.
# Build the 10x8 syndrome-difference system and exhibit an admissible kernel vector.
from fractions import Fraction as Fr

xs = [1,2,3,4,5,6,7,8]
n, k, m = 8, 3, 5
# GRS twist multipliers eta_i = 1/prod_{l!=i}(x_i - x_l) over Q
eta = []
for i in range(n):
    pr = 1
    for l in range(n):
        if l != i: pr *= (xs[i]-xs[l])
    eta.append(Fr(1, pr))

blocks = [(0,7),(1,6),(2,5),(3,4)]   # {1,8},{2,7},{3,6},{4,5} (0-indexed)

# pencil construction over Q: B = 1 - 9T + beta*T^2, A = B + T^2, beta = 1
beta, lam, rho = 1, 1, 1
prods = [Fr(xs[a]*xs[b]) for a,b in blocks]    # 8, 14, 18, 20
gammas = [Fr(-1) + Fr(lam, p_ - beta) for p_ in prods]
print("gammas over Q:", gammas)

# error words: weights = partial fractions of rho*(1+gam)*T/V_block
errors = []
for (blk, gam) in zip(blocks, gammas):
    e = [Fr(0)]*n
    for i in blk:
        tau = Fr(1, xs[i])
        dV = Fr(1)
        for j in blk:
            if j != i: dV *= (1 - Fr(xs[j]) * tau)
        wt_twisted = rho*(1+gam)*tau / dV
        e[i] = wt_twisted / eta[i]
    errors.append(e)

def synd(word):
    return [sum(eta[i]*word[i]*Fr(xs[i])**j for i in range(n)) for j in range(m)]

synds = [synd(e) for e in errors]
g1 = gammas[0]
v = [(synds[1][j]-synds[0][j])/(gammas[1]-g1) for j in range(m)]
ok = True
for a in (2,3):
    cand = [(synds[a][j]-synds[0][j])/(gammas[a]-g1) for j in range(m)]
    if cand != v: ok = False
print("affine syndrome family over Q (the rank-deficient admissible kernel):",
      "VERIFIED" if ok else "FAILED")
print("all 8 weights nonzero:", all(errors[a][i] != 0 for a,(blk,_) in
      enumerate(zip(blocks,gammas)) for i in blocks[a]))
# affine-normalize gammas to (0,1,g,h) as in their sweep
a0, a1 = gammas[0], gammas[1]
norm = [(g_-a0)/(a1-a0) for g_ in gammas]
print("affine-normalized gamma = (0,1,g,h):", norm)
print("admissible (distinct, g,h not in {0,1}, g != h):",
      len(set(norm)) == 4 and all(x not in (Fr(0),Fr(1)) for x in norm[2:]))
