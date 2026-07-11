import itertools, sympy, math, cmath
from collections import Counter

def mu_n(p, n):
    g = sympy.primitive_root(p)
    h = pow(g, (p-1)//n, p)
    return sorted({pow(h, k, p) for k in range(n)})

def rEnergy(G, r, p):
    cnt = Counter()
    for v in itertools.product(G, repeat=r):
        cnt[sum(v) % p] += 1
    return sum(c*c for c in cnt.values())

# verify the predicted bound  ||eta_b|| <= (q*E_r)^(1/2r)  vs ACTUAL max period
# and where (q*|G|^(2r-1))^(1/2r) sits vs sqrt(q) and sqrt(n).
def max_period(G, p, n):
    # eta_b = sum_{x in G} e_p(b x); worst over b != 0
    best = 0.0
    for b in range(1, p):
        s = 0+0j
        for x in G:
            s += cmath.exp(2j*math.pi*(b*x % p)/p)
        best = max(best, abs(s))
    return best

# small enough p to brute force max over b: use prize-regime-ish thin but tiny p
for (n, p) in [(4, 4001), (8, 8009)]:
    G = mu_n(p, n)
    mp = max_period(G, p, n)
    sq = math.sqrt(p); sn = math.sqrt(n)
    print(f"n={n} p={p} maxperiod={mp:.3f} sqrt(n)={sn:.3f} sqrt(q)={sq:.3f}")
    for r in range(1, 6):
        E = rEnergy(G, r, p)
        pred_E = (p*E)**(1/(2*r))         # actual energy bound
        pred_triv = (p*(n**(2*r-1)))**(1/(2*r))  # trivial ceiling bound
        print(f"  r={r}: (qE)^(1/2r)={pred_E:.3f}  (q|G|^(2r-1))^(1/2r)={pred_triv:.3f}  [holds:{mp<=pred_E+1e-6}]")
