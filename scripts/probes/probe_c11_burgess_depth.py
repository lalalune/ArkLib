"""
C11: Burgess/Korobov/Heath-Brown-Konyagin DEPTH-r amplification for the char-p subgroup.

Two distinct questions, both tested over PROPER mu_n (n=2^mu, p prime, n|p-1, p>>n^3,
never n=p-1):

(Q1) BURGESS EXPONENT AT DEPTH: the incomplete-character-sum / amplified Burgess bound is
     M(n) <= C n^{1-1/r} p^{(r+1)/(4r^2)}.  Does optimizing r ever get below the
     Wick/Ramanujan target sqrt(n log(p/n))?  Equivalently: does the *exponent*
     e(r,beta) = (1 - 1/r) + beta*(r+1)/(4r^2)  (where p = n^beta) ever go below 1/2?

(Q2) THE SOFT CEILING R_r:  the moment-method consumer needs the *nonzero* energy ratio
     R_r := (sum_{b!=0} |eta_b|^{2r}/q) / ((2r-1)!! n^r) <= 1 (or bounded) to depth r ~ log m.
     We measure R_r DIRECTLY (exact, full coset enumeration) and ALSO the Burgess-supplied
     bound on R_r:  since sum_{b!=0}|eta_b|^{2r} <= (q-1) * M(n)^{2r}, the Burgess single-sum
     bound gives  R_r^Burgess = (q-1) M(n)^{2r} / (q (2r-1)!! n^r).  Does THAT <= 1 at depth?
"""
import itertools, math
from sympy import isprime, primitive_root
import cmath

def find_prime(n, beta_target, tries=200000):
    # want p prime, n | p-1, p ~ n^beta_target, NOT n=p-1
    target = int(round(n**beta_target))
    m0 = max(2, target // n)
    for m in range(m0, m0+tries):
        p = m*n + 1
        if p <= n+1:  # exclude n=p-1
            continue
        if isprime(p):
            return p, m
    return None, None

def gauss_periods(n, p):
    # mu_n = n-th roots of unity in F_p; g primitive root, h = g^{(p-1)/n}
    g = primitive_root(p)
    m = (p-1)//n
    h = pow(g, m, p)
    mu = [pow(h, i, p) % p for i in range(n)]
    # eta_b = sum_{x in mu_n} e_p(b x), b=1..p-1
    etas = []
    w = 2j*math.pi/p
    for b in range(1, p):
        s = 0+0j
        for x in mu:
            s += cmath.exp(w * ((b*x) % p))
        etas.append(abs(s))
    return etas, m

def double_fact(k):
    # (2r-1)!! for k = 2r-1
    r = 1
    i = k
    while i > 0:
        r *= i
        i -= 2
    return r

print("=== Q1: Burgess depth exponent e(r,beta) = (1-1/r) + beta(r+1)/(4r^2), beta=4 (prize) ===")
for beta in [2.0, 3.0, 4.0, 5.0]:
    best = (1e9, None)
    for r in range(1, 400):
        e = (1 - 1/r) + beta*(r+1)/(4*r*r)
        if e < best[0]:
            best = (e, r)
    print(f"  beta={beta}: min exponent over r = {best[0]:.6f} at r={best[1]}  (target 0.5; trivial=1.0)")

print()
print("=== Q2: exact NONZERO energy ratio R_r vs Burgess-supplied R_r bound, proper mu_n ===")
print(" (R_r = (sum_{b!=0}|eta_b|^{2r}/q)/((2r-1)!! n^r); want <= 1 to depth log m)")
for mu in [3,4,5]:
    n = 2**mu
    p, m = find_prime(n, 4.0)
    if p is None:
        print(f"  n={n}: no prime found"); continue
    etas, m = gauss_periods(n, p)
    q = p
    logm = math.log(m)
    Mn = max(etas)  # single-sum sup (the BGK/Burgess object)
    depth = max(1, int(round(logm)))  # r ~ log m
    print(f"  n={n} p={p} m={m} beta={math.log(p)/math.log(n):.3f} logm={logm:.2f} M(n)={Mn:.3f} sqrt(2n logm)={math.sqrt(2*n*logm):.3f}")
    for r in [1,2,3, depth, depth+2]:
        df = double_fact(2*r-1)
        wick = df * (n**r)
        # exact nonzero energy sum_{b!=0} |eta_b|^{2r}
        Sr = sum(e**(2*r) for e in etas)  # b=1..p-1 all nonzero already
        Rr_exact = (Sr/q) / wick
        # Burgess-supplied bound: sum_{b!=0} |eta_b|^{2r} <= (q-1) M(n)^{2r}
        Rr_burgess = ((q-1)*(Mn**(2*r))/q) / wick
        print(f"    r={r:3d}: R_r(exact)={Rr_exact:.4f}   R_r(Burgess-bd)={Rr_burgess:.3e}")
