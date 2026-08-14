import numpy as np
from itertools import combinations
from math import comb, sqrt, gcd, log
from sympy import isprime

# KEY REGIME: m = b mod n with k < m < (1-delta)n. The agreement set realizable as
# roots of x^m - P (deg P < k) has e_j(S)=0 for j=1..m-k (the REALIZABILITY/Hankel
# constraints).  This is the genuine excess regime: |S| can be up to m=deg, but the
# realizability constraints (m-k of them) cut it down. The RAGGED part is what's open.
#
# Test: how does max-ragged scale with n at FIXED rate, in this regime?
# If n-independent (-> Schlickewei-Evertse, off-BGK), good. If grows ~ -> BGK.

def primitive_root_mod_p(p):
    if p == 2: return 1
    phi = p-1; m = phi; d = 2; fac=[]
    while d*d <= m:
        if m % d == 0:
            fac.append(d)
            while m % d == 0: m//=d
        d+=1
    if m>1: fac.append(m)
    for g in range(2,p):
        if all(pow(g,phi//q,p)!=1 for q in fac): return g
    return None

def find_thin_prime(n, lo):
    t = (lo-1)//n + 1
    while True:
        p = 1 + n*t
        if isprime(p): return p
        t+=1

def coeffs_of_subset(sub, powers, p):
    coeffs = [1]
    for j in sub:
        xj = powers[j]
        new = [0]*(len(coeffs)+1)
        for i,c in enumerate(coeffs):
            new[i+1] = (new[i+1] + c) % p
            new[i]   = (new[i]   - c*xj) % p
        coeffs = new
    return coeffs

def is_coset_union(ssub, n):
    for d in range(2, n+1):
        if n % d == 0:
            shift = n//d
            if all(((j+shift)%n) in ssub for j in ssub):
                return False  # it IS a coset union (proper d) -> not ragged
    return True

def analyze(p, n, k, m, g, max_enum=3_000_000):
    """Enumerate size-s subsets S of mu_n that satisfy the realizability constraints
    (coeffs[k..m-1]=0 => poly = X^m + deg<k), for the LARGEST s achievable, and report
    max ragged s. We enumerate over subsets of each size s from m down."""
    e_exp = (p-1)//n
    base = pow(g, e_exp, p)
    powers = [pow(base, j, p) for j in range(n)]
    # The agreement set S = roots of Q=x^m - P(x) deg P<k, S subset mu_n.
    # |S| = (number of mu_n roots of Q) <= m. We want MAX agreement = max over deg<k P.
    # But Q always has degree m; its mu_n-roots S satisfy prod_{x in S}(X-x) | Q.
    # If |S|=s, the cofactor has degree m-s. Max agreement <= m always.
    # To MAXIMIZE the agreement = maximize roots in mu_n of x^m - P:
    # choose P so x^m - P splits with many mu_n roots. Best: S = any s-subset of mu_n,
    # set P = x^m - prod_{x in S}(X-x)*cofactor... we need deg P < k.
    # Cleanest: take S of size s, Q0 = prod_{x in S}(X-x) (deg s). We need Q0 | (x^m - P)
    # with deg P<k. i.e. x^m - P = Q0 * H, deg H = m-s. P = x^m - Q0*H must have deg<k.
    # The TOP m-k+1 coeffs of Q0*H (degrees k..m) must match x^m (i.e. coeff_m=1, coeff_{k..m-1}=0).
    # For s=m: H=1, need Q0 = x^m + deg<k  => e_1..e_{m-k}(S)=0 (m-k constraints). 
    # We enumerate s=m case (cleanest realizability). 
    if comb(n, m) > max_enum:
        return None
    best_rag = 0; cnt=0; best_any=0; cnt_any=0
    for sub in combinations(range(n), m):
        coeffs = coeffs_of_subset(sub, powers, p)
        if all(coeffs[i] % p == 0 for i in range(k, m)):
            cnt_any+=1; best_any=m
            if is_coset_union(set(sub), n):
                cnt+=1; best_rag = m
    return (best_any, cnt_any, best_rag, cnt)

# char-0 version (work in cyclotomic field via numpy complex, high precision check)
def analyze_char0(n, k, m, max_enum=3_000_000, tol=1e-7):
    if comb(n, m) > max_enum: return None
    w = np.exp(2j*np.pi/n)
    powers = [w**j for j in range(n)]
    best_any=0; cnt_any=0; best_rag=0; cnt=0
    for sub in combinations(range(n), m):
        coeffs = np.poly([powers[j] for j in sub])  # numpy: leading first
        # coeffs[0]=1 (X^m), coeffs[i] = coeff of X^{m-i}. Need coeff of X^{k..m-1} =0
        # X^{m-i} for i=1..m-k  => indices 1..m-k must be ~0
        if all(abs(coeffs[i])<tol for i in range(1, m-k+1)):
            cnt_any+=1; best_any=m
            if is_coset_union(set(sub), n):
                cnt+=1; best_rag=m
    return (best_any,cnt_any,best_rag,cnt)

print("=== EXCESS REGIME m>k: ragged agreement at fixed rate, char-0 vs char-p ===")
print("Testing if max-ragged-|S| is n-INDEPENDENT (Schlickewei-Evertse) or grows (BGK)")
print()
print(" n  k  m   char0(any,#,rag,#rag)   charP(any,#,rag,#rag)   prime")
for n in [8,12,16,18,20]:
    k = max(2, n//4)
    # excess direction: m just above k where constraints bite but enumeration feasible
    for m in sorted(set([k+1, k+2, min(n-1, 3*k)])):
        if m<=k or m>=n: continue
        if comb(n,m) > 2_000_000: continue
        p = find_thin_prime(n, 1000)
        g = primitive_root_mod_p(p)
        c0 = analyze_char0(n,k,m)
        cp = analyze(p,n,k,m,g)
        s0 = f"{c0}" if c0 else "skip"
        sp = f"{cp}" if cp else "skip"
        print(f"{n:2d} {k:2d} {m:2d}  {s0:24s} {sp:24s} {p}")
