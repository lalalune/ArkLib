import numpy as np
from itertools import combinations
from math import comb, sqrt, gcd, log
from sympy import isprime

# DECISIVE EXPERIMENT.
# The real agreement model (matching FarThresholdMaximality + the agreement poly):
#   monomial line x^a + gamma x^b (TWO terms), agrees with codeword c (deg<k) at x in mu_n iff
#   x^a + gamma x^b - c(x) = 0.  On mu_n this is a (k+2)-sparse poly P.
#   S = roots of P in mu_n.  Max over (gamma, c) of |S|, and the ragged part.
#
# We MAXIMIZE agreement = find the (gamma,c) giving the most mu_n roots, and report
# the ragged (non-coset-union) size. We want to know:
#   (Q1) Is max-ragged n-INDEPENDENT at fixed k (Schlickewei-Evertse)? 
#   (Q2) Does char-p ever EXCEED char-0 ragged? (the BGK / char-faithfulness question)
#   (Q3) Does ragged-count match the Kambire budget ~ n (BGK) or stay O(k) (off-BGK)?
#
# Model: fix direction (a,b). For each candidate agreement set S (subset of mu_n),
# S is realizable by SOME (gamma,c) iff the |S| equations { x_i^a + gamma x_i^b = c(x_i) }
# (c deg<k, gamma scalar) are consistent: i.e. the points (x_i^b, x_i^a evaluated...) 
# Linear system: unknowns = gamma (1) + c coeffs (k) = k+1 unknowns.
# Equation at x_i:  c_0 + c_1 x_i + ... + c_{k-1} x_i^{k-1} - gamma x_i^b = - x_i^a.
# So S is realizable iff the |S|x(k+1) Vandermonde-like system [1,x_i,...,x_i^{k-1}, -x_i^b | -x_i^a]
# is consistent. |S| <= k+1 always solvable (generic). For |S| > k+1: consistency = rank condition.
# MAX agreement = max |S| with the augmented matrix rank = coefficient matrix rank.
#
# This is the REALIZABILITY/HANKEL constraint (single deg-<k poly) the thread flags.

def primitive_root_mod_p(p):
    if p == 2: return 1
    phi = p-1; mm = phi; d = 2; fac=[]
    while d*d <= mm:
        if mm % d == 0:
            fac.append(d)
            while mm % d == 0: mm//=d
        d+=1
    if mm>1: fac.append(mm)
    for g in range(2,p):
        if all(pow(g,phi//q,p)!=1 for q in fac): return g
    return None

def find_thin_prime(n, lo):
    t = (lo-1)//n + 1
    while True:
        p = 1 + n*t
        if isprime(p): return p
        t+=1

def rank_modp(M, p):
    M = [[x % p for x in row] for row in M]
    rows = len(M); cols = len(M[0]) if rows else 0
    r = 0
    for col in range(cols):
        piv = None
        for i in range(r, rows):
            if M[i][col] % p != 0:
                piv = i; break
        if piv is None: continue
        M[r], M[piv] = M[piv], M[r]
        inv = pow(M[r][col], p-2, p)
        M[r] = [(x*inv)%p for x in M[r]]
        for i in range(rows):
            if i!=r and M[i][col]%p!=0:
                f = M[i][col]
                M[i] = [(M[i][j]-f*M[r][j])%p for j in range(cols)]
        r+=1
        if r==rows: break
    return r

def is_coset_union(ssub, n):
    for d in range(2, n+1):
        if n % d == 0:
            shift = n//d
            if all(((j+shift)%n) in ssub for j in ssub):
                return False
    return True

def max_realizable_charp(p, n, k, a, b, g):
    """Max |S| (subset of mu_n) realizable as agreement of line x^a+gamma x^b with a single
    deg-<k codeword over F_p, plus the max ragged such |S|. Realizable iff augmented rank=coeff rank."""
    e_exp=(p-1)//n; base=pow(g,e_exp,p)
    powers=[pow(base,j,p) for j in range(n)]
    # for each subset S (small n only), coeff matrix cols: [x^0..x^{k-1}, -x^b], aug col -x^a
    best_any=0; best_rag=0; cnt_rag=0; n_any=0
    # search by size descending; cap enumeration
    for s in range(n, 0, -1):
        if comb(n,s) > 800_000:
            continue
        found_any=False; found_rag=False; this_cnt=0
        for sub in combinations(range(n), s):
            coeff=[]; aug=[]
            for j in sub:
                xj=powers[j]
                row=[pow(xj,t,p) for t in range(k)] + [(-pow(xj,b,p))%p]
                coeff.append(row[:])
                aug.append(row + [(-pow(xj,a,p))%p])
            rc=rank_modp(coeff,p); ra=rank_modp(aug,p)
            if rc==ra:  # consistent => realizable
                found_any=True
                if best_any< s: best_any=s
                if is_coset_union(set(sub),n):
                    found_rag=True; this_cnt+=1
                    if best_rag< s: best_rag=s
        if found_any and best_any>=s:
            # record ragged count at the top realizable ragged size
            if found_rag and best_rag==s:
                cnt_rag=this_cnt
            if best_any> k+1:  # only interesting if exceeds generic
                pass
            if best_any>=s and s<=best_any:
                # once we found the max any, also need max rag; continue down a bit
                if best_rag>0 and s< best_rag:
                    break
        if best_any>0 and s < best_any - 2:
            break
    return best_any, best_rag, cnt_rag

print("=== REALIZABILITY-based max agreement & ragged (char-p), genuine direction ===")
print("Direction (a,b) with d=gcd(a-b,n)>=2 (genuine ragged), low exponents.")
print(" n  k  (a,b)  d  maxAny  maxRagged  Johnson  k+1")
for n in [8,12,16]:
    p=find_thin_prime(n,1000); g=primitive_root_mod_p(p)
    k=max(2,n//4)
    for d in [2,4]:
        if n%d: continue
        # genuine direction: a-b = d (so gcd(a-b,n) has factor d); low exponents
        a = k+d; b = k
        if a>=n or b>=n: continue
        dd=gcd(a-b,n)
        ba,br,cr = max_realizable_charp(p,n,k,a,b,g)
        print(f"{n:2d} {k:2d} ({a},{b})  {dd}   {ba:3d}     {br:3d}      {sqrt(n*k):.2f}    {k+1}")
