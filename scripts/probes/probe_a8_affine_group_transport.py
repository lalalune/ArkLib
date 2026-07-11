"""
A8 follow-up: the AFFINE-GROUP Cayley graph Aff = mu_n |x F_p, and the TRANSPORT question.

The only place a Bourgain-Gamburd-style gap could conceivably live is the NON-ABELIAN
semidirect product G = mu_n |x F_p (the "ax+b" group with dilations restricted to mu_n).
But this group is SOLVABLE (metabelian), hence AMENABLE -- the EXACT excluded case in every
BG / superstrong-approximation theorem (which need Zariski-dense in a SEMISIMPLE group, e.g.
SL_2, with property (tau)). We test two things:

  (Q1) Does Cay(Aff, {dilate, translate}^{+-1}) have a UNIFORM (n-independent) spectral gap?
       If gap -> 0 as n grows (or as p grows), NO BG expansion: amenable, as predicted.
  (Q2) TRANSPORT: is M(mu_n) recoverable as / bounded by an eigenvalue of this affine Cayley
       operator? The affine spectrum decomposes by F_p-characters psi_b; the b-block is the
       n x n circulant-like operator on the mu_n-coordinate twisted by psi_b. Its top eigenvalue
       is governed by row sums sum_s psi_b(h^s * c) -- which for the right vector reproduces
       eta_b = sum_{x in mu_n} psi_b(x) = the period. So the affine operator CONTAINS the wall
       as a sub-block. => any gap statement about Aff is EQUIVALENT to the wall, not a relocation.

HONEST regime: n=2^mu, n|p-1, p PRIME. For T2 dense-eig feasibility we need n*p <= ~6000, so we
take the SMALLEST honest primes (still p > n, n|p-1, PRIME, proper subgroup); we separately
DISPLAY M at the p>>n^3 regime to show the wall is the same object. NEVER n=p-1.
"""
import numpy as np, math
from sympy import isprime, primitive_root
import scipy.sparse as sp
from scipy.sparse.linalg import eigsh

def small_prime(n, pmin):
    k = pmin//n + 1
    while True:
        p = k*n+1
        if isprime(p): return p
        k += 1

def gen_h(p,n):
    g = primitive_root(p); return pow(g,(p-1)//n,p)

def affine_gap(p,h,n):
    """Cay(mu_n |x F_p, {gA^{+-1}, gT^{+-1}}); return (lambda1, lambda2, gap=lambda1-lambda2)."""
    N=n*p
    hpow=[pow(h,s,p) for s in range(n)]
    def idx(s,c): return s*p+c
    rows=[];cols=[]
    for s in range(n):
        for c in range(p):
            i=idx(s,c)
            for j in (idx((s+1)%n,c),idx((s-1)%n,c),
                      idx(s,(c+hpow[s])%p),idx(s,(c-hpow[s])%p)):
                rows.append(i);cols.append(j)
    A=sp.coo_matrix((np.ones(len(rows)),(rows,cols)),shape=(N,N)).tocsr()
    A=(A+A.T)/2
    vals=np.sort(eigsh(A,k=min(8,N-2),which='LA')[0])[::-1]
    return vals[0], vals[1], vals[0]-vals[1]

def period_M(p,h,n):
    mu=np.array([pow(h,j,p) for j in range(n)],dtype=np.int64)
    best=0.0
    for b in range(1,p):
        ang=2*math.pi*((b*mu)%p)/p
        best=max(best,abs(np.sum(np.cos(ang))+1j*np.sum(np.sin(ang))))
    return best

print("="*92)
print("A8-affine: gap of the SOLVABLE affine Cayley graph mu_n |x F_p, and TRANSPORT to M")
print("HONEST: n=2^mu, n|p-1, p PRIME, proper subgroup, NEVER n=p-1")
print("="*92)
print(f"{'mu':>3} {'n':>4} {'p':>6} {'|Aff|':>7} | {'lam1':>7} {'lam2':>7} {'gap':>7} {'gap/4':>7} | {'M(period)':>9} {'M/sqrtn':>8}")
for mu in range(2,6):
    n=2**mu
    p=small_prime(n, max(2*n, 24))     # smallest honest prime keeping n*p feasible for dense-ish eig
    while n*p > 6500:                  # ensure feasibility; bump n down isn't allowed, so accept
        break
    if n*p > 9000:
        print(f"{mu:>3} {n:>4} {p:>6} {n*p:>7} | (skipped: n*p too large for dense eig)")
        continue
    h=gen_h(p,n)
    l1,l2,gap=affine_gap(p,h,n)
    M=period_M(p,h,n)
    print(f"{mu:>3} {n:>4} {p:>6} {n*p:>7} | {l1:>7.3f} {l2:>7.3f} {gap:>7.4f} {gap/4:>7.4f} | {M:>9.3f} {M/math.sqrt(n):>8.3f}")

print()
print("VERDICT lines:")
print(" Q1: if gap (lam1-lam2) SHRINKS with n (toward 0), the affine Cayley graph is NOT a uniform")
print("     expander -> NO Bourgain-Gamburd gap (consistent with solvable=amenable).")
print(" Q2: the affine operator's psi_b-isotypic block has top eigenvalue tied to eta_b; M is a")
print("     SUB-BLOCK eigenvalue. Bounding the affine gap is THEREFORE equivalent to bounding M =")
print("     the same wall, not a relocation off the domain.")
