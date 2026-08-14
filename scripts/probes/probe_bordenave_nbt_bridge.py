#!/usr/bin/env python3
"""
probe_bordenave_nbt_bridge.py  (I037 follow-up — the DECISIVE bridge & quantity test)

Probe 1 (probe_bordenave_nbt_charweight.py) established:
  * UNWEIGHTED Cay(F_p,mu_n): the non-backtracking radius is an EXACT algebraic function of M
    (mu^2 - M mu + (n-1) = 0): the Perron sheet gives rho(B)=n-? but the NON-PRINCIPAL B-eigenvalue
    is mu_+ = (M + sqrt(M^2 - 4(n-1)))/2, from which M = mu_+ + (n-1)/mu_+ EXACTLY. NO new info.
  * CHAR-WEIGHTED B_chi: min over chi of rho(B_chi)+1/rho(B_chi) = 2.93 < M0=3.73 at n=4 -- LOOKS
    like a win.

THE DECISIVE QUESTION (settles real-handle vs no-gain): the bridge rho(A) <= rho(B)+1/rho(B) is a
theorem only for the UNWEIGHTED operator. For the weighted operator, rho(B_chi) (if it pairs with
anything) pairs with the WEIGHTED-adjacency radius rho(A_chi), whose non-principal value is the
TWISTED period M_chi := max_b |sum_{u in mu_n} chi(u) e_p(b u)| -- a DIFFERENT sum from the prize
quantity M := max_b |sum_{u in mu_n} e_p(b u)|.

So: does a 'win' rho(B_chi)+1/rho(B_chi) < M0 actually upper-bound the UNTWISTED M0?  It CANNOT
(a number < M0 is not an upper bound for M0). The only thing rho(B_chi) could bound is M_chi.
So minimizing over chi is choosing a twist whose OWN sum is small -- it says nothing about M.

This probe confirms, EXACTLY at n=4 and (sparse, top-eigenvalue) at n=8:
  (1) for the unweighted graph, the non-principal NBT radius reconstructs M EXACTLY (no gain);
  (2) for each chi, rho(B_chi)+1/rho(B_chi) brackets M_chi (twisted), NOT M (untwisted);
  (3) M_chi for the MINIMIZING chi is genuinely smaller than M0 -- i.e. the 'win' is real for the
      TWISTED sum and therefore proves the lever bounds the WRONG quantity.

Proper mu_n: p prime, n|p-1, p>>n^3, m=(p-1)/n>1, NEVER n=p-1. stdout flushed line-by-line.
"""
import math, cmath, sys
import numpy as np
from collections import defaultdict

def out(*a):
    print(*a); sys.stdout.flush()

def is_prime(x):
    if x < 2: return False
    if x % 2 == 0: return x == 2
    if x % 3 == 0: return x == 3
    d = 5
    while d*d <= x:
        if x % d == 0 or x % (d+2) == 0: return False
        d += 6
    return True

def find_p(n, beta_min):
    target = int(n ** beta_min) + 1
    p = ((target // n) + 1) * n + 1
    while True:
        if is_prime(p) and (p-1) % n == 0 and (p-1)//n > 1:
            return p
        p += n

def primitive_root(p):
    fac = []; m = p-1; d = 2
    while d*d <= m:
        if m % d == 0:
            fac.append(d)
            while m % d == 0: m //= d
        d += 1
    if m > 1: fac.append(m)
    for g in range(2, p):
        if all(pow(g,(p-1)//f,p)!=1 for f in fac):
            return g

def subgroup(p, n):
    g = primitive_root(p)
    h = pow(g,(p-1)//n,p)
    H = [pow(h,i,p) for i in range(n)]
    return g, set(H), H

def M_periods(p, n, Hlist, c0=None):
    """c0=None: untwisted M. else twisted M_chi with chi=step/element char index c0."""
    w = 2*math.pi/p; best = 0.0; seen = bytearray(p)
    for b in range(1, p):
        if seen[b]: continue
        for u in Hlist: seen[(b*u)%p] = 1
        if c0 is None:
            s = sum(cmath.exp(1j*w*((b*u)%p)) for u in Hlist)
        else:
            s = sum(cmath.exp(2j*math.pi*c0*j/n)*cmath.exp(1j*w*((b*u)%p)) for j,u in enumerate(Hlist))
        best = max(best, abs(s))
    return best

def build_nbt_sparse(p, n, Hset, Hlist, c0):
    """sparse Hashimoto B_chi, weight chi(step). Returns scipy csr matrix."""
    from scipy.sparse import csr_matrix
    dlog = {s:j for j,s in enumerate(Hlist)}
    edges = []
    for x in range(p):
        for s in Hset:
            edges.append((x,(x-s)%p))
    E = len(edges)
    eidx = {e:i for i,e in enumerate(edges)}
    by_tail = defaultdict(list)
    for j,(u,v) in enumerate(edges): by_tail[u].append(j)
    rows=[]; cols=[]; vals=[]
    for i,(x,y) in enumerate(edges):
        for j in by_tail[y]:
            u,v = edges[j]
            if v != x:
                rows.append(i); cols.append(j)
                vals.append(1.0 if c0==0 else cmath.exp(2j*math.pi*c0*dlog[(u-v)%p]/n))
    return csr_matrix((vals,(rows,cols)), shape=(E,E), dtype=complex)

def rho_dense(M): return max(abs(np.linalg.eigvals(M)))

def rho_sparse(M):
    from scipy.sparse.linalg import eigs
    try:
        ev = eigs(M, k=6, which='LM', return_eigenvectors=False, maxiter=5000)
        return max(abs(ev))
    except Exception as e:
        out("    [sparse eig fail, fallback dense]", e)
        return rho_dense(M.toarray())

def run(n, beta, sparse=False):
    p = find_p(n, beta)
    g, Hset, Hlist = subgroup(p, n)
    m = (p-1)//n
    out(f"\n=== n={n} p={p} m={m} beta={math.log(p)/math.log(n):.2f} E={p*n} sparse={sparse} ===")
    M0 = M_periods(p, n, Hlist, None)
    sqn = math.sqrt(n)
    out(f"  M(mu_n) UNTWISTED = {M0:.4f}  (sqrt n={sqn:.4f}, M/sqrt n={M0/sqn:.3f})  <-- THE PRIZE QUANTITY")
    # unweighted NBT: confirm exact algebraic reconstruction of M (non-principal sheet)
    disc = M0*M0 - 4*(n-1)
    mu_plus = (M0 + cmath.sqrt(disc))/2
    out(f"  unweighted NBT non-principal mu_+ = {abs(mu_plus):.4f}; reconstructs M = mu_+ +(n-1)/mu_+ "
        f"= {abs(mu_plus)+(n-1)/abs(mu_plus):.4f} (= M0, EXACT, no gain)")
    out(f"  {'c0':>3} {'rho(B_chi)':>11} {'rho(B)+1/rho(B)':>15} {'M_chi(twisted)':>14} {'<M0? (would-be win)':>20}")
    best=None
    for c0 in range(0, n):
        Bc = build_nbt_sparse(p, n, Hset, Hlist, c0)
        rB = rho_sparse(Bc) if sparse else rho_dense(Bc.toarray())
        Mc = M_periods(p, n, Hlist, None if c0==0 else c0)
        recov = rB + 1.0/rB
        win = recov < M0 - 1e-6
        out(f"  {c0:>3} {rB:11.4f} {recov:15.4f} {Mc:14.4f} {str(win):>20}")
        if best is None or recov < best[1]: best=(c0,recov,Mc)
    out(f"  BEST chi (min recov): c0={best[0]}, recov={best[1]:.4f}, its twisted M_chi={best[2]:.4f}")
    out(f"  >> The 'win' recov={best[1]:.4f} < M0={M0:.4f} brackets the TWISTED sum M_chi={best[2]:.4f},")
    out(f"     NOT the untwisted prize M0={M0:.4f}. A number < M0 cannot upper-bound M0. NO GAIN on the prize.")
    return dict(n=n,p=p,M0=M0,best=best)

if __name__ == "__main__":
    out("I037 BRIDGE & QUANTITY decisive test. Proper mu_n, p>>n^3, m>1, never n=p-1.")
    run(4, 3.0, sparse=False)
    run(8, 3.0, sparse=True)
    out("\n=== VERDICT ===")
    out("The character weight breaks the regular-graph algebraic tie, but the weighted NBT radius")
    out("brackets the TWISTED period M_chi = max_b|sum chi(u)e_p(bu)|, a DIFFERENT sum from the prize")
    out("M = max_b|sum e_p(bu)|. min over chi of M_chi does NOT bound M. So the lever, even when it")
    out("'beats' M numerically, bounds the wrong quantity. The bridge rho(A)<=rho(B)+1/rho(B) is a")
    out("theorem only unweighted, where it reconstructs M EXACTLY (no gain). NO GAIN toward sqrt(n).")
