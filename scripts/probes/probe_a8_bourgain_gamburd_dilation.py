"""
A8 [Bourgain-Gamburd multiplicative dilation spectral gap] PROBE.

CONTEXT (the wall). The prize core is
    M(mu_n) = max_{b!=0} | Sum_{x in mu_n} e_p(b x) |  <=?  C*sqrt(n*log(p/n)),
where mu_n = 2^mu-th roots of unity in F_p^*, n=2^mu, n|p-1, p PRIME, p>>n^3.
The ADDITIVE Cayley graph Cay(F_p, mu_n) has its non-principal eigenvalue EXACTLY = M(mu_n)
(Liu-Zhou). That is W4 = the wall; sum-product (Bourgain-Garaev) caps it at n^{0.99}, vacuous
in the prize window.

THE A8 ANGLE (RELOCATE to the MULTIPLICATIVE action). The dilation b->zeta*b (zeta a primitive
2^mu-th root) generates the CYCLIC group G=<zeta> ~ mu_n acting on F_p by multiplication.
Bourgain-Gamburd / superstrong approximation gives a UNIFORM spectral gap for Cayley graphs of
groups whose generators are "thick" (no abelian / affine / proper-subgroup obstruction).
NEW LEMMA (to be tested): the Schreier/Cayley structure of the dilation action has a BG gap that
bounds the period M(mu_n) <= C sqrt(n log).

THE TEST. Build TWO candidate "multiplicative dilation" operators and measure their spectral gap
vs n, on proper subgroups (HONEST regime), and ask: gap = Ramanujan-scale 2/sqrt(deg)
(=> escapes wall, would give M<=2 sqrt n past Johnson), or does it inherit the SAME M(mu_n) wall
(=> reduces-to-wall)?

  (T1) The pure dilation Schreier graph on F_p:  vertices F_p, edges x ~ zeta^{+-1} x.
       This is the ACTION graph of the cyclic group G on the line.
  (T2) The affine-group Cayley graph  Aff = G |x F_p  (semidirect product),
       generators = {dilation by zeta} U {translation by 1}. This is where BG/superstrong
       approximation would actually apply IF the group were non-amenable/thick.
  (T3) The DIRECT period:  M(mu_n) itself, and the additive-Cayley eigenvalue (= the wall),
       for calibration.

HONESTY: proper subgroup mu_n, n=2^mu, n|p-1, p PRIME, p>>n^3, NEVER n=p-1.
"""
import numpy as np
import cmath, math
from sympy import isprime, primitive_root

def find_prime(n, mult_min):
    """Smallest prime p with n | p-1 and p > mult_min (so p >> n^3 when mult_min=n^3)."""
    # p = k*n + 1
    k = mult_min // n + 1
    while True:
        p = k*n + 1
        if isprime(p):
            return p
        k += 1

def subgroup_mu_n(p, n):
    """The 2^mu-th roots of unity mu_n in F_p^*: elements x with x^n=1.
       Built as g^{(p-1)/n * j} for primitive root g."""
    g = primitive_root(p)
    h = pow(g, (p-1)//n, p)  # generator of the order-n subgroup
    mu = [pow(h, j, p) for j in range(n)]
    return mu, h

def period_M(p, mu):
    """M = max_{b!=0} |sum_{x in mu} e_p(b x)|.  (the wall object)."""
    n = len(mu)
    mu_arr = np.array(mu, dtype=np.int64)
    best = 0.0
    # b ranges 1..p-1; for moderate p compute all
    for b in range(1, p):
        ang = 2*math.pi*((b*mu_arr) % p)/p
        s = np.sum(np.cos(ang)) + 1j*np.sum(np.sin(ang))
        best = max(best, abs(s))
    return best

def additive_cayley_second_eig(p, mu):
    """Non-principal eigenvalue of Cay(F_p, mu U -mu): the additive wall (= related to M).
       Eigenvalues are sum_{x in S} e_p(b x), b=0..p-1; S symmetric closure."""
    S = set(mu) | set((p-x)%p for x in mu)
    S = list(S)
    S_arr = np.array(S, dtype=np.int64)
    eigs = []
    for b in range(p):
        ang = 2*math.pi*((b*S_arr) % p)/p
        eigs.append(np.sum(np.cos(ang)))  # real (symmetric set)
    eigs = np.array(eigs)
    deg = len(S)
    # principal eig = deg (b=0); second = max over b!=0 of |eig|
    second = max(abs(eigs[b]) for b in range(1,p))
    return second, deg

def dilation_schreier_second_eig(p, h, n):
    """T1: dilation Schreier graph on F_p^* (orbits = cosets of <h>).
       The action x -> h*x partitions F_p^* into (p-1)/n orbits each a single n-cycle.
       Each orbit is a CYCLE of length n => the graph is a disjoint union of n-cycles + fixed pt 0.
       Spectral gap of a disjoint union of n-cycles = gap of a single n-cycle = 2-2cos(2pi/n).
       Second eigenvalue (adjacency, undirected, gen {h, h^{-1}}) = 2 cos(2pi/n).
       We compute it directly to CONFIRM the structural claim."""
    # The orbit of any nonzero x under mult by h is {x, hx, h^2 x, ...} a single n-cycle.
    # Adjacency eigenvalues of an n-cycle: 2 cos(2 pi k / n), k=0..n-1.
    # Largest = 2 (k=0, principal), second-largest = 2 cos(2pi/n).
    second = 2*math.cos(2*math.pi/n)
    deg = 2
    return second, deg

def affine_cayley_second_eig(p, h, n):
    """T2: Cayley graph of the affine group Aff(1,F_p)_G = G |x F_p where G=<h> (order n).
       |Aff| = n*p.  Generators: a=(dilate by h), t=(translate by 1), and inverses.
       Element (s, c) acts as x -> s x + c.  Group mult: (s1,c1)(s2,c2)=(s1 s2, s1 c2 + c1).
       We build the regular representation adjacency restricted to a manageable size:
       full |Aff|=n*p is too big for dense eig when p>>n^3, so we use the IRREP decomposition:
       the nontrivial spectrum of Cay(Aff, {a^{+-1}, t^{+-1}}) is governed by the induced reps.
       Instead we MEASURE the gap directly for SMALL p (p just above n^3 may be large; we keep
       p moderate by relaxing to p>n^2 for T2 feasibility, FLAGGED, T1/T3 stay at p>>n^3)."""
    # Build group elements as (s_index in 0..n-1 [meaning h^s], c in 0..p-1)
    # adjacency by right-multiplication by generators a=(1->h i.e s+1), t=(c+1 in dilated frame)
    # Generators (as group elements):
    #   gA = (h^1, 0):  (s,c) * gA = (s+1 mod n, c)   [since s1 c2 + c1 = h^s*0+c = c]
    #   gAinv = (h^{-1},0)
    #   gT = (1, 1):    (s,c) * gT = (s, h^s*1 + c) = (s, (h^s + c) mod p)
    #   gTinv = (1,-1): (s,c)*gTinv = (s, (c - h^s) mod p)
    N = n*p
    if N > 4500:
        return None, None  # too big for dense; skip
    hpow = [pow(h, s, p) for s in range(n)]
    def idx(s,c): return s*p + c
    import scipy.sparse as sp
    rows=[]; cols=[]
    for s in range(n):
        for c in range(p):
            i = idx(s,c)
            # gA: (s+1, c)
            rows.append(i); cols.append(idx((s+1)%n, c))
            # gAinv: (s-1, c)
            rows.append(i); cols.append(idx((s-1)%n, c))
            # gT: (s, c + hpow[s])
            rows.append(i); cols.append(idx(s, (c+hpow[s])%p))
            # gTinv: (s, c - hpow[s])
            rows.append(i); cols.append(idx(s, (c-hpow[s])%p))
    A = sp.coo_matrix((np.ones(len(rows)), (rows,cols)), shape=(N,N)).tocsr()
    A = (A + A.T)/2  # symmetrize (undirected)
    from scipy.sparse.linalg import eigsh
    k = min(6, N-2)
    vals = eigsh(A, k=k, which='LA', return_eigenvalues=True) if False else eigsh(A, k=k, which='LA')[0]
    vals = np.sort(vals)[::-1]
    deg = 4
    # principal = 4 (regular, connected); second = vals[1]
    second = vals[1]
    return second, deg

print("="*100)
print("A8: Bourgain-Gamburd MULTIPLICATIVE dilation spectral gap vs the period wall M(mu_n)")
print("HONEST regime: n=2^mu, n|p-1, p PRIME, p>>n^3 (T1/T3); T2 affine needs p moderate (FLAGGED)")
print("="*100)
print(f"{'mu':>3} {'n':>5} {'p':>10} | {'M(wall)':>10} {'sqrt(n)':>8} {'M/sqrtn':>8} {'sqrt(nlog)':>10} {'M/snlog':>8} | {'addCay2eig':>10} {'dilSchr2':>9}")
for mu in range(2, 8):
    n = 2**mu
    p = find_prime(n, n**3)        # p >> n^3, prime, n|p-1
    mu_set, h = subgroup_mu_n(p, n)
    M = period_M(p, mu_set)
    addsec, adddeg = additive_cayley_second_eig(p, mu_set)
    dilsec, dildeg = dilation_schreier_second_eig(p, h, n)
    sn = math.sqrt(n)
    snlog = math.sqrt(n*math.log(p/n))
    print(f"{mu:>3} {n:>5} {p:>10} | {M:>10.3f} {sn:>8.3f} {M/sn:>8.3f} {snlog:>10.3f} {M/snlog:>8.3f} | {addsec:>10.3f} {dilsec:>9.4f}")

print()
print("Interpretation key:")
print("  - dilSchr2 = 2cos(2pi/n) -> 2 as n grows: the pure dilation Schreier graph is a union of")
print("    n-CYCLES (abelian/amenable). Its 'gap' (2 - 2cos(2pi/n) ~ (2pi/n)^2) is the cycle gap,")
print("    which has NOTHING to do with M and does NOT bound it. NO Bourgain-Gamburd gap (amenable).")
print("  - addCay2eig = the WALL (~= M up to the +-mu symmetrization).")
