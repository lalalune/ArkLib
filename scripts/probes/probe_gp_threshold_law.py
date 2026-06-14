#!/usr/bin/env python3
"""
PROXIMITY PRIZE -- Conjecture (G): the SUPPRESSION MECHANISM and THRESHOLD LAW for the ONE
open link (F_p-genuine relations among n-th roots of unity, n=2^mu proper subgroup, p~n^beta).

ENUMERATION GROUND TRUTH (probe_gp_genuine_threshold_mitm, n=8 p=521):
  G_r=0 for r<=4; first genuine relations at r*=5; minimal genuine alpha has Norm 2p.
THIS PROBE explains it and gives the threshold law.

MECHANISM. A depth-r genuine relation is alpha = (sum of r roots) - (sum of r roots) with
alpha != 0 in Z[zeta_n] and alpha in the prime P|p (zeta -> z mod P).  In coords
v in Z[x]/(x^{n/2}+1) (length phi=n/2), a sum of r roots zeta^{a} is ANY integer vector u
with (zeta^a -> +e_{a mod phi} if a<phi else -e_{a-phi}); summing r of them gives any u with
L1(u) <= r and L1(u) == r (mod 2).  So alpha = u_x - u_y realizable at depth r  iff
v = alpha admits a split with L1(u_x),L1(u_y) <= r.  The minimal depth is
        cost(v) = ceil( L1(v) / 2 )                                   [tight: take u_x =
v^+ , u_y = v^- (positive/negative parts), pad the lighter side with cancelling pairs to
balance to a common r; r = ceil(L1(v)/2) suffices since L1(v)=L1(v^+)+L1(v^-)].

  =>  r*(n,p) = min over 0 != v in P  ceil( L1(v) / 2 )  =  ceil( lambda1_{L1}(P) / 2 ),
      lambda1_{L1}(P) = shortest L1 vector of the ideal lattice P.

VALIDATION: ceil(lambda1_{L1}/2) must equal the ENUMERATED r* (=5 for n=8,p=521).  Then we
sweep beta and watch lambda1_{L1}(P) (hence r*) GROW -- THE suppression that pushes r* up.

LOWER BOUND (why suppression is forced -- rigorous): every 0 != v in P has p | Norm(v) and
Norm(v) != 0, so |Norm(v)| >= p.  Norm(v) = prod of phi conjugate values; by AM-GM on the
phi archimedean absolute values |sigma_j(v)|,
    (1/phi) sum_j |sigma_j(v)|  >=  (prod_j |sigma_j(v)|)^{1/phi} = |Norm(v)|^{1/phi} >= p^{1/phi}.
Each |sigma_j(v)| <= L1(v) (triangle ineq, |zeta|=1), so L1(v) >= max_j|sigma_j(v)| >=
(geometric mean) >= p^{1/phi}.  Hence
    lambda1_{L1}(P) >= p^{1/phi} = n^{2 beta / n},   r* >= (1/2) n^{2 beta / n}.
For FIXED n this GROWS with beta; and r*/log2 m ~ (n^{2 beta/n}) / (2 (beta-1) log2 n) -> the
suppression depth outruns the needed log2 m once beta is large enough (the conjectured
direction).  [This is a clean lower bound on r*; the conjecture also needs r* >= (beta-1)log2 n.]

Honesty: shortest L1 vector found by EXACT direct search over small integer v with the exact
membership test v(z) == 0 (mod p) (so v in P is certified, no lattice-reduction heuristic);
search radius grows until a vector is found, and we cross-check Norm divisibility by p.
"""
import itertools, math, cmath
from collections import defaultdict

def isprime(q):
    if q<2: return False
    if q%2==0: return q==2
    d=3
    while d*d<=q:
        if q%d==0: return False
        d+=2
    return True
def factor(m):
    f=set();d=2
    while d*d<=m:
        while m%d==0:f.add(d);m//=d
        d+=1
    if m>1:f.add(m)
    return f
def primroot(p):
    fs=factor(p-1)
    for g in range(2,p):
        if all(pow(g,(p-1)//q,p)!=1 for q in fs): return g
    raise RuntimeError
def find_prime(t,mod):
    p=t+((1-(t%mod))%mod)
    if p<t:p+=mod
    while not isprime(p):p+=mod
    return p
def embeddings(n):
    phi=n//2
    return [[cmath.exp(2j*math.pi*j/n)**k for k in range(phi)] for j in range(1,n,2)]
def cyc_norm(vec, emb):
    pr=1.0+0j
    for row in emb:
        pr*=sum(vec[k]*row[k] for k in range(len(vec)))
    return round(pr.real)

def shortest_L1_in_P(n, p, z, emb, max_radius=None):
    """EXACT shortest-L1 nonzero v in P = {v : sum v_k z^k == 0 (mod p)}.
       We enumerate v by increasing L1 shell (so the first hit is the true L1 minimum),
       using the membership test v(z)==0 mod p.  Smart: fix the search over coords in a way
       that grows the L1 budget.  We iterate radius R and within it enumerate by L1 ascending.
       Returns (l1, vec, Norm)."""
    phi=n//2
    zp=[pow(z,k,p) for k in range(phi)]
    if max_radius is None:
        max_radius=max(6, int(p**(1.0/phi))+3)
    # iterate target L1 = 1,2,3,...; for each, enumerate integer vectors of that exact L1.
    # number of vectors of L1=L in phi dims is manageable for small L. Stop at first in P.
    def comps_with_l1(L, dims):
        # all integer vectors length dims with sum|.| == L  (ordered, signed)
        # generate magnitude compositions then sign assignments on nonzeros
        def mag(L,d):
            if d==1:
                yield (L,); return
            for first in range(L+1):
                for rest in mag(L-first,d-1):
                    yield (first,)+rest
        for mags in mag(L,dims):
            nz=[i for i in range(dims) if mags[i]>0]
            for signs in itertools.product((1,-1),repeat=len(nz)):
                v=list(mags)
                for idx,s in zip(nz,signs): v[idx]*=s
                yield tuple(v)
    Lcap = 2*max_radius
    for L in range(1, Lcap+1):
        for v in comps_with_l1(L, phi):
            if sum(v[k]*zp[k] for k in range(phi))%p==0:
                return L, v, cyc_norm(v, emb)
    return None, None, None

def analyze(n, p, enum_rstar=None):
    phi=n//2; g=primroot(p); z=pow(g,(p-1)//n,p); emb=embeddings(n)
    beta=math.log(p)/math.log(n); m=(p-1)//n
    l1,vec,N=shortest_L1_in_P(n,p,z,emb)
    rstar=math.ceil(l1/2)
    inP = (sum(vec[k]*pow(z,k,p) for k in range(phi))%p==0)
    pdiv = (N%p==0)
    lb = p**(1.0/phi)
    tag=''
    if enum_rstar is not None:
        tag=f"  [enum r*={enum_rstar}: {'MATCH' if rstar==enum_rstar else 'MISMATCH'}]"
    print(f" n={n:>2} p={p:>9} beta={beta:.2f} log2m={math.log2(m):>4.1f} | "
          f"shortest-L1(P)={l1:>3} (Norm={N}{'=p' if N==p else ('='+str(N//p)+'p' if N%p==0 else '')}, inP={inP}) | "
          f"r*=ceil(L1/2)={rstar:>3}{tag} | LB p^(1/phi)={lb:.2f} (=>r*>={math.ceil(lb/2)}) | "
          f"r*/log2m={rstar/math.log2(m):.2f}",flush=True)
    return dict(n=n,p=p,beta=beta,l1=l1,rstar=rstar,logm=math.log2(m),N=N)

if __name__=="__main__":
    print("=== THRESHOLD LAW  r* = ceil(shortest-L1(P)/2)  +  growth with beta ===\n",flush=True)
    print("# n=8 validate against ENUMERATED r*=5 at p=521:",flush=True)
    analyze(8,521,enum_rstar=5)
    print("\n# n=8 beta sweep (does r* grow & catch log2 m?):",flush=True)
    for bp10 in range(30,81,5):
        p=find_prime(int(round(8**(bp10/10))),8); analyze(8,p)
    print("\n# n=16 beta sweep:",flush=True)
    for bp10 in range(30,71,5):
        p=find_prime(int(round(16**(bp10/10))),16); analyze(16,p)
    print("\n# n=32 beta sweep (prize-regime n=2^5); phi=16 so L1 search is heavier:",flush=True)
    for bp10 in [30,35,40]:
        p=find_prime(int(round(32**(bp10/10))),32); analyze(32,p)
    print("\nKEY: r* tracks ceil(shortest-L1(P)/2) which is >= ceil(p^(1/phi)/2) (Minkowski/AM-GM,",flush=True)
    print("rigorous lower bound). For fixed n it grows polynomially in p (exponentially in beta),",flush=True)
    print("the SUPPRESSION that pushes the relation threshold up -- Conjecture (G)'s mechanism.",flush=True)
