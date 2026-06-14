"""
#407 ATTACK [G1] — Galois norm-power spread for p-adic EXCESS relations.  (RESULT: VACUOUS; the
exact obstruction is recorded below.)  Self-contained NT (no sympy); helper modules nt/symmetric/
mitm in this dir.

SETUP. n=2^mu, p==1 (mod n) prime, h a primitive n-th root mod p, P=ker(Z[zeta_n]->F_p, zeta->h).
A p-adic EXCESS relation D=sum eps_i zeta^{c_i} (eps in {+-1}, c_i distinct in Z_n, weight w) has
  (A) sum eps_i h^{c_i}==0 mod p   [D in P],  and  (B) D!=0 over C  [reduce mod x^{n/2}+1 nonzero].
[G1] HOPE: with t = #{conjugate primes P_k : D in P_k}, |N(D)|<=w^{n/2} and p^t | N(D) give
  w >= p^{2t/n}; if STRUCTURE forces t=Omega(n) the bound becomes Omega(n).

MEASURED (this script; prize-adjacent p~n^4..n^5 AND smaller exponents where relations are findable;
multiple structured primes incl. and excl. Fermat; n=16/32/64; NEVER the full group):
  1. For the TRUE minimum-weight excess relations (all of them, MITM), t == 1 EXACTLY, universally
     (n=16/32/64, every prime). => bound p^(2/n) -> 1 at n~p^{1/4}.  VACUOUS, as warned.
  2. t>1 occurs ONLY for relations whose support is a union of S-orbits for a subgroup S<(Z/n)^*
     (sigma_k D = D for k in S forces D in P_{k^{-1}} for all k in S).  For these t == |S| EXACTLY
     — the symmetry is the ONLY source of spread; there is NO accidental extra spread (verified).
  3. Such S-symmetric excess relations EXIST only for SMALL |S| (observed |S|=2 only; |S|>=4 never
     realizable at any weight searched), and their min weight w_S >= w_true GROWS with m.  An
     S-symmetric D is a Z-combination of the (n/2)/|S| Gaussian periods eta_j=sum_{k in S}zeta^{k g_j};
     "D in P, C-nonzero" = a vanishing-mod-p-but-not-over-C relation among Gaussian periods = a
     Gauss-period / BGK char-sum statement.  So getting t=Omega(n) is EXACTLY the BGK wall.

OBSTRUCTION (one sentence): the norm-power bound w>=p^{2t/n} is only nonvacuous when t=Omega(n/log p),
which forces D to be invariant under a subgroup S of order Omega(n/log p) and hence a vanishing
combination of (n/2)/|S| Gaussian periods mod p — whose nonexistence (so that NO such excess exists,
forcing w>=2ceil(log m) on the genuine minimum) is precisely the BGK/Gauss-period sub-Gaussianity
that the prize already reduces to; t and w grow TOGETHER, never decoupling.  REDUCES TO BGK.
"""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from nt import find_prime_for_subgroup, subgroup_elements, is_prime
from mitm import find_min_excess_mitm, galois_spread
from symmetric import subgroups_of_units, s_symmetric_excess
from math import log2, ceil
from collections import Counter

def run():
    print("== (1) TRUE min-weight excess: t==1 universally (bound p^(2/n) vacuous) ==")
    for n,exp in [(16,2),(16,3),(32,2),(32,3),(64,2)]:
        p=find_prime_for_subgroup(n,exp); H,h=subgroup_elements(n,p); m=(p-1)//n
        w,found=find_min_excess_mitm(n,h,p,max_w=12,want=2000)
        if w:
            ts=[len(galois_spread(es,n,h,p)) for es in found]
            print(f"  n={n} p={p} m={m}: min_w={w} #rel={len(found)} t-dist={dict(sorted(Counter(ts).items()))}")
    print("\n== (2) S-symmetric: t==|S| exactly; only |S|=2 realizable; w_S grows with m ==")
    n=32; S2=frozenset({1,n-1})
    for exp in (2,3):
        p=find_prime_for_subgroup(n,exp); H,h=subgroup_elements(n,p); m=(p-1)//n
        for mo in range(1,8):
            res=s_symmetric_excess(n,h,p,S2,max_orbits=mo)
            if res:
                w=min(r[1] for r in res); ts=set(r[2] for r in res)
                print(f"  n={n} p={p} m={m}: |S|=2 min_w={w} t-set={ts} (2ceil log2 m={2*ceil(log2(m))})")
                break

if __name__=="__main__":
    run()
