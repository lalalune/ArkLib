#!/usr/bin/env python3
"""
probe_i001_ore_moore_frobenius_stepanov  (issue #444 — ATTACK on idea I001)

I001 (stepanov-2adic, novelty=9): "Artin-Schreier additive (Ore) auxiliary Stepanov:
multiplicity from the Frobenius filtration, not tangency."
  Build the Stepanov auxiliary as an additive/linearized (Ore) polynomial
  L(X)=sum c_i X^{p^i}, counting 'multiplicity' as the p-adic order of vanishing in the
  Frobenius module (NOT ordinary tangency, which separability of X^n-1 pins to 1). The
  Moore-determinant rank formula on the F_2-log-lattice of mu_n is claimed to supply
  vanishing order mu = log_2 n, giving the NEW LEMMA:
     L of p-degree d, vanishing on mu_n with its first floor(log_2 n) Frobenius-Hasse
     derivatives  ==>  |mu_n cap Z(L)| * (mu+1) <= deg L,
  i.e. a Moore-minor rank-defect >= mu on a near-extremal bad set.

TARGET it must beat: M(mu_n) = max_{b!=0}|sum_{x in mu_n} e_p(bx)|. Trivial n; Johnson/L2
sqrt(n); SOTA n^{1-o(1)} (BGK). Goal sqrt(n). Regime: n=2^mu, p prime, p>>n^3, n != p-1.

================================================================================
VERDICT: NO-GAIN (refutes the literal NEW LEMMA; at best yields the TRIVIAL bound M<=n).
================================================================================

STEP 1 (structural obstruction). An Ore poly L is F_p-LINEAR; Z(L) is an F_p-subspace.
  mu_n subset F_p (the PRIME field), which is 1-dimensional over F_p. Any single nonzero
  a in mu_n F_p-spans all of F_p, so the smallest subspace containing mu_n is F_p itself:
  the unique Ore poly vanishing there is L = X^p - X, p-degree 1 but ORDINARY degree p ~ q.
  Stepanov needs deg << q, so this auxiliary is vacuous. Moreover Frobenius x->x^p is the
  IDENTITY on F_p (verified for the test primes), so the 'Frobenius filtration' on the
  x-coordinates (= mu_n) is TRIVIAL — there is no p-adic multiplicity to harvest there.

STEP 2 (the Hasse-jet reading: defect = 0, the separability wall). Impose 'f and its first
  mu Hasse derivatives vanish at every point of mu_n' = (mu+1)*n linear conditions on a
  degree-D ordinary polynomial. The NEW LEMMA needs these conditions to have rank-DEFECT
  >= mu (mu of them redundant from the 2-power tower). MEASURED rank over F_p for
  n=8,16,32,64: defect = 0 EVERY TIME (full rank n(mu+1)). The (mu+1)-jet conditions are
  INDEPENDENT — exactly because X^n-1 is separable (mu_n points are simple). So the smallest
  nonzero auxiliary has degree D = n(mu+1), and the Stepanov count obeys count*(mu+1) <= D,
  i.e. count <= n: TRIVIAL. The (mu+1) factor in I001's lemma is EXACTLY CANCELLED by the
  (mu+1)-fold degree cost of imposing the jets. NO discount from the tower.

STEP 3 (the Moore-determinant reading: wrong kind of defect). The Moore matrix [a_i^{p^j}]
  over F_p has rank 1 (NOT mu): Frobenius=id collapses every column to column 0. A Moore
  rank-defect would mean the a_i are F_p-linearly dependent, letting a small-p-degree Ore poly
  catch them — but here that just re-derives L = X^p - X (degree p, useless). The genuinely
  full-rank object is the EXPONENT Vandermonde / character table [h^{kj}] on Z/2^mu (defect 0,
  verified) — i.e. the DFT that Parseval already uses to give the L2-average sqrt(n). The
  2-power tower contributes NO extra vanishing order for a polynomial in x.

STEP 4 (the bound, all readings). Even GRANTING I001's defect, count <= D/(mu+1) with
  D ~ n(mu+1) gives count <= n. Best achievable M-bound = n = TRIVIAL, BELOW even BGK's
  n^{1-o(1)}. Confirmed against the true M(mu_n) (n=8: 7.70, n=16: 13.46) — the would-be
  Ore-Stepanov bound n never drops toward sqrt(n).

ROOT CAUSE (one sentence): mu_n lies in the 1-dimensional F_p-space F_p and X^n-1 is
separable, so there is NO additive/Frobenius multiplicity > 1 to manufacture; the only place
the 2-power structure is nontrivial (the exponent/character lattice) is already full-rank and
already exploited by Parseval. The claimed Moore-minor rank-defect >= mu is FALSE in every
operative reading.
"""
import sympy, cmath, math
from math import comb

def subgroup(p, n):
    g = sympy.primitive_root(p); h = pow(g, (p-1)//n, p)
    S, cur = [], 1
    for _ in range(n):
        S.append(cur); cur = (cur*h) % p
    assert len(set(S)) == n
    return S, h, g

def rank_mod_p(rows, ncols, p):
    M = [list(r) for r in rows]; rank=0; col=0; nr=len(M); r=0
    while r < nr and col < ncols:
        piv=None
        for i in range(r,nr):
            if M[i][col]%p: piv=i; break
        if piv is None: col+=1; continue
        M[r],M[piv]=M[piv],M[r]
        inv=pow(M[r][col],p-2,p); M[r]=[(x*inv)%p for x in M[r]]
        for i in range(nr):
            if i!=r and M[i][col]%p:
                f=M[i][col]; M[i]=[(M[i][j]-f*M[r][j])%p for j in range(ncols)]
        r+=1; rank+=1; col+=1
    return rank

def hasse_jet_rows(S, p, D, order):
    rows=[]
    for a in S:
        ap=[1]*(D+1)
        for j in range(1,D+1): ap[j]=(ap[j-1]*a)%p
        for k in range(order):
            row=[0]*(D+1)
            for j in range(k,D+1): row[j]=(comb(j,k)%p)*ap[j-k]%p
            rows.append(row)
    return rows

# proper subgroups: p prime, p >> n^3, n | p-1, n != p-1
CASES = [(8,10273),(16,81937),(32,655489),(64,5243201)]

print("="*100); print("I001 PROBE — Ore/Moore Frobenius-filtration Stepanov for M(mu_n). VERDICT: NO-GAIN."); print("="*100)

print("\n[STEP 1] Frobenius x->x^p is identity on F_p (Ore over F_p vanishing on mu_n forces X^p-X, deg p):")
import random
for _,p in CASES:
    xs=[random.randrange(1,p) for _ in range(2000)]
    print(f"  p={p}: Frob==id on F_p? {all(pow(x,p,p)==x for x in xs)}")

print("\n[STEP 2] (mu+1)-Hasse-jet rank-defect on mu_n (I001 needs >= mu); measured over F_p:")
for n,p in CASES:
    mu=n.bit_length()-1; order=mu+1
    assert (p-1)%n==0 and n!=p-1 and sympy.isprime(p) and p>n**3
    S,_,_=subgroup(p,n); ncond=n*order; D=ncond
    r=rank_mod_p(hasse_jet_rows(S,p,D,order),D+1,p)
    print(f"  n=2^{mu}={n} p={p}: ncond={ncond} rank={r} DEFECT={ncond-r} (need>={mu})  "
          f"=> count*(mu+1)<=D={D} => count<=n (TRIVIAL)")

print("\n[STEP 3] Moore matrix [a^{p^j}] over F_p (rank 1, Frobenius collapse) vs full-rank exponent DFT:")
for n,p in CASES:
    mu=n.bit_length()-1
    S,h,g=subgroup(p,n)
    A=[[pow(a,p**j,p) for j in range(mu)] for a in S]; rA=rank_mod_p(A,mu,p)
    V=[[pow(h,(k*j)%n,p) for j in range(n)] for k in range(n)]; rV=rank_mod_p(V,n,p)
    print(f"  n=2^{mu}={n}: Moore[a^p^j] rank={rA} (Frobenius=id => 1, mult=1 NOT mu); "
          f"exponent DFT rank={rV}/{n} (full, =Parseval's sqrt n)")

print("\n[STEP 4] Best Ore-Stepanov M-bound (=n) vs true M(mu_n) vs sqrt(n) vs BGK n^.99:")
print(f"  {'n':>4} {'trueM':>8} {'sqrt(n)':>8} {'I001(=n)':>9} {'BGK n^.99':>10}")
for n,p in CASES[:2]:
    S,_,_=subgroup(p,n)
    M=max(abs(sum(cmath.exp(2j*math.pi*(b*x%p)/p) for x in S)) for b in range(1,p))
    print(f"  {n:>4} {M:>8.3f} {n**0.5:>8.3f} {n:>9} {n**0.99:>10.2f}")

print("\nVERDICT: NO-GAIN. The Moore-minor rank-defect >= mu (the NEW LEMMA) is FALSE: Hasse defect=0,")
print("Frobenius-filtration rank=1. Best bound = trivial M<=n, below BGK's n^{1-o(1)}, no handle toward sqrt n.")
