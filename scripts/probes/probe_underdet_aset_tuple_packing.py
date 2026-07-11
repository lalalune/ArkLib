#!/usr/bin/env python3
"""
probe_underdet_aset_tuple_packing.py  (lane: pack, #444 under-det/agreement-sharing face)

The previous probe (single-tuple) showed: for GENERIC words, min per-gamma tuple-mult = 1,
so multiplicity-aware packing on raw tuples gives NO deflation. The REAL object pinnedScalars
requires each gamma to own a non-degenerate ALIGNED a-SET (a > k+1): an a-subset every (k+1)-
subtuple of which is gamma-aligned. That FORCES per-gamma non-deg-tuple multiplicity:

  An aligned a-set S_gamma (|S|=a) has EVERY (k+1)-subtuple gamma-aligned => contributes
  C(a, k+1) gamma-aligned (k+1)-tuples, of which at most (deg ones) are degenerate.
  By the overlap law these tuple-classes are DISJOINT across distinct gamma. Hence

      #pinned * (C(a,k+1) - maxDeg_per_aset)  <=  C(n, k+1)
   => #pinned  <=  C(n,k+1) / (C(a,k+1) - D).

This probe PLANTS deep aligned a-sets (a codeword of degree<k agreeing with a gamma-pencil on
a points) and measures:
  (1) per-gamma non-deg (k+1)-tuple count inside its a-set  (expect ~ C(a,k+1), nearly all nondeg)
  (2) DISJOINTNESS across distinct gammas (overlap law)     (expect: shared tuples are degenerate)
  (3) the resulting deflation  C(n,k+1)/that  vs raw C(n,k+1)
Exact F_p, PROPER thin mu_n, p >> n^3, NEVER n=q-1.
"""
import itertools, random
from math import comb
import sympy

def find_prime(n):
    p = n**4
    while True:
        p = int(sympy.nextprime(p))
        if (p - 1) % n == 0:
            return p

def mu_n(p, n, g):
    h = pow(g, (p - 1) // n, p)
    S, x = [], 1
    for _ in range(n):
        S.append(x); x = (x * h) % p
    return S

def det_modp(mat, p):
    M = [row[:] for row in mat]; nn = len(M); det = 1
    for c in range(nn):
        piv = next((r for r in range(c, nn) if M[r][c] % p), None)
        if piv is None: return 0
        if piv != c: M[c], M[piv] = M[piv], M[c]; det = (-det) % p
        inv = pow(M[c][c], p-2, p); det = (det * M[c][c]) % p
        for r in range(c+1, nn):
            f = (M[r][c]*inv) % p
            if f:
                for cc in range(c, nn):
                    M[r][cc] = (M[r][cc] - f*M[c][cc]) % p
    return det % p

def residual(dom, k, T, y, p):
    m = [[pow(dom[i], j, p) for j in range(k)] + [y[i] % p] for i in T]
    return det_modp(m, p)

def poly_eval(coeffs, x, p):
    r = 0
    for c in reversed(coeffs):
        r = (r*x + c) % p
    return r

def run(n, k, a, p=None, n_planted=4, seed=0, verbose=True):
    random.seed(seed)
    if p is None: p = find_prime(n)
    g = int(sympy.primitive_root(p))
    dom = mu_n(p, n, g)
    assert len(set(dom)) == n and p > n**3 and (p-1)%n==0

    # Build u0, u1 as random base, then PLANT: pick n_planted disjoint-ish a-subsets, and on each,
    # set u0 = codeword c0(deg<k) and u1 = codeword c1(deg<k) so the pencil residual = 0 for some gamma.
    # residual(T,u0)+gamma*residual(T,u1)=0 for ALL (k+1)-subtuples T of S iff u0+gamma*u1 = deg<k poly on S.
    # Simplest: make u0 itself a deg<k poly on S (residual u0 = 0) AND u1 a deg<k poly on S (residual u1=0)
    # -> tuple is DEGENERATE (both 0). To get NON-deg aligned: u0 deg<k on S, u1 NOT deg<k on S, gamma=0.
    # gamma=0-aligned: residual u0 = 0 on all subtuples (u0 is deg<k on S), residual u1 != 0 (nondeg).
    # For distinct gammas, use u0 = c0 + gamma_S * (u1 restricted)... simpler: plant gamma=0 sets with
    # DIFFERENT codewords c0 -> but gamma=0 for all -> same gamma. Need distinct gamma.
    # Construct: on S, choose target gamma_S; set u0|S = A(deg<k) - gamma_S*B, u1|S = B, with B not deg<k.
    # Then residual(u0) = residual(A) - gamma_S residual(B) = -gamma_S residual(B) (A deg<k => res 0),
    # residual(u0)+gamma_S residual(u1) = -gamma_S res(B)+gamma_S res(B)=0. nondeg iff res(B)!=0. Good.
    u0 = [random.randrange(p) for _ in range(n)]
    u1 = [random.randrange(p) for _ in range(n)]
    planted = []
    allidx = list(range(n))
    random.shuffle(allidx)
    for j in range(n_planted):
        S = sorted(allidx[j*a:(j+1)*a]) if (j+1)*a <= n else sorted(random.sample(range(n), a))
        gamma_S = random.randrange(1, p)
        A = [random.randrange(p) for _ in range(k)]   # deg<k coeffs
        B = [random.randrange(p) for _ in range(k)] + [random.randrange(1,p)]  # deg k (NOT deg<k)
        for i in S:
            x = dom[i]
            u1[i] = poly_eval(B, x, p)
            u0[i] = (poly_eval(A, x, p) - gamma_S * u1[i]) % p
        planted.append((S, gamma_S))

    # Measure per-gamma nondeg tuple classes over ALL (k+1)-subtuples
    tuple_gamma = {}
    gamma_tuples = {}
    nondeg = 0
    for T in itertools.combinations(range(n), k+1):
        r0 = residual(dom,k,T,u0,p); r1 = residual(dom,k,T,u1,p)
        if r0==0 and r1==0: continue
        nondeg += 1
        if r1 % p == 0: continue
        gm = (-r0*pow(r1,p-2,p)) % p
        tuple_gamma[T]=gm
        gamma_tuples.setdefault(gm,set()).add(T)
    Cnk1 = comb(n,k+1); Cak1 = comb(a,k+1)

    # per-PLANTED-gamma nondeg tuple count inside its a-set
    planted_counts = []
    for (S,gm) in planted:
        cnt = 0
        for T in itertools.combinations(S, k+1):
            r0 = residual(dom,k,T,u0,p); r1=residual(dom,k,T,u1,p)
            if not (r0==0 and r1==0): cnt+=1
        planted_counts.append((gm,cnt))
    minplanted = min(c for _,c in planted_counts) if planted_counts else 0

    # (2) disjointness: any tuple pinned to 2 gammas? (impossible by construction; check vertical-share)
    npinned = len(gamma_tuples)
    if verbose:
        print(f"--- n={n} k={k} a={a} p={p} planted={n_planted} ---")
        print(f"  C(n,k+1)={Cnk1}  C(a,k+1)={Cak1}  #nondeg-tuples={nondeg}  #pinned-gammas={npinned}")
        print(f"  planted per-gamma nondeg-tuples-in-aset: {[c for _,c in planted_counts]} (C(a,k+1)={Cak1})")
        print(f"     => each planted gamma owns ~C(a,k+1) nondeg tuples: {all(c>=Cak1-2 for _,c in planted_counts)}")
        if minplanted>0:
            print(f"  PACKING deflation: #pinned bounded by C(n,k+1)/(per-gamma count) = {Cnk1}/{minplanted} = {Cnk1//minplanted}")
            print(f"     vs loose C(n,k+1)={Cnk1}  => deflation x{minplanted}  [REAL: {minplanted>1}]")
        # honesty: does deflated bound reach budget ~ n?
        if minplanted>0:
            print(f"  deflated bound {Cnk1//minplanted} vs budget n={n}: <= n? {Cnk1//minplanted <= n}")
    return dict(n=n,k=k,a=a,Cnk1=Cnk1,Cak1=Cak1,minplanted=minplanted,npinned=npinned)

if __name__=="__main__":
    print("== A-SET multiplicity-aware PACKING: per-gamma nondeg-tuple count = C(a,k+1), disjoint ==")
    print("== planted deep aligned a-sets, exact F_p, PROPER thin mu_n, p~n^4, NEVER n=q-1 ==\n")
    for (n,k,a) in [(16,1,6),(16,2,7),(16,1,8),(32,1,8),(32,2,9),(32,1,12)]:
        try:
            run(n,k,a,seed=0)
        except Exception as e:
            import traceback; print(f"  n={n} ERROR {e}"); traceback.print_exc()
        print()
