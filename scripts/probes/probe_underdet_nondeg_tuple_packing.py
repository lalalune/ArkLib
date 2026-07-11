#!/usr/bin/env python3
"""
probe_underdet_nondeg_tuple_packing.py  (lane: pack, #444 under-det / agreement-sharing face)

Tests the MULTIPLICITY-AWARE PACKING lever that extends AgreementSetPacking:

  Each pinned scalar gamma owns a class of NON-DEGENERATE (k+1)-tuples (the (k+1)-subsets
  T of the domain with residual(T,u0) + gamma*residual(T,u1) = 0 and residual not both 0).
  The overlap law (gamma_eq_of_shared_nondeg_tuple) says distinct gamma's tuple-classes are
  DISJOINT.  Hence

      sum_{gamma pinned} |NondegTuples(gamma)|  <=  #(all nondeg (k+1)-tuples)  <=  C(n, k+1).

  This DEFLATES the loose  #pinned <= C(n,k+1)  by the per-gamma tuple multiplicity m_gamma:
      #pinned <= C(n,k+1) / min_gamma m_gamma.

  Verify (exact F_p, PROPER thin mu_n, p >> n^3, NEVER n=q-1):
    (A) DISJOINTNESS: no nondeg (k+1)-tuple is aligned for two distinct gammas.
    (B) The summed bound holds and is the right object.
    (C) Whether min m_gamma > 1 (so the deflation is real, not vacuous M=1).
    (D) Where #pinned lands vs budget (Johnson check) — honesty: does the sharing sustain a gap?
"""
import itertools, sys

def is_qr_prime_with_subgroup(p, n):
    return (p - 1) % n == 0

def find_prime(nmin_exp, n):
    # prize band p ~ n^4, p prime, n | p-1
    import sympy
    target = n**4
    p = target
    while True:
        p = sympy.nextprime(p)
        if (p - 1) % n == 0:
            return p

def mu_n(p, n, g):
    # n-th roots of unity = <g^((p-1)/n)>
    h = pow(g, (p - 1) // n, p)
    S = []
    x = 1
    for _ in range(n):
        S.append(x)
        x = (x * h) % p
    return sorted(set(S))

def primitive_root(p):
    import sympy
    return int(sympy.primitive_root(p))

def residual(dom, k, T, y, p):
    # bordered (k+1)x(k+1) det: cols 0..k-1 = dom^j, col k = y at the index
    # rows indexed by the (k+1) chosen domain indices in T
    m = []
    for idx in T:
        row = [pow(dom[idx], j, p) for j in range(k)] + [y[idx] % p]
        m.append(row)
    return det_modp(m, p)

def det_modp(mat, p):
    M = [row[:] for row in mat]
    n = len(M)
    det = 1
    for c in range(n):
        piv = None
        for r in range(c, n):
            if M[r][c] % p != 0:
                piv = r; break
        if piv is None:
            return 0
        if piv != c:
            M[c], M[piv] = M[piv], M[c]
            det = (-det) % p
        inv = pow(M[c][c], p - 2, p)
        det = (det * M[c][c]) % p
        for r in range(c + 1, n):
            f = (M[r][c] * inv) % p
            if f:
                for cc in range(c, n):
                    M[r][cc] = (M[r][cc] - f * M[c][cc]) % p
    return det % p

def run(n, k, p=None, seed=0, verbose=True):
    import random
    random.seed(seed)
    if p is None:
        p = find_prime(0, n)
    g = primitive_root(p)
    dom = mu_n(p, n, g)        # the PROPER thin subgroup mu_n as domain points
    assert len(dom) == n, (len(dom), n)
    assert p > n**3 and (p-1)%n==0 and len(dom)==n and dom != list(range(1,n+1))
    # u0, u1 : random "received/stack" functions on the n coords (Fin n -> F)
    u0 = [random.randrange(p) for _ in range(n)]
    u1 = [random.randrange(p) for _ in range(n)]
    idxs = list(range(n))
    # For each (k+1)-subset T (as sorted tuple of domain INDICES), compute r0,r1.
    # gamma pinned by T (if r1 != 0):  gamma = -r0 / r1  ; nondeg iff not(r0==0 and r1==0).
    tuple_gamma = {}     # T -> gamma (only nondeg with r1 != 0)
    gamma_tuples = {}    # gamma -> set of T
    nondeg_count = 0
    r1zero_nondeg = 0    # r1==0 but r0!=0 : nondeg but NOT pinned to a finite gamma (vertical)
    for T in itertools.combinations(idxs, k+1):
        r0 = residual(dom, k, T, u0, p)
        r1 = residual(dom, k, T, u1, p)
        nd = not (r0 == 0 and r1 == 0)
        if not nd:
            continue
        nondeg_count += 1
        if r1 % p == 0:
            r1zero_nondeg += 1
            continue
        gamma = (-r0 * pow(r1, p-2, p)) % p
        tuple_gamma[T] = gamma
        gamma_tuples.setdefault(gamma, set()).add(T)

    # (A) DISJOINTNESS is automatic at the TUPLE level: each nondeg T pins ONE gamma.
    # The real test: is the gamma well-defined (no T pinned to 2 gammas)? By construction yes.
    # The packing claim: distinct gammas' tuple-classes are disjoint -> guaranteed since map T->gamma.
    # Verify the SUMMED bound:
    pinned = sorted(gamma_tuples.keys())
    npinned = len(pinned)
    mult = {gm: len(ts) for gm, ts in gamma_tuples.items()}
    summ = sum(mult.values())
    from math import comb
    Cnk1 = comb(n, k+1)
    minmult = min(mult.values()) if mult else 0
    maxmult = max(mult.values()) if mult else 0

    if verbose:
        print(f"--- n={n} k={k} p={p} (p/n^4={p/n**4:.2f}) ---")
        print(f"  C(n,k+1)            = {Cnk1}")
        print(f"  #nondeg (k+1)-tuples= {nondeg_count}  (vertical r1=0 nondeg: {r1zero_nondeg})")
        print(f"  #pinned gammas      = {npinned}")
        print(f"  sum_gamma mult      = {summ}   (<= nondeg_count? {summ <= nondeg_count})")
        print(f"  min mult / max mult = {minmult} / {maxmult}")
        print(f"  loose  #pinned <= C(n,k+1)      : {npinned} <= {Cnk1}  [{npinned<=Cnk1}]")
        if minmult>0:
            print(f"  packed #pinned <= C(n,k+1)/minmult: {npinned} <= {Cnk1//minmult}  [{npinned <= Cnk1//minmult}]  (deflation x{minmult})")
        # honesty: budget = q*eps* ~ n. Is #pinned <= n (Johnson) here?
        print(f"  budget proxy n      = {n}   #pinned <= n ? {npinned <= n}  (Johnson-collapse signal)")
    return dict(n=n,k=k,p=p,npinned=npinned,summ=summ,nondeg=nondeg_count,Cnk1=Cnk1,
                minmult=minmult,maxmult=maxmult)

if __name__ == "__main__":
    print("== MULTIPLICITY-AWARE PACKING probe: disjoint nondeg-tuple classes, summed bound ==")
    print("== PROPER thin mu_n, exact F_p, p~n^4, NEVER n=q-1 ==\n")
    # k small (k=1,2), n a 2-power in the small-but-honest range; a is implicit (we use all tuples)
    for (n,k) in [(8,1),(8,2),(16,1),(16,2),(16,3),(32,1),(32,2)]:
        try:
            for seed in [0,1,2]:
                run(n,k,seed=seed,verbose=(seed==0))
        except Exception as e:
            print(f"  n={n} k={k} ERROR {e}")
        print()
