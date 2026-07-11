#!/usr/bin/env python3
"""
Probe (#444 census face): pinnedScalars = image of the residual-ratio map.

CLAIM: every pinned scalar gamma (a gamma owning a non-degenerate aligned a-set)
is gamma = -R0(t)/R1(t) for some injective (k+1)-tuple t with R1(t) != 0,
where R0(t)=residual(t,u0), R1(t)=residual(t,u1) are bordered-Vandermonde dets.
Hence pinnedScalars SUBSETEQ { -R0(t)/R1(t) : t inj, R1(t)!=0 } =: ratioImage.

We verify (over small prime fields, PROPER 2-power subgroup domains, p >> n^3 where
feasible, NEVER n=q-1):
  (A) pinnedScalars == ratioImage   (the image characterization is EXACT, not just subset)
  (B) #ratioImage <= #{non-degenerate injective tuples}  (the a-priori count bound)
  (C) the over-determined cliff sanity: ratioImage can be << |F| (real reduction)
"""
import itertools, random
from itertools import combinations, permutations

def is_prime(m):
    if m < 2: return False
    i = 2
    while i*i <= m:
        if m % i == 0: return False
        i += 1
    return True

def det_modp(M, p):
    # Gaussian elimination over F_p, returns det mod p
    M = [row[:] for row in M]
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
        inv = pow(M[c][c], p-2, p)
        det = (det * M[c][c]) % p
        for r in range(c+1, n):
            f = (M[r][c] * inv) % p
            if f:
                for cc in range(c, n):
                    M[r][cc] = (M[r][cc] - f*M[c][cc]) % p
    return det % p

def bordered_det(dom_vals, k, tup, y, p):
    # bordered matrix: rows indexed by tuple elements (k+1 of them),
    # cols 0..k-1 = power columns x^j, col k = value y at that index
    M = []
    for a in range(k+1):
        idx = tup[a]
        row = []
        for b in range(k+1):
            if b < k:
                row.append(pow(dom_vals[idx], b, p))
            else:
                row.append(y[idx] % p)
        M.append(row)
    return det_modp(M, p)

def residual(dom_vals, k, tup, y, p):
    return bordered_det(dom_vals, k, tup, y, p)

def run(p, n, g, k, a, u0, u1, label):
    # domain = mu_n = { g^i } embedded into F_p, indexed 0..n-1
    dom = [pow(g, i, p) for i in range(n)]
    assert len(set(dom)) == n, "domain not injective"
    idxs = list(range(n))

    # enumerate injective (k+1)-tuples (ordered) for ratio image
    ratio_image = set()
    nondeg_tuples = 0
    for tup in permutations(idxs, k+1):
        r0 = residual(dom, k, tup, u0, p)
        r1 = residual(dom, k, tup, u1, p)
        if r1 != 0:
            nondeg_tuples += 1
            gamma = (-r0 * pow(r1, p-2, p)) % p
            ratio_image.add(gamma)
        elif r0 != 0:
            nondeg_tuples += 1  # non-degenerate but R1=0 -> no finite gamma (infinite slope)

    # pinnedScalars: gamma such that EXISTS an a-set S that is gamma-Aligned AND
    # contains a non-degenerate tuple. Aligned(gamma,S): for ALL inj (k+1)-tuples t in S,
    # R0(t)+gamma*R1(t)=0. Non-degenerate: some tuple has not(R0=0 and R1=0).
    pinned = set()
    for S in combinations(idxs, a):
        Sset = set(S)
        # for each candidate gamma, check aligned; but gamma is pinned by any nondeg tuple in S
        # collect tuples inside S
        inner = list(permutations(S, k+1))
        # find a non-degenerate tuple to pin gamma
        cand_gamma = None
        nondeg_present = False
        for tup in inner:
            r0 = residual(dom, k, tup, u0, p)
            r1 = residual(dom, k, tup, u1, p)
            if not (r0 == 0 and r1 == 0):
                nondeg_present = True
                if r1 != 0:
                    cand_gamma = (-r0 * pow(r1, p-2, p)) % p
                    break
        if not nondeg_present:
            continue
        if cand_gamma is None:
            continue  # only infinite-slope nondeg tuples; gamma not finite
        g0 = cand_gamma
        # verify Aligned for g0 over ALL inner tuples
        ok = True
        for tup in inner:
            r0 = residual(dom, k, tup, u0, p)
            r1 = residual(dom, k, tup, u1, p)
            if (r0 + g0*r1) % p != 0:
                ok = False; break
        if ok:
            pinned.add(g0)

    A_eq = (pinned == ratio_image - {x for x in []})  # raw equality check below
    subset = pinned.issubset(ratio_image)
    equal = (pinned == ratio_image)
    print(f"[{label}] p={p} n={n} k={k} a={a}: "
          f"#pinned={len(pinned)} #ratioImage={len(ratio_image)} "
          f"#nondegTuples={nondeg_tuples} |F|={p} "
          f"subset={subset} EXACT_equal={equal} "
          f"reduction(ratioImg<<F)={len(ratio_image) < p}")
    if not subset:
        print("   !!! SUBSET FAILED. pinned-ratio diff:", sorted(pinned - ratio_image)[:8])
    return subset, equal, len(pinned), len(ratio_image), nondeg_tuples, p

if __name__ == "__main__":
    random.seed(7)
    results = []
    # small feasible cases: n=2^a proper subgroup of F_p*, p prime, p = 1 mod n
    # k = a-set agreement params from the prize regime style; keep enumerable (n<=8, k<=2)
    configs = []
    # find primes p ≡ 1 mod n with a generator g of order n
    def find_g(p, n):
        # element of order exactly n: take h = primitive root^((p-1)/n)
        # find a primitive root
        def order(x):
            o=1; cur=x%p
            while cur!=1:
                cur=(cur*x)%p; o+=1
            return o
        for cand in range(2,p):
            if pow(cand,(p-1)//2,p)!=1 and order(cand)==p-1:
                g = pow(cand,(p-1)//n,p)
                return g
        return None

    test_specs = [
        # (n, k, a, p) ; p ≡ 1 mod n, PROPER subgroup (n<p-1), NEVER n=q-1
        (4, 1, 2, 41),    # p-1=40, n=4 proper
        (4, 1, 3, 41),
        (4, 2, 3, 73),    # p-1=72
        (8, 1, 2, 41),    # p-1=40, n=8 proper
        (8, 1, 3, 41),
        (8, 2, 3, 113),   # p-1=112
        (4, 1, 2, 1009),  # larger p, p>>n^3
        (8, 2, 4, 1009),
    ]
    for (n,k,a,p) in test_specs:
        if not is_prime(p): 
            print(f"skip p={p} not prime"); continue
        if (p-1) % n != 0:
            print(f"skip n={n} not | p-1={p-1}"); continue
        if n >= p-1:
            print(f"skip n={n} == q-1 (forbidden full group)"); continue
        g = find_g(p, n)
        if g is None:
            print(f"skip: no order-{n} element mod {p}"); continue
        # random stacks u0,u1 (a few per config)
        allok=True; allexact=True
        for trial in range(3):
            u0 = [random.randrange(p) for _ in range(n)]
            u1 = [random.randrange(p) for _ in range(n)]
            sub, eq, npn, nri, ndt, pp = run(p,n,g,k,a,u0,u1,f"n{n}k{k}a{a}p{p}#{trial}")
            allok = allok and sub
            allexact = allexact and eq
            results.append((sub,eq))
    nsub = sum(1 for s,e in results if s)
    nex  = sum(1 for s,e in results if e)
    print(f"\nSUMMARY: {len(results)} runs | subset holds {nsub}/{len(results)} | "
          f"EXACT image holds {nex}/{len(results)}")
