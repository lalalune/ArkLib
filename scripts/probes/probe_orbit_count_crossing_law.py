#!/usr/bin/env python3
"""
probe_orbit_count_crossing_law.py  (#407)

Numerically confirms the ORBIT-COUNT CROSSING LAW factorization:

    I_pencil(delta) = N_pencil(delta) * S,   S = n / gcd(b-a, n)

where, for a monomial pencil (a,b) on a multiplicative domain mu_n = <omega> subset F_q^*:
    I_pencil(delta) = #{ alpha in F_q : x^a + alpha*x^b is delta-close to RS[k] }
                    = #{ alpha : exists g, deg g < k, agree(alpha,g) >= (1-delta)*n }
The Action-Orbit theorem (Chai-Fan 2026/861, in-tree as agreement_orbit_invariance) says the bad-
alpha set is a union of orbits of the cyclic group <omega^{b-a}> acting by alpha |-> alpha*omega^{b-a},
each orbit of size S = ord(omega^{b-a}) = n / gcd(b-a, n).

Hence the crossing law:  I_pencil <= n  <=>  N_pencil <= gcd(b-a, n).

This probe brute-forces I (count bad alphas), then independently counts the orbits N of the bad set
under alpha |-> alpha*omega^{b-a}, and checks I == N*S exactly, plus the crossing equivalence.
"""

def main():
    # Field F_q, q prime, with a multiplicative subgroup mu_n of order n.
    # Pick q prime with n | q-1 so a primitive n-th root of unity exists.
    cases = []

    # (q, n, k) : q prime, n | q-1, k = rate dim
    # n=8, q=521 (520 = 8*65), rate 1/4 -> k=2  (matches kb note prize regime)
    cases.append((521, 8, 2))
    # n=8, q=17 (16=8*2)
    cases.append((17, 8, 2))
    # n=6, q=7 (6 | 6)
    cases.append((7, 6, 2))
    # n=12, q=13
    cases.append((13, 12, 3))
    # n=10, q=11
    cases.append((11, 10, 3))

    for (q, n, k) in cases:
        assert (q - 1) % n == 0, f"need n|q-1: q={q}, n={n}"
        # find primitive n-th root of unity omega in F_q
        # take a generator-ish element: find any element of order exactly n
        omega = None
        for cand in range(2, q):
            # order of cand divides q-1; we want pow == 1 at n and not earlier divisor
            if pow(cand, n, q) == 1:
                # check order exactly n
                ok = True
                d = 1
                while d < n:
                    if n % d == 0 and pow(cand, d, q) == 1:
                        ok = False
                        break
                    d += 1
                if ok:
                    omega = cand
                    break
        assert omega is not None, f"no prim {n}-th root in F_{q}"
        D = [pow(omega, i, q) for i in range(n)]  # the domain mu_n

        from math import gcd
        print(f"=== q={q}, n={n}, k={k}, omega={omega} ===")

        # iterate over a few far pencils (a,b), avoiding correlated subgroup directions
        pencils = []
        for a in range(0, n):
            for b in range(a+1, n+1):
                pencils.append((a, b))

        # precompute, for a delta budget t = floor((1-delta)*n) agreement threshold,
        # the bad-alpha set: alpha bad iff exists g deg<k with agreement >= t.
        # We test the *maximal* nontrivial threshold t where the structure is visible.
        for (a, b) in pencils[:12]:
            d = gcd(b - a, n)
            S = n // d
            # agreement threshold: require agreement on >= n - 1 points (delta small), a clean regime
            # We sweep a couple thresholds and report the first with nontrivial bad set.
            for t in [n - 1, n - 2]:
                # bad-alpha set
                bad = []
                for alpha in range(0, q):
                    # exists g, deg<k, #{x in D: x^a+alpha x^b == g(x)} >= t ?
                    # equivalently: exists a subset A of D, |A|>=t, and a poly g deg<k interpolating
                    # the points (x, x^a+alpha x^b) for x in A.  For |A|>=k the interpolant is unique;
                    # g deg<k exists iff those |A| points lie on a single deg<k poly.
                    # Brute: for each x compute target y_x = x^a+alpha x^b; bad iff some deg<k poly
                    # agrees with x->y_x on >= t of the n points.
                    ys = [(pow(x, a, q) + alpha * pow(x, b, q)) % q for x in D]
                    # check: does there exist deg<k poly hitting >= t of (D[i], ys[i])?
                    # k small; choose any k points to fix g (Lagrange), count agreements, max over choices.
                    # max agreement of a deg<k poly = max over k-subsets of interpolant agreement.
                    best = max_agreement(D, ys, k, q)
                    if best >= t:
                        bad.append(alpha)
                bad_set = set(bad)
                I = len(bad_set)
                # count orbits under alpha -> alpha * omega^{b-a}
                mult = pow(omega, (b - a) % n, q)
                N = count_orbits(bad_set, mult, q)
                ok_eq = (I == N * S)
                ok_cross = ((I <= n) == (N <= d))
                if I > 0:
                    print(f"  pencil(a={a},b={b}) d=gcd={d} S={S} t={t}: "
                          f"I={I} N={N} N*S={N*S} eq={ok_eq} | I<=n:{I<=n} N<=d:{N<=d} cross={ok_cross}")
                    break

def max_agreement(D, ys, k, q):
    """max number of points (D[i],ys[i]) lying on a single poly of degree < k."""
    import itertools
    n = len(D)
    if k >= n:
        # any n points lie on deg<n poly
        return n
    best = 0
    # for deg<k, a poly is fixed by any k points. Enumerate k-subsets, interpolate, count agreements.
    idxs = list(range(n))
    seen = set()
    for sub in itertools.combinations(idxs, k):
        xs = [D[i] for i in sub]
        if len(set(xs)) < k:
            continue
        vs = [ys[i] for i in sub]
        coeffs = lagrange_coeffs(xs, vs, q)
        cnt = 0
        for i in range(n):
            if poly_eval(coeffs, D[i], q) == ys[i]:
                cnt += 1
        if cnt > best:
            best = cnt
        if best == n:
            break
    return best

def lagrange_coeffs(xs, vs, q):
    """return coeff list of interpolating poly deg<len(xs) over F_q."""
    k = len(xs)
    # polynomial as coeff list
    poly = [0] * k
    for i in range(k):
        # basis L_i(x) = prod_{j!=i} (x-x_j)/(x_i-x_j)
        num = [1]  # poly = 1
        denom = 1
        for j in range(k):
            if j == i:
                continue
            # multiply num by (x - x_j)
            num = poly_mul(num, [(-xs[j]) % q, 1], q)
            denom = (denom * (xs[i] - xs[j])) % q
        inv = pow(denom, q - 2, q)
        scale = (vs[i] * inv) % q
        for t in range(len(num)):
            poly[t] = (poly[t] + num[t] * scale) % q
    return poly

def poly_mul(a, b, q):
    res = [0] * (len(a) + len(b) - 1)
    for i, ai in enumerate(a):
        for j, bj in enumerate(b):
            res[i + j] = (res[i + j] + ai * bj) % q
    return res

def poly_eval(coeffs, x, q):
    r = 0
    p = 1
    for c in coeffs:
        r = (r + c * p) % q
        p = (p * x) % q
    return r

def count_orbits(S_set, mult, q):
    """count orbits of S_set under alpha -> alpha*mult mod q (alpha=0 fixed)."""
    seen = set()
    orbits = 0
    for a in S_set:
        if a in seen:
            continue
        orbits += 1
        b = a
        while True:
            seen.add(b)
            b = (b * mult) % q
            if b == a:
                break
            if b not in S_set:
                # shouldn't happen if orbit-closed; guard
                break
    return orbits

if __name__ == "__main__":
    main()

# --- refinement: verify the FREE-ACTION hypothesis precisely ---
def verify_free_action():
    """
    Confirm: on the bad set B with alpha=0 removed (or when S=1), every orbit of
    alpha -> alpha*mult has size EXACTLY S = ord(mult). Then |B'| = N'*S exactly.
    The crossing law I<=n <=> N<=d is what we formalize; the EXACT factorization needs
    the free-action (constant-orbit-size) hypothesis, which holds off the fixed point.
    """
    from math import gcd
    cases = [(521,8,2),(17,8,2),(7,6,2),(13,12,3),(11,10,3)]
    all_ok = True
    for (q,n,k) in cases:
        omega = next(c for c in range(2,q) if pow(c,n,q)==1 and
                     all(not(n%d==0 and pow(c,d,q)==1) for d in range(1,n)))
        D=[pow(omega,i,q) for i in range(n)]
        for a in range(n):
            for b in range(a+1,n+1):
                d=gcd(b-a,n); S=n//d; mult=pow(omega,(b-a)%n,q)
                # ord of mult must equal S
                ordm=1; t=mult
                while t!=1: t=(t*mult)%q; ordm+=1
                assert ordm==S, f"ord mismatch {ordm} vs {S}"
                for thr in [n-1,n-2]:
                    bad=set()
                    for alpha in range(q):
                        ys=[(pow(x,a,q)+alpha*pow(x,b,q))%q for x in D]
                        if max_agreement(D,ys,k,q)>=thr: bad.add(alpha)
                    if not bad: continue
                    # every NONZERO-orbit must have size exactly S
                    seen=set(); good=True
                    for al in bad:
                        if al in seen: continue
                        orb=[]; bb=al
                        while True:
                            orb.append(bb); seen.add(bb); bb=(bb*mult)%q
                            if bb==al: break
                        if al!=0 and len(orb)!=S: good=False
                    # B minus fixed point partitions into size-S orbits
                    Bp = bad - {0}
                    Np = 0; sn=set()
                    for al in Bp:
                        if al in sn: continue
                        Np+=1; bb=al
                        while True:
                            sn.add(bb); bb=(bb*mult)%q
                            if bb==al: break
                    factor_ok = (len(Bp)==Np*S)
                    if not (good and factor_ok):
                        all_ok=False
                        print(f"  FAIL q={q} n={n} (a={a},b={b}) thr={thr}: free={good} factor={factor_ok}")
                    break
    print("FREE-ACTION / EXACT-FACTORIZATION off fixed point:", "ALL OK" if all_ok else "FAILURES")

verify_free_action()
