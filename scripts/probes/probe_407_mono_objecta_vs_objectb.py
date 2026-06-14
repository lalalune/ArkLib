#!/usr/bin/env python3
# ============================================================================
# Issue #407 — DECISIVE comparison: object (a) divided-difference bad-scalar
# count N  vs  object (b) line-incidence I, for the ring-hom monotonicity claim.
#
# Verdict produced by this probe (μ_n proper subgroup, p≡1 mod n, n=8,16):
#   * Object (a) N: monotonicity N(char-p) <= N(char-0) HOLDS at every tested
#     thin prime and direction — BUT it is near-trivial: N(char-p) <= p, so when
#     p is small the count cannot exceed the (large) char-0 count, and when p is
#     faithful (p >> n^4) N(char-p)=N(char-0). The claim is true for (a).
#   * Object (b) I (the deployed δ* quantity, governing law I(δ)=max#{α:line
#     δ-close}): char-p EXCEEDS char-0 at thin primes in the deeper window bands.
#     e.g. n=16, dir(6,7): band w=6 has I=0 in char-0 but I=10 at p=113, I=4 at
#     p=257, I=6 at p=17. char-p > char-0 — the OPPOSITE of the monotonicity.
#   * MECHANISM: the same event — a denominator DD_T(x^b)=h_{b-k}(ζ^T) that is
#     nonzero over ℂ but ≡0 mod q ("excess prime") — DELETES the finite scalar
#     γ_T from object (a) (so N can only drop), while by the Schur dichotomy it
#     SATURATES the monomial line (bad for every α) and pushes object (b)'s
#     incidence UP. (a) and (b) move in OPPOSITE directions on the same event.
#
# CONCLUSION: the ring-hom monotonicity is TRUE but about the WRONG object
# (finite-scalar count N), and does NOT transfer to the line-incidence object I
# that the governing δ* law actually uses. Confirms the sibling line-incidence
# finding (char-p > char-0 at thin primes). NOT a refutation of (a); it is a
# refutation of the *relevance* of (a)'s monotonicity to δ*.
#
# char-0 is taken as the faithful-prime limit (p >> n^4, no excess subsets),
# validated by stability across several such primes.
# ============================================================================
import itertools, math, sympy

def proot(q, n): return pow(sympy.primitive_root(q), (q-1)//n, q)

def DDmod(T, pts, fv, q):
    s = 0; m = len(T)
    for t in range(m):
        d = 1
        for u in range(m):
            if u != t: d = (d * ((pts[T[t]]-pts[T[u]]) % q)) % q
        s = (s + fv[T[t]] * pow(d, q-2, q)) % q
    return s

def object_a_N(q, n, k, a, b):
    """distinct finite γ_T = -DD_T(x^a)/DD_T(x^b), eligible T (DD_T(x^b)!=0)."""
    z = proot(q, n); pts = [pow(z, i, q) for i in range(n)]
    pa = [pow(x, a, q) for x in pts]; pb = [pow(x, b, q) for x in pts]
    G = set(); el = 0
    for T in itertools.combinations(range(n), k+1):
        db = DDmod(T, pts, pb, q)
        if db % q == 0: continue
        el += 1; da = DDmod(T, pts, pa, q)
        G.add(((-da) * pow(db, q-2, q)) % q)
    return len(G), el

def solve(M, rhs, q):
    m = len(M); A = [list(M[i])+[rhs[i]] for i in range(m)]; r = 0
    for c in range(m):
        piv = None
        for i in range(r, m):
            if A[i][c] % q: piv = i; break
        if piv is None: return None
        A[r], A[piv] = A[piv], A[r]; inv = pow(A[r][c], q-2, q)
        A[r] = [(v*inv) % q for v in A[r]]
        for i in range(m):
            if i != r and A[i][c] % q:
                f = A[i][c]; A[i] = [(A[i][j]-f*A[r][j]) % q for j in range(m+1)]
        r += 1
    return [A[i][m] % q for i in range(m)]

def object_b_I(q, n, k, a, b):
    """distinct γ vs line-incidence agreement bands, via (k+1)-subset solves."""
    z = proot(q, n); pts = [pow(z, i, q) for i in range(n)]
    pa = [pow(x, a, q) for x in pts]; pb = [pow(x, b, q) for x in pts]
    ga = {}
    for T in itertools.combinations(range(n), k+1):
        M = []; rhs = []
        for i in T:
            M.append([pow(pts[i], j, q) for j in range(k)] + [(-pa[i]) % q]); rhs.append(pb[i] % q)
        s = solve(M, rhs, q)
        if s is None: continue
        g = s[:k]; gam = s[k]
        if gam in ga: continue
        cnt = 0
        for i in range(n):
            gi = 0; xi = pts[i]
            for j in range(k-1, -1, -1): gi = (gi*xi + g[j]) % q
            if gi == (pb[i] + gam*pa[i]) % q: cnt += 1
        ga[gam] = cnt
    return {w: sum(1 for v in ga.values() if v >= w) for w in range(k+1, n+1)}

def run(n, k, dirs):
    primes = [p for p in range(n+1, 700000) if (p-1) % n == 0 and sympy.isprime(p)]
    thin = [p for p in primes if p < n**3]
    faith = [p for p in primes if p > n**4][:2]
    for (a, b) in dirs:
        print(f"\n### n={n} k={k} dir=({a},{b}) gcd(a-b,n)={math.gcd(a-b,n)}")
        # char-0 (faithful) reference for both objects
        N0, _ = object_a_N(faith[0], n, k, a, b)
        I0 = object_b_I(faith[0], n, k, a, b)
        print(f"  char-0 (q={faith[0]}>n^4): (a) N={N0}   (b) I-bands={ {w:v for w,v in I0.items() if v} }")
        print(f"  --- object (a) N  (claim: N(char-p) <= N(char-0)) ---")
        a_viol = []
        for p in thin[:6]:
            Np, _ = object_a_N(p, n, k, a, b)
            fl = "  <<< EXCEEDS (refute)" if Np > N0 else ""
            if Np > N0: a_viol.append((p, Np))
            print(f"    p={p:>6} (p/n3={p/n**3:5.2f}): N={Np:>5}  (<=p={p}){fl}")
        print(f"    (a) verdict: {'MONOTONE (holds)' if not a_viol else 'VIOLATED '+str(a_viol)}")
        print(f"  --- object (b) I  (deployed δ* quantity) ---")
        b_exc = []
        for p in thin[:6]:
            Ip = object_b_I(p, n, k, a, b)
            exc = {w: Ip[w] for w in Ip if Ip[w] > I0[w]}
            if exc: b_exc.append((p, exc))
            print(f"    p={p:>6} (p/n3={p/n**3:5.2f}): bands={ {w:v for w,v in Ip.items() if v} }"
                  + (f"   EXCEEDS char-0 at {exc}" if exc else ""))
        print(f"    (b) verdict: {'char-p > char-0 OCCURS at '+str(b_exc) if b_exc else 'no excess in tested bands'}")

if __name__ == "__main__":
    print("="*78)
    print("Object (a) divided-diff count N vs Object (b) line-incidence I — #407 monotonicity")
    print("char-0 = faithful-prime limit (q >> n^4)")
    print("="*78)
    run(8, 2, [(2, 3), (2, 4)])
    run(16, 4, [(6, 7), (5, 7), (4, 5)])
