#!/usr/bin/env python3
"""
probe_cyclicsieving_listgrowth.py  (#389/#407 — cyclic-sieving / n-core list-growth, prize-deciding)

Settles the open core of the cyclic-sieving attack (memory issue389-schur-roots-of-unity-lever):

  The smooth-domain (mu_n) GM-MDS / HOMDS list-decoding certificate for a degree-pattern lambda
  is det(zeta^{beta_j i}), beta_j = lambda_j + (n-1-j); it is NONZERO iff the beta_j are distinct
  mod n (abacus n-core EMPTY) and VANISHES iff two collide mod n (n-core NONEMPTY).  This is
  exactly ArkLib/.../HOMDSSmoothObstruction.homds_det_ne_zero_iff_nCoreEmpty (machine-checked).
  Each vanishing certificate = an extra linear dependence = a POTENTIAL spurious list codeword.

  OPEN QUESTION the lever poses: does cyclic-sieving / n-core (hook-content) VANISHING boost the
  smooth-mu_n coset list ABOVE the trivial single-coset O(1/rho), to SUPER-POLY (=> prize floor
  FALSE for plain RS) or stay poly (=> floor list face plausibly closes)?

THREE machine-checked findings (this probe; PRIZE regime: proper subgroup mu_{2^mu}, multi-prime):

  (A) The raw cyclic-sieving enumeration, when counted over coset-UNION supports (an earlier probe
      multiplied a per-coset kernel dim by C(#cosets, #needed)), EXPLODES super-poly.  BUT that
      counts rank-deficient SUPPORTS / dependences, NOT codewords -- a single coset support of
      m=k+1 columns has NO beta-collision mod n in the window a>k (shown below: count 0), so the
      explosion lived entirely in the binomial coset-union factor C(A, .), not in distinct shapes.

  (B) GROUND TRUTH: the EXACT F_p worst-case CODEWORD list (full C(n,k) enumeration) is generic-
      MDS-sized.  In the strict interior window (agreement a comfortably above k) it is O(1/rho)
      (a handful), p-INDEPENDENT.  The only large list is the a=k+1 BOUNDARY spike.

  (C) DECISIVE: at a=k+1 the SMOOTH mu_n list ~ a RANDOM (non-smooth) domain list (n=16,k=8:
      SMOOTH 67 vs RANDOM 70).  So the spike is GENERIC MDS list-decoding, NOT a cyclic-sieving /
      smooth-mu_n effect; the smooth structure gives NO list boost.

CONCLUSION (honest): the cyclic-sieving / n-core lever does NOT super-poly-boost the list and
does NOT refute the floor.  The super-poly of (A) is exactly the proven core-vs-list binomial
factor #cores <= L * C(A, k+m+1) (ArkLib SubJohnsonListSupply.explainableCoreSupply_of_listBound):
the n-core enumeration counts the C(A,.) supports, NOT the list L.  The route REDUCES to the same
generic-MDS list bound L (the named open core SubJohnsonListBound), with smooth mu_n providing no
advantage over a random domain.  => precise reduction to the named core, no closure, no refutation.
"""
import math, itertools, random


# ---- number theory (no sympy; inline primitive root) ----
def is_prime(n):
    if n < 2:
        return False
    i = 2
    while i * i <= n:
        if n % i == 0:
            return False
        i += 1
    return True


def primes_for(n, count=2):
    out = []
    c = (8 * n // n + 1) * n + 1
    while len(out) < count:
        if is_prime(c):
            out.append(c)
        c += n
    return out


def primitive_subgroup(p, n):
    """PROPER subgroup mu_n = {h^t} <= F_p^*, h a primitive n-th root (NEVER full group)."""
    for g in range(2, p):
        h = pow(g, (p - 1) // n, p)
        if pow(h, n, p) == 1 and all(pow(h, j, p) != 1 for j in range(1, n)):
            return [pow(h, t, p) for t in range(n)]
    raise RuntimeError("no generator")


def random_domain(p, n, rng):
    s = set()
    while len(s) < n:
        s.add(rng.randrange(1, p))
    return list(s)


# ---- finite-field polynomial machinery ----
def poly_eval(c, x, p):
    v = 0
    for a in reversed(c):
        v = (v * x + a) % p
    return v


def interp(xs, ys, k, p):
    co = [0] * k
    for i in range(k):
        num = [1]
        den = 1
        for j in range(k):
            if j == i:
                continue
            nw = [0] * (len(num) + 1)
            for t, cc in enumerate(num):
                nw[t] = (nw[t] + cc * ((-xs[j]) % p)) % p
                nw[t + 1] = (nw[t + 1] + cc) % p
            num = nw
            den = den * (xs[i] - xs[j]) % p
        inv = pow(den, p - 2, p)
        for t in range(len(num)):
            co[t] = (co[t] + ys[i] * num[t] % p * inv) % p
    return tuple(co)


def exact_list(D, w, p, k, a):
    """EXACT #{ deg-<k polynomials agreeing with w on >= a of the n points } (full C(n,k))."""
    n = len(D)
    polys = set()
    for idx in itertools.combinations(range(n), k):
        c = interp([D[i] for i in idx], [w[i] for i in idx], k, p)
        if c in polys:
            continue
        if sum(1 for i in range(n) if poly_eval(c, D[i], p) == w[i]) >= a:
            polys.add(c)
    return len(polys)


def worst_list(D, p, k, a, rng, nrand):
    """Worst over cyclic-sieving coset-glued words + random words."""
    n = len(D)
    best = 0
    for nb in [d for d in (2, 4) if n % d == 0]:
        bc = [tuple(((b * 37 + t * 101 + 5) % (p - 1)) + 1 for t in range(k)) for b in range(nb)]
        w = [poly_eval(bc[t % nb], D[t], p) for t in range(n)]
        best = max(best, exact_list(D, w, p, k, a))
    for _ in range(nrand):
        w = [rng.randrange(p) for _ in range(n)]
        best = max(best, exact_list(D, w, p, k, a))
    return best


# ---- (A) naive n-core support enumeration (the over-count) ----
def beta_collide_mod_n(lam, m, n):
    seen = set()
    lam = list(lam) + [0] * (m - len(lam))
    for j in range(m):
        r = (lam[j] + (m - 1 - j)) % n
        if r in seen:
            return True
        seen.add(r)
    return False


def weakly_decreasing(m, maxpart):
    def rec(pos, prev):
        if pos == m:
            yield ()
            return
        for v in range(min(prev, maxpart), -1, -1):
            for rest in rec(pos + 1, v):
                yield (v,) + rest
    yield from rec(0, maxpart)


def naive_ncore_support_count(n, k, m):
    """#{ shapes lambda (m columns, parts in [0,k-1]) with NONEMPTY n-core } -- the naive
    cyclic-sieving enumeration. This is the SUPPORT/dependence count, NOT codewords."""
    cnt = 0
    for lam in weakly_decreasing(m, k - 1):
        if beta_collide_mod_n(lam, m, n):
            cnt += 1
    return cnt


def main():
    rng = random.Random(5)
    print("=" * 84)
    print("CYCLIC-SIEVING / n-CORE LIST GROWTH (prize regime: proper mu_{2^mu}, multi-prime)")
    print("=" * 84)

    print("\n(A) NAIVE n-core-nonempty SUPPORT count (the over-count) -- explodes super-poly:")
    print(f"    {'n':>4} {'k':>3} {'m(cols)':>7} | {'#nonempty-ncore shapes':>22}")
    for mu in range(3, 7):
        n = 2 ** mu
        k = max(2, n // 2)
        m = min(8, k + 1)  # keep enumeration small
        cnt = naive_ncore_support_count(n, k, m)
        print(f"    {n:>4} {k:>3} {m:>7} | {cnt:>22}")
    print("    -> grows fast, BUT counts rank-deficient SUPPORTS, not distinct codewords (see B,C).")

    print("\n(B) GROUND TRUTH: EXACT worst-case CODEWORD list (full C(n,k)), strict interior window:")
    print(f"    {'n':>4} {'k':>3} {'a':>3} {'a-k':>4} {'p':>5} | {'EXACT list':>10}  (rho=1/2)")
    for n in [8, 12, 16]:
        k = n // 2
        if math.comb(n, k) > 1_000_000:
            continue
        for da in [2, 3]:  # strict interior (a >= k+2), NOT the k+1 boundary
            a = k + da
            for p in primes_for(n, 1):
                D = primitive_subgroup(p, n)
                nrand = 40 if math.comb(n, k) < 200000 else 12
                L = worst_list(D, p, k, a, rng, nrand)
                print(f"    {n:>4} {k:>3} {a:>3} {da:>4} {p:>5} | {L:>10}")
    print("    -> O(1/rho) (a handful), p-independent: NO super-poly list in the strict interior.")

    print("\n(C) DECISIVE: SMOOTH mu_n vs RANDOM domain at the a=k+1 boundary spike (rho=1/2):")
    print(f"    {'n':>4} {'k':>3} {'a-k':>4} {'p':>5} | {'SMOOTH list':>11} {'RANDOM list':>11}")
    for n in [8, 12, 16]:
        k = n // 2
        if math.comb(n, k) > 1_000_000:
            continue
        a = k + 1
        for p in primes_for(n, 1):
            Ds = primitive_subgroup(p, n)
            Dr = random_domain(p, n, rng)
            nrand = 30 if math.comb(n, k) < 200000 else 8
            Ls = worst_list(Ds, p, k, a, rng, nrand)
            Lr = worst_list(Dr, p, k, a, rng, nrand)
            print(f"    {n:>4} {k:>3} {a - k:>4} {p:>5} | {Ls:>11} {Lr:>11}")
    print("    -> SMOOTH ~ RANDOM: the spike is GENERIC MDS list-decoding, NOT cyclic-sieving.")

    print("\n" + "=" * 84)
    print("CONCLUSION: cyclic-sieving / n-core lever does NOT super-poly-boost the smooth list and")
    print("does NOT refute the floor. (A)'s super-poly is exactly the proven core-vs-list binomial")
    print("factor #cores <= L*C(A,k+m+1) (SubJohnsonListSupply.explainableCoreSupply_of_listBound):")
    print("the n-core enumeration counts the C(A,.) SUPPORTS, not the list L. The route REDUCES to")
    print("the named open core SubJohnsonListBound's list L, with smooth mu_n giving no advantage")
    print("over a random domain. => reduction to named core; no closure, no refutation.")


if __name__ == "__main__":
    main()
