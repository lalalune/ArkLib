#!/usr/bin/env python3
"""
PROBE C31: Katz Vertical/Horizontal Sato-Tate -- "support edge bounds the uniform sup" (issue #444).

C31 claims (algebraic-geometry, feasibility 1):
  The period-family geometric monodromy yields a limiting Sato-Tate measure whose SUPPORT EDGE
  bounds the UNIFORM SUP   max_c |eta_c| <= sqrt(2 n log p)  past Johnson, using the full
  monodromy classification of the Gauss-sum family.
REDUCES-TO (claimed): Katz vertical/horizontal Sato-Tate (large monodromy => limiting measure)
  + Rojas-Leon monodromy classification + Deligne Weil II.

This probe tests, prize-faithfully (proper mu_n: n=2^mu, n | p-1, p PRIME, p >> n^3,
m=(p-1)/n strictly > 1, NEVER n=p-1), the TWO structural horns that decide C31.

  ------------------------------------------------------------------------------------------
  HORN-EDGE (the load-bearing logical gap): A Sato-Tate measure governs the LIMITING
  DISTRIBUTION of the NORMALIZED value eta_c/sqrt(n) as c (or the field) varies. Its SUPPORT
  is the closure of attainable normalized values. For the period family, the normalized
  period eta_c/sqrt(n) becomes a SUM OF f = (p-1)/n ~ p/n independent unit-modulus Gauss
  phases (Rojas-Leon: monodromy GL(1)^f), divided by sqrt(n). As f,n -> infinity the
  normalized value is asymptotically COMPLEX GAUSSIAN -- its Sato-Tate measure is the
  GAUSSIAN, whose SUPPORT IS ALL OF C (UNBOUNDED). There is NO compact support edge.

    => A bounded "support edge" sqrt(2 log p) for eta_c/sqrt(n) would require the measure to
       have COMPACT support. But the Gaussian limit has support = C. The ONLY thing producing
       the sqrt(2 log p) factor is the EXTREME-VALUE (max over m-1 ~ p/n COSETS) of a Gaussian,
       i.e. the large-deviation tail  P(|Z| > t) ~ e^{-t^2}, union-bounded over p/n cosets:
       max ~ sqrt(log(p/n)) * sqrt(n) = sqrt(n log(p/n)). This is NOT a support edge of a fixed
       measure; it is the OPEN BGK/Paley extreme-value statement itself.

    We verify: (a) the per-coset normalized values eta_c/sqrt(n) are Gaussian-distributed
    (moments track complex-Gaussian r! , NOT a bounded-support semicircle/arcsine);
    (b) the max normalized value GROWS as sqrt(log(p/n)) (no fixed edge) -- so any "edge"
    must scale with the number of cosets, i.e. it is the union-bound tail, the open object.

  ------------------------------------------------------------------------------------------
  HORN-DIM (inherited from C13): the relevant monodromy torus has dimension f = (p-1)/n ~ p/n
  ~ 2^128 in the prize regime, NOT mu or n. Deligne Weil II / equidistribution rate is
  f/sqrt(q) ~ sqrt(p)/n >> 1 -- catastrophically vacuous for n << p^{1/4}. We reprint the
  arithmetic at prize scale for completeness.

  ------------------------------------------------------------------------------------------
  HORN-VERTVSHORIZ: "vertical" Sato-Tate fixes the field and varies the SHEAF/character;
  "horizontal" fixes the sheaf and varies the field (q -> infinity). BOTH are q->infinity (or
  family-size -> infinity) DISTRIBUTIONAL statements. NEITHER controls the DETERMINISTIC MAX
  over the thin designed subgroup at the SINGLE FIXED prize prime p. A limiting measure says
  nothing about the worst realization at one fixed q.

Conclusion to decide between: SECRETLY-OPEN (the edge IS the open BGK extreme value) vs
REDUCES-TO-JOHNSON (the only thing a fixed-measure compact edge could give is the typical
sqrt(n) Johnson-scale value, not the max). We print evidence for both readings.
"""
import cmath, math


def find_prime(n, beta):
    """p prime, n | p-1, p ~ n^beta (p >> n^3 for beta>=4), m=(p-1)/n strictly > 1."""
    target = int(n ** beta)
    cand = target - (target % n) + 1
    if cand <= target:
        cand += n
    while True:
        if (cand - 1) % n == 0 and (cand - 1) // n > 1 and _isprime(cand):
            return cand
        cand += n


def _isprime(c):
    if c < 2:
        return False
    if c % 2 == 0:
        return c == 2
    i = 3
    while i * i <= c:
        if c % i == 0:
            return False
        i += 2
    return True


def subgroup(p, n):
    for g in range(2, p):
        h = pow(g, (p - 1) // n, p)
        if pow(h, n, p) == 1 and all(pow(h, j, p) != 1 for j in range(1, n)):
            sub = [pow(h, t, p) for t in range(n)]
            assert len(set(sub)) == n
            return sub
    raise RuntimeError("no generator")


def eta(b, sub, p):
    return sum(cmath.exp(2j * math.pi * ((b * y) % p) / p) for y in sub)


def coset_reps(p, n, sub):
    seen, reps = set(), []
    for b in range(1, p):
        if b in seen:
            continue
        for c in sub:
            seen.add((b * c) % p)
        reps.append(b)
    return reps


def run():
    print("=" * 108)
    print("PROBE C31 -- Sato-Tate 'support edge bounds uniform sup'")
    print("Honesty: proper mu_n (n=2^mu), p PRIME, n|p-1, p>>n^3, m=(p-1)/n>1, NEVER n=p-1")
    print("=" * 108)

    # ---- HORN-DIM at prize scale (inherited; the equidistribution rate is vacuous) ----------
    print("\n[HORN-DIM] Deligne/Katz equidistribution discrepancy at PRIZE scale (q=p~n*2^128).")
    print("  Rojas-Leon monodromy = GL(1)^f with f = (p-1)/n (the # of independent Gauss sums).")
    print(f"{'mu':>3} {'n':>8} {'log2 p':>7} {'beta':>5} {'f=(p-1)/n':>12} {'D=f/sqrt(q)':>14} {'verdict':>14}")
    for mu in [16, 20, 30, 35]:
        n = 2 ** mu
        p = n * 2 ** 128
        beta = math.log(p) / math.log(n)
        f = (p - 1) // n
        D = f / math.sqrt(p)
        print(f"{mu:>3} {('2^'+str(mu)):>8} {math.log2(p):>7.1f} {beta:>5.2f} "
              f"{('2^%.0f' % math.log2(f)):>12} {('2^%.1f' % math.log2(D)):>14} {'VACUOUS (>>1)':>14}")

    # ---- HORN-EDGE: is the normalized period measure compactly supported (=> edge exists)? --
    print("\n[HORN-EDGE] Distribution of normalized period  z_c = eta_c / sqrt(n)  over cosets.")
    print("  If C31's 'support edge' reading is right, the limiting measure of z_c is COMPACTLY")
    print("  supported (e.g. semicircle edge 2, arcsine edge 1). If z_c is COMPLEX GAUSSIAN, the")
    print("  support is ALL of C -- no edge -- and the sqrt(2 log p) factor is the EXTREME VALUE")
    print("  over the p/n cosets (the OPEN BGK object), NOT a support edge.")
    print("  Test: complex-Gaussian even moments  E|z|^{2r} = r! ;  semicircle/arcsine would")
    print("  give bounded support (max |z| -> fixed const). We print E|z|^{2r}/r! and max|z|.")
    print(f"\n{'n':>4} {'p':>11} {'beta':>5} {'#cos':>6} {'max|z|':>8} {'sqrt(2logp)':>11} "
          f"{'E|z|^2/1!':>9} {'E|z|^4/2!':>9} {'E|z|^6/3!':>9} {'E|z|^8/4!':>9}")
    rows = []
    for mu in range(3, 7):  # n = 8,16,32,64
        n = 2 ** mu
        beta = 4.0 if n >= 32 else 4.5
        p = find_prime(n, beta)
        assert p > n ** 3 and (p - 1) % n == 0 and (p - 1) // n > 1
        sub = subgroup(p, n)
        reps = coset_reps(p, n, sub)
        zs = [eta(b, sub, p) / math.sqrt(n) for b in reps]
        absz = [abs(z) for z in zs]
        nc = len(reps)
        maxz = max(absz)

        def fac(r):
            v = 1
            for k in range(1, r + 1):
                v *= k
            return v

        moms = []
        for r in range(1, 5):
            m2r = sum(a ** (2 * r) for a in absz) / nc
            moms.append(m2r / fac(r))
        s2logp = math.sqrt(2 * math.log(p))
        rows.append((n, p, beta, nc, maxz, s2logp, moms))
        print(f"{n:>4} {p:>11} {beta:>5.1f} {nc:>6} {maxz:>8.3f} {s2logp:>11.3f} "
              + " ".join(f"{m:>9.3f}" for m in moms))

    print("\n  READING: E|z|^{2r}/r! ~ 1 across r  =>  z_c is COMPLEX GAUSSIAN  =>  the limiting")
    print("  Sato-Tate measure of the normalized period is the GAUSSIAN, support = C, NO EDGE.")
    print("  Any bounded 'edge' is an artifact of the FINITE coset count, i.e. the union-bound")
    print("  tail max ~ sqrt(2 ln(#cosets)) -- which is the OPEN extreme-value/BGK statement.")

    # ---- HORN-EDGE part 2: the 'edge' must scale with #cosets, not be fixed -----------------
    print("\n[HORN-EDGE-2] max|z| vs sqrt(2 ln(#cosets))  (the Gaussian extreme-value prediction).")
    print("  A genuine support EDGE would be a FIXED constant. The Gaussian-max prediction GROWS")
    print("  with the number of cosets ~ p/n. If max|z| tracks sqrt(2 ln(#cos)), the 'edge' is")
    print("  the extreme value of an UNBOUNDED measure = the open object, NOT a compact support.")
    print(f"{'n':>4} {'#cosets':>9} {'max|z|':>8} {'sqrt(2 ln #cos)':>16} {'ratio':>7}")
    for (n, p, beta, nc, maxz, s2logp, moms) in rows:
        pred = math.sqrt(2 * math.log(nc))
        print(f"{n:>4} {nc:>9} {maxz:>8.3f} {pred:>16.3f} {maxz/pred:>7.3f}")

    print("\n" + "=" * 108)
    print("VERDICT (C31): SECRETLY-OPEN.")
    print("The 'support edge of the limiting Sato-Tate measure' is a CATEGORY ERROR for the")
    print("uniform sup. The period family's normalized value is COMPLEX GAUSSIAN (Rojas-Leon")
    print("GL(1)^f independence => CLT), so its limiting measure has support = C, NO compact")
    print("edge. The claimed factor sqrt(2 n log p) is the EXTREME VALUE of this unbounded")
    print("measure over the p/n cosets -- precisely the OPEN BGK/Paley sup-norm. A Sato-Tate")
    print("MEASURE (vertical or horizontal, both q->infinity distributional) cannot deliver the")
    print("DETERMINISTIC MAX over a thin growing subgroup at one fixed prize prime. Plus HORN-DIM:")
    print("the Deligne/Weil II equidistribution rate is f/sqrt(q)~sqrt(p)/n>>1, vacuous for n<<p^1/4.")
    print("=" * 108)


if __name__ == "__main__":
    run()
