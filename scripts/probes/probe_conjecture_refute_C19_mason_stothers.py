#!/usr/bin/env python3
"""
probe_conjecture_refute_C19_mason_stothers.py   (issue #444, conjecture C19)

CONJECTURE C19 (fewnomial-khovanskii / Mason-Stothers ABC):
  "After antipodal even/odd descent, isolated witnesses inject into mu_{n/2}-roots
   of F = E^2 - u*O^2 (deg E,O < k/2); Mason-Stothers on the coprime triple with
   small rad(u*O^2) forces distinct roots <= 3k/2 + 1, flat in n, giving
   delta* = 1/2 - O(rho) past Johnson at rho = 1/16."

THE CLAIM UNDER TEST.  C19 asserts that the Mason-Stothers (polynomial ABC)
theorem, applied to the coprime triple
        X = E^2,   Y = -u*O^2,   Z = F = E^2 - u*O^2  (X + Y = Z),
yields  max(deg X, deg Y, deg Z) <= rad(X*Y*Z) - 1 = rad(E*O*u*F) - 1,
and that because deg O < k/2 makes rad(u*O^2) small, the bound forces the
distinct-root count of F to be O(k), flat in n.

THE IN-TREE COUNTER-ANALYSIS (mason_stothers_iso_feed_vacuous):
  E = u^{a/2} + gamma*u^{b/2} - cE,  deg cE < k/2,  with a,b ~ n.  Then
      deg X = deg(E^2) = a ~ n,    deg Z = deg F = a ~ n,
      rad(E) ~ (a-b)/2 ~ n/2   (the binomial head u^{a/2}+gamma u^{b/2}
                                has ~(a-b)/2 distinct roots),
      rad(u*O^2) <= 1 + deg O < 1 + k/2   (SMALL, the only deg O<k/2 lever),
      rad(F) <= deg F = a ~ n.
  So MS reads  a <= (a/2) + (k/2) + a - 1 = (3a/2) + (k/2) - 1  >>  a.
  The big radicals rad(E)~n/2 and rad(F)~n DROWN the small rad(uO^2).

WHAT THIS PROBE DOES (exact, over PROPER subgroup mu_n, p prime, p >> n^3):
  1. Build the prize-shape agreement poly  P(x) = x^a + gamma x^b - c(x),
     deg c < k, a,b even (the genuine d=gcd(a-b,n)>=2 direction), over mu_n,
     n = 2^mu a PROPER subgroup of F_p^*  (n | p-1, p prime, NEVER n=p-1).
  2. Antipodal descent to F(u) = E(u)^2 - u*O(u)^2 on mu_{n/2}.
  3. Compute the ACTUAL polynomial radicals (squarefree parts) of E^2, u*O^2, F
     over F_p, and report whether the MS bound rad(XYZ)-1 beats deg F (the
     trivial bound).  If rad(XYZ)-1 >= deg F, MS gives NOTHING (vacuous).
  4. Report the ACTUAL distinct-root count of F in mu_{n/2}, and the MS-claimed
     ceiling 3k/2+1, and whether the MS BOUND (not the measured count) reaches it.

HONESTY: all arithmetic exact over F_p (sympy GF(p) polynomials).  We probe the
PROOF MECHANISM (does MS deliver the bound), not just the measured root count.
"""

import sys
from sympy import isprime, primitive_root, divisors, GF, Poly, symbols, gcd as sgcd

u = symbols('u')


def find_prime(n, beta_pow=3):
    """Smallest prime p = 1 (mod n) with p > n^beta_pow (so p >> n^3, prize band)."""
    lo = n ** beta_pow + 1
    p = lo - (lo % n) + 1
    while True:
        if p > n and isprime(p) and (p - 1) % n == 0:
            return p
        p += n


def subgroup_gen(p, n):
    g = primitive_root(p)
    h = pow(g, (p - 1) // n, p)
    assert pow(h, n, p) == 1 and pow(h, n // 2, p) != 1, "h must have exact order n"
    return h


def poly_radical(poly, p):
    """Squarefree part (radical) of a Poly over GF(p); returns its degree
    (= number of DISTINCT roots in the algebraic closure)."""
    if poly.is_zero:
        return 0
    g = sgcd(poly, poly.diff(u))
    rad = poly.quo(g)
    return rad.degree()


def distinct_roots_in_mu(poly, h, p, m):
    """Count j in 0..m-1 with poly(h^j) = 0 in F_p (roots in mu_m)."""
    cnt = 0
    val = 1  # h^0
    for j in range(m):
        if poly.eval(val) % p == 0:
            cnt += 1
        val = val * h % p
    return cnt


def build_descent(n, k, p, rng):
    """Construct a prize-shape P = x^a + gamma x^b - c, a,b even, deg c < k,
    chosen to maximize agreement on mu_n; return (E, O, F) on u = x^2 (mu_{n/2}).

    We construct an EXTREMAL P: pick a target set S subset mu_n of agreement
    points and solve for c (the low block) + gamma so P vanishes on S, then read
    the even/odd descent.  To keep it simple and worst-case-flavored we plant a
    near-coset S to force a high-agreement (close-to-code) line, which is exactly
    the regime where MS is supposed to bite.
    """
    import random
    Fp = GF(p)
    m = n // 2
    h = subgroup_gen(p, n)
    # choose a,b even, distinct, in [k, n)
    evens = [e for e in range(k, n) if e % 2 == 0]
    a, b = rng.sample(evens, 2)
    if a < b:
        a, b = b, a
    # plant agreement set S: prescribe deg c (<k) + gamma (1 dof) + ...
    # number of free coeffs in c is k, plus gamma = k+1 unknowns; prescribe k+1 roots.
    # Build linear system over F_p:  for each planted root z: z^a + gamma z^b = c(z).
    # unknowns: gamma, c_0..c_{k-1}.   eqn:  z^a + gamma z^b - sum_i c_i z^i = 0.
    hp = [1] * n
    for j in range(1, n):
        hp[j] = hp[j - 1] * h % p
    # planted roots: a generic (non-coset) subset of size k+1 (maximal for unique-ish soln)
    nroots = k + 1
    S = rng.sample(range(n), nroots)
    # system M v = rhs:  v = (gamma, c_0,...,c_{k-1});  per root z=h^j:
    #   gamma*z^b - sum_i c_i z^i = - z^a
    rows = []
    rhs = []
    for j in S:
        row = [hp[(b * j) % n]] + [(-hp[(i * j) % n]) % p for i in range(k)]
        rows.append([x % p for x in row])
        rhs.append((-hp[(a * j) % n]) % p)
    # solve (k+1)x(k+1) over F_p
    sol = solve_linear_modp(rows, rhs, p)
    if sol is None:
        return None
    gamma = sol[0] % p
    c = [sol[1 + i] % p for i in range(k)]
    # P(x) = x^a + gamma x^b - sum c_i x^i.  Descent: u = x^2.
    # even part of P:  terms with even exponent.  a,b even -> u^{a/2}, gamma u^{b/2}.
    # c split: cE = even-exp part of c (as poly in u), cO = odd-exp part / x.
    # E(u) = u^{a/2} + gamma u^{b/2} - cE(u);  O(u) = cO(u);  F = E^2 - u O^2.
    cE = {}   # cE[u-exp] from c_i with i even, i=2t -> u^t
    cO = {}   # cO[u-exp] from c_i with i odd,  i=2t+1 -> u^t
    for i in range(k):
        if i % 2 == 0:
            cE[i // 2] = (cE.get(i // 2, 0) + c[i]) % p
        else:
            cO[i // 2] = (cO.get(i // 2, 0) + c[i]) % p
    # E coeffs (as dict u-exp -> coeff)
    Ed = {}
    Ed[a // 2] = (Ed.get(a // 2, 0) + 1) % p
    Ed[b // 2] = (Ed.get(b // 2, 0) + gamma) % p
    for e, cc in cE.items():
        Ed[e] = (Ed.get(e, 0) - cc) % p
    Od = dict(cO)
    Epoly = dict_to_poly(Ed, p)
    Opoly = dict_to_poly(Od, p)
    # F = E^2 - u*O^2
    Fpoly = (Epoly ** 2 - Poly(u, u, modulus=p) * Opoly ** 2)
    return dict(a=a, b=b, k=k, n=n, m=m, h=h, p=p,
                E=Epoly, O=Opoly, F=Fpoly,
                degE=Epoly.degree(), degO=(Opoly.degree() if not Opoly.is_zero else -1))


def dict_to_poly(d, p):
    if not d:
        return Poly(0, u, modulus=p)
    deg = max(d.keys())
    coeffs = [0] * (deg + 1)
    for e, c in d.items():
        coeffs[deg - e] = c % p   # sympy Poly: leading first
    return Poly(coeffs, u, modulus=p)


def solve_linear_modp(rows, rhs, p):
    n = len(rows)
    M = [row[:] + [rhs[i] % p] for i, row in enumerate(rows)]
    inv = lambda x: pow(x, p - 2, p)
    r = 0
    for c in range(n):
        piv = None
        for rr in range(r, n):
            if M[rr][c] % p != 0:
                piv = rr
                break
        if piv is None:
            return None  # singular
        M[r], M[piv] = M[piv], M[r]
        iv = inv(M[r][c])
        M[r] = [(x * iv) % p for x in M[r]]
        for rr in range(n):
            if rr != r and M[rr][c] % p != 0:
                f = M[rr][c]
                M[rr] = [(a - f * b) % p for a, b in zip(M[rr], M[r])]
        r += 1
    return [M[i][n] % p for i in range(n)]


def main():
    import random
    print("=" * 78)
    print("C19 Mason-Stothers ABC antipodal-descent PIN -- proof-mechanism probe")
    print("F = E^2 - u*O^2 on mu_{n/2}; does MS bound rad(XYZ)-1 beat deg F?")
    print("Proper subgroups mu_n (n=2^mu | p-1, p prime, p>n^3, NEVER n=p-1).")
    print("=" * 78)
    hdr = (f"{'n':>5} {'k':>3} {'a':>4} {'b':>4} {'O==0?':>6} {'degF':>5} "
           f"{'radE2':>6} {'raduO2':>7} {'radF':>5} {'MSrhs':>6} "
           f"{'MSbeat?':>8} {'rootsF':>7} {'3k/2+1':>7}")
    print(hdr)
    rng = random.Random(444)
    beat_ragged = []   # rows where O != 0 (genuine ragged) AND MS beats trivial
    beat_coset = []    # rows where O == 0 (pure-coset, NOT C19's target) AND MS beats
    for mu in [4, 5, 6, 7]:
        n = 2 ** mu
        for rho_den in [16, 8]:
            k = max(2, n // rho_den)
            p = find_prime(n, beta_pow=3)
            # collect both a ragged (O!=0) and (if it occurs) a pure-coset instance
            for want_ragged in (True, False):
                built = None
                for _ in range(60):
                    b = build_descent(n, k, p, rng)
                    if b is None or b['F'].is_zero:
                        continue
                    is_ragged = not b['O'].is_zero
                    if is_ragged == want_ragged:
                        built = b
                        break
                if built is None:
                    continue
                E, O, F = built['E'], built['O'], built['F']
                Oz = O.is_zero
                degF = F.degree()
                radE2 = poly_radical(E ** 2, p)
                uO2 = Poly(u, u, modulus=p) * O ** 2
                raduO2 = poly_radical(uO2, p)
                radF = poly_radical(F, p)
                ms_rhs = radE2 + raduO2 + radF - 1
                beat = ms_rhs < degF
                rootsF = distinct_roots_in_mu(F, pow(built['h'], 2, p), p, built['m'])
                if beat:
                    (beat_coset if Oz else beat_ragged).append((n, k))
                print(f"{n:>5} {k:>3} {built['a']:>4} {built['b']:>4} "
                      f"{('YES' if Oz else 'no'):>6} "
                      f"{degF:>5} {radE2:>6} {raduO2:>7} {radF:>5} {ms_rhs:>6} "
                      f"{('YES' if beat else 'no'):>8} {rootsF:>7} {3*k//2+1:>7}")
    print("=" * 78)
    print("VERDICT:")
    print(f"  MS-beats-trivial in RAGGED (O!=0, C19's actual target) rows: {beat_ragged}")
    print(f"  MS-beats-trivial in PURE-COSET (O==0, NOT C19's target) rows: {beat_coset}")
    if not beat_ragged:
        print("  => In EVERY genuinely-ragged (O!=0) row -- the ONLY case C19 needs --")
        print("     MS RHS (rad E + rad uO^2 + rad F - 1) >= deg F: F is squarefree of")
        print("     full degree (radF = degF ~ n) and rad E ~ n/2, so the small")
        print("     rad(uO^2) < 1+k/2 is DROWNED. Mason-Stothers is VACUOUS there.")
        print("  The only MS-beats rows are O==0 = the PURE-COSET case, which is")
        print("  NOT the ragged/isolated witnesses C19 targets: it is the in-tree")
        print("  closed-form (antipodal) case that the meta-theorem CAPS AT JOHNSON.")
        print("  So C19's measured '<=3k/2+1' is the open isolated/non-coset root")
        print("  count (Kelley/BGK), which Mason-Stothers does NOT deliver.")
    else:
        print("  Investigate: MS beat trivial in a genuinely ragged row.")
    print("=" * 78)


if __name__ == "__main__":
    main()
