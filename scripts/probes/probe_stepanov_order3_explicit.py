#!/usr/bin/env python3
"""
PROBE: does an explicit closed-form order-3 Stepanov auxiliary exist for the thin
2-power subgroup mu_n, exploiting the A = mu_n ∩ (mu_n + c) degeneracy
(x^n = 1 AND (c - x)^n = 1 on A), with degree < 1.5n so that r(c)*3 <= deg
BEATS the order-2 bound r(c) <= (n+1)/2 ?

Order-2 explicit auxiliary (in-tree, RepCountStepanovOrderTwo):
  Q2(X) = (c - X)^{n+1} + X^{n+1} - c,  deg = n+1, vanishes to order >= 2 on A,
  giving 2 r(c) <= n+1.

We search the SAME family / its natural order-3 generalizations and CHECK numerically
(exact mod p, proper thin mu_n, p >> n^3, n = 2^a, n | p-1, NEVER n = q-1) the actual
root multiplicity on A, then report deg and the implied r(c) bound.

Strictly probe-first: NO formalization unless a real degree<1.5n order-3 auxiliary
is found that is GENERIC in c (works for all off-diagonal c, all primes).
"""
import sympy as sp

def prime_factors(n):
    f=set(); d=2
    while d*d<=n:
        while n%d==0: f.add(d); n//=d
        d+=1
    if n>1: f.add(n)
    return f

def find_gen(p, n):
    pf = prime_factors(n)
    for cand in range(2, p):
        if pow(cand, n, p) == 1 and all(pow(cand, n//q, p)!=1 for q in pf):
            return cand
    raise RuntimeError((p,n))

def mu_n(p, n):
    g = find_gen(p, n)
    return [pow(g, i, p) for i in range(n)]

def find_prime(n, beta):
    # p = k*n + 1 prime, p ~ n^beta, p >> n^3
    import sympy
    target = n**beta
    k = max(1, target // n)
    while True:
        p = k*n + 1
        if p > 2*n**3 and sympy.isprime(p):
            return p
        k += 1

def root_mult_on_A(coeffs_modp, A, p):
    """coeffs_modp: list of (exponent, coeff) ; A: set of roots in F_p.
    Returns min over a in A of the vanishing order of the poly at a (capped at 6)."""
    x = sp.symbols('x')
    # build as sympy poly over integers, evaluate Hasse/derivatives mod p
    # represent poly by dict exp->coeff
    from collections import defaultdict
    poly = defaultdict(int)
    for e,c in coeffs_modp:
        poly[e] = (poly[e] + c) % p
    # poly as list
    if not poly: return 99
    maxd = max(poly)
    # derivative chain via finite-diff Hasse: order of vanishing at a =
    #   smallest k with k-th Hasse derivative != 0 at a.
    # Hasse_k(X^e) = C(e,k) X^{e-k}. Evaluate at a.
    def hasse_eval(k, a):
        s = 0
        for e,c in poly.items():
            if e>=k:
                s = (s + c * sp.binomial(e,k) * pow(a, e-k, p)) % p
        return s % p
    worst = 99
    nonzero_poly = any(v%p!=0 for v in poly.values())
    if not nonzero_poly:
        return -1  # ZERO polynomial — useless
    for a in A:
        k=0
        while k<=8:
            if hasse_eval(k, a) != 0:
                break
            k+=1
        worst = min(worst, k)
    return worst

def candidate_auxiliaries(c, n, p):
    """Return list of (name, deg, coeff_dict_list) candidate order-3 auxiliaries.
    On A: x^n=1, (c-x)^n=1. We want poly vanishing to order>=3.
    Family ideas (all reduce using the two relations):
    """
    cands = []
    # baseline order-2: Q2 = (c-X)^{n+1} + X^{n+1} - c
    def expand_binom_powerC_minusX(power):
        # (c - X)^power as dict exp->coeff mod p
        from collections import defaultdict
        d=defaultdict(int)
        for k in range(power+1):
            coeff = (sp.binomial(power,k) * pow(c, power-k, p) * ((-1)**k)) % p
            d[k] = (d[k]+coeff)%p
        return d
    def add(d, e, co):
        from collections import defaultdict
        d[e] = (d.get(e,0)+co)%p
    from collections import defaultdict
    # Q2
    d2 = expand_binom_powerC_minusX(n+1)
    add(d2, n+1, 1)
    add(d2, 0, (-c)%p)
    cands.append(("Q2_order2_ref", n+1, list(d2.items())))

    # Candidate A: Q3a = (c-X)^{n+2} + X^{n+2} - c*( (c-X)+X ) = (c-X)^{n+2}+X^{n+2}-c^2... try forcing triple
    # Better: use that on A, both f=X^n-1 and h=(c-X)^n-1 vanish (order1). f*h vanishes order2 generically.
    # For order3 we want a combination vanishing to order3. Consider P = (c-X)^{n}*X^{n} ... too high deg.
    # The order-2 trick: Q2 = (c-X)*(c-X)^n + X*X^n - c. On A: (c-X)^n=1,X^n=1 -> (c-X)+X-c=0 (val), deriv also 0.
    # Generalize: Q_m built so that after substituting the relations it is the Taylor expansion of 0 to order m.
    # Candidate: R3 = (c-X)^{n+1}*X + X^{n+1}*(c-X) - c*X*(c-X) ... let's just try a few explicit ones and MEASURE.

    # Candidate B (degree n+2): S = (c-X)^{n+2} + X^{n+2} - c^2 + ??? -- measure raw (c-X)^{n+2}+X^{n+2}
    dB = expand_binom_powerC_minusX(n+2)
    add(dB, n+2, 1)
    cands.append(("raw_(c-X)^{n+2}+X^{n+2}", n+2, list(dB.items())))

    # Candidate C: the SQUARE of Q2 -> vanishes order>=4 but degree 2(n+1) ~2n, r<=2(n+1)/4=(n+1)/2 same.
    # skip (no improvement by construction).

    # Candidate D: Q2 * (something of low degree vanishing order1 on A) -> order3 but adds deg.
    #   minimal extra factor vanishing order1 on ALL of A with small degree: none generic except via relations.
    # Candidate E (the real HBK idea): use that A has size r(c) <= (n+1)/2 SMALL, build
    #   auxiliary of degree ~ n vanishing to order ~ sqrt(n). Not closed-form-simple; skip in probe.

    # Candidate F: "second-order Q": Q2'' style. Take T = (c-X)^{n+1} + X^{n+1} - c, and
    #   U = (c-X)^{2n+1} + X^{2n+1} - c. Measure U (deg 2n+1): does it vanish to HIGHER order on A?
    dF = expand_binom_powerC_minusX(2*n+1)
    add(dF, 2*n+1, 1)
    add(dF, 0, (-c)%p)
    cands.append(("(c-X)^{2n+1}+X^{2n+1}-c", 2*n+1, list(dF.items())))

    # Candidate G: (c-X)^{n+1} + X^{n+1} - c  multiplied structurally is messy; measure
    #   V = (c-X)^{n+2} + X^{n+2} - c*(c)  with linear correction to kill value+deriv.
    return cands

def main():
    print("PROBE order-3 explicit Stepanov auxiliary on A = mu_n ∩ (mu_n + c)")
    print("goal: order>=3 auxiliary with deg < 1.5n  =>  r(c) <= deg/3 < (n+1)/2  (BEAT order-2)")
    print("="*80)
    for n in [8, 16]:
        for beta in [4]:
            p = find_prime(n, beta)
            G = set(mu_n(p, n))
            # pick an off-diagonal c: c with c^n != 1 (c not in mu_n) and A=G∩(G+c) nonempty
            found_c = None
            for c in range(1, p):
                if pow(c, n, p) == 1:  # c in mu_n -> diagonal-ish, skip
                    continue
                A = [x for x in G if ((x - c) % p) in G]
                if len(A) >= 2:
                    found_c = (c, A); break
            if not found_c:
                print(f"n={n} p={p}: no good off-diagonal c found"); continue
            c, A = found_c
            print(f"\nn={n} p={p} (p/n^3={p/n**3:.1f})  c={c}  |A|=r(c)={len(A)}  order-2 bound (n+1)/2={ (n+1)//2 }")
            for name, deg, coeffs in candidate_auxiliaries(c, n, p):
                m = root_mult_on_A(coeffs, A, p)
                if m == -1:
                    print(f"   {name:38s} deg={deg:4d}  ZERO POLY (useless)")
                    continue
                implied = deg / m if m>0 else float('inf')
                beat = "  <-- BEATS order-2" if (m>=3 and deg < 1.5*n) else ""
                print(f"   {name:38s} deg={deg:4d}  vanish-order={m}  => r(c)<= deg/m = {implied:.2f}{beat}")

if __name__ == "__main__":
    main()
