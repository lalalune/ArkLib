"""
PROBE (rule 2): scalar-side dilation invariance of the far-line bad-scalar set, MONOMIAL directions.

Claim under test (the structural brick, NOT a moment/incidence bound):
  For RS[F, mu_n, k] on a THIN multiplicative subgroup mu_n (n = 2^a, PROPER subgroup of F*),
  a MONOMIAL far direction u1 = x^A and offset u0 = x^B, the far-line bad-scalar set

      B = { gamma in F : the line  x -> x^B + gamma * x^A  agrees with some
                         degree-<k codeword on a witness set of size >= (1-delta)*n }

  is INVARIANT under multiplication by g^(A-B) for EVERY g in mu_n.
  Mechanism: dilation x -> g*x is a coordinate permutation fixing RS (p(g x) has deg < k).
  Under it  u0 -> g^B u0,  u1 -> g^A u1, so the line  u0 + gamma u1  ->  g^B (u0 + gamma g^(A-B) u1).
  RS is a LINEAR code (closed under the scalar g^B), so gamma is bad  <=>  g^(A-B) gamma is bad.
  => B is a union of  < g^(A-B) : g in mu_n >  = mu_{n / gcd(A-B, n)}  -orbits (cosets).

PRIZE-REGIME DISCIPLINE:
  - PROPER thin subgroup: n = 2^a, mu_n STRICTLY inside F_p*  ((p-1)/n >= 2, often >> ).
  - large primes p >> n^3 AND structured Fermat-type, multiple primes.
  - NEVER n = q-1 (full group -> false positives).
  - "bad" computed by EXACT brute-force list-decode of the line vs all RS codewords (deg<k polys).
We verify THREE things per (n,k,A,B,p,delta):
  (I)  the SET is exactly mult-invariant under g^(A-B) for every g in mu_n  (the brick),
  (II) hence B is a union of  mu_{n'} cosets,  n' = n / gcd(A-B, n)        (the consequence),
  (III) NON-VACUOUS:  B is nonempty and is NOT all of F  in some tested cases (so invariance bites).
"""

import itertools

def is_primitive_root(g, p):
    # order of g is p-1
    if pow(g, p-1, p) != 1:
        return False
    # check g^((p-1)/q) != 1 for prime q | p-1
    m = p-1
    q = 2
    fac = set()
    while q*q <= m:
        while m % q == 0:
            fac.add(q); m //= q
        q += 1
    if m > 1: fac.add(m)
    for q in fac:
        if pow(g, (p-1)//q, p) == 1:
            return False
    return True

def primitive_root(p):
    for g in range(2, p):
        if is_primitive_root(g, p):
            return g
    return None

def subgroup_mun(p, n):
    # mu_n = elements of order dividing n; need n | p-1
    assert (p-1) % n == 0
    g = primitive_root(p)
    h = pow(g, (p-1)//n, p)   # generator of mu_n
    elts = []
    cur = 1
    for _ in range(n):
        elts.append(cur)
        cur = (cur*h) % p
    return sorted(set(elts)), h

def rs_codewords_on_domain(domain, k, p):
    # all evaluations of polys of degree < k on the domain (n points). k coefficients in F_p.
    # returns set of tuples (codeword values on domain).
    n = len(domain)
    cws = set()
    for coeffs in itertools.product(range(p), repeat=k):
        cw = tuple(sum(coeffs[j]*pow(x, j, p) for j in range(k)) % p for x in domain)
        cws.add(cw)
    return cws

def line_eval(domain, B, A, gamma, p):
    # u0 + gamma u1  evaluated on domain:  x^B + gamma x^A
    return tuple((pow(x, B, p) + gamma*pow(x, A, p)) % p for x in domain)

def bad_scalars(domain, k, A, B, p, w):
    # gamma is BAD if the line agrees with SOME codeword on >= w coordinates
    cws = rs_codewords_on_domain(domain, k, p)
    bad = set()
    for gamma in range(p):
        lv = line_eval(domain, B, A, gamma, p)
        for cw in cws:
            agree = sum(1 for a, b in zip(lv, cw) if a == b)
            if agree >= w:
                bad.add(gamma)
                break
    return bad

def gcd(a, b):
    while b: a, b = b, a % b
    return a

# (n=2^a, k, A, B, p, w=(1-delta)n)  -- thin PROPER subgroup, prize-regime-shaped, small enough to brute
CASES = [
    # n, k, A, B, p, w
    (4, 2, 3, 0, 13, 3),    # mu_4 in F_13*, (p-1)/n=3; dir x^3, offset 1; w=3 (delta=1/4)
    (4, 2, 3, 1, 13, 3),    # A-B=2 -> n'=2
    (4, 2, 2, 0, 41, 3),    # A-B=2 -> g^2 invariance,  p=41 >> n^3? 41>64 no; structured
    (4, 1, 3, 0, 17, 2),    # Fermat-ish p=17=2^4+1, mu_4 proper, k=1
    (8, 2, 5, 0, 17, 6),    # mu_8 in F_17 (full? p-1=16, n=8 proper, (p-1)/n=2), dir x^5
    (8, 2, 5, 1, 17, 6),    # A-B=4 -> n'=8/gcd(4,8)=2
    (8, 2, 3, 0, 41, 6),    # mu_8 in F_41, (p-1)/8=5, dir x^3
    (4, 2, 3, 0, 29, 3),    # mu_4 in F_29, (p-1)/4=7
    (4, 2, 1, 0, 53, 3),    # A-B=1 -> n'=4 (full mu_4 invariance), p=53
]

def run():
    nI = nII = nIII = total = 0
    nonvac = 0
    for (n, k, A, B, p, w) in CASES:
        if (p-1) % n != 0:
            print(f"SKIP n={n} p={p}: n does not divide p-1"); continue
        if n == p-1:
            print(f"SKIP n={n} p={p}: n == q-1 (full group, forbidden)"); continue
        domain, h = subgroup_mun(p, n)
        if len(domain) != n:
            print(f"SKIP n={n} p={p}: subgroup size {len(domain)} != {n}"); continue
        d = (A - B) % n
        nprime = n // gcd(d, n)              # mu_{n'} = scalar invariance group exponent set
        # the scalar multipliers:  g^(A-B) for g in mu_n  ==  mu_{n'}
        mults = sorted(set(pow(g, (A - B) % (p-1), p) for g in domain))
        bad = bad_scalars(domain, k, A, B, p, w)
        total += 1
        # (I) invariance: for every m in mults, m*bad (mod p) == bad
        inv_ok = all(set((m*gamma) % p for gamma in bad) == bad for m in mults)
        # (II) union-of-cosets: bad partitions into orbits under multiplication by mults-group
        # orbit of gamma = { m*gamma : m in <mults> }; check each orbit fully in or fully out
        multgrp = set([1])
        changed = True
        while changed:
            changed = False
            for m in mults:
                for x in list(multgrp):
                    y = (m*x) % p
                    if y not in multgrp:
                        multgrp.add(y); changed = True
        coset_ok = True
        seen = set()
        ncosets = 0
        for gamma in range(p):
            if gamma in seen: continue
            orbit = set((m*gamma) % p for m in multgrp)
            seen |= orbit
            inb = orbit & bad
            if inb and inb != orbit:
                coset_ok = False
            if gamma in bad:
                pass
            if orbit <= bad and gamma in bad:
                ncosets += 1
        nonempty = len(bad) > 0
        not_all = len(bad) < p
        if inv_ok: nI += 1
        if coset_ok: nII += 1
        if nonempty: nIII += 1
        if nonempty and not_all: nonvac += 1
        print(f"n={n} k={k} dir(x^{A}) off(x^{B}) p={p} w={w} | "
              f"A-B mod n={d} n'={nprime} |mults|={len(mults)} |multgrp|={len(multgrp)} "
              f"|bad|={len(bad)} "
              f"INV={'OK' if inv_ok else 'FAIL'} COSET={'OK' if coset_ok else 'FAIL'} "
              f"nonempty={nonempty} not_all={not_all}")
    print(f"\nSUMMARY: (I) invariance {nI}/{total}  (II) union-of-cosets {nII}/{total}  "
          f"(III) nonempty {nIII}/{total}  NON-VACUOUS(nonempty & !=F) {nonvac}/{total}")

run()
