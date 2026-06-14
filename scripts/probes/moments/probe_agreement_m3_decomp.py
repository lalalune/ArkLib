#!/usr/bin/env python3
"""Decomposition engine for the agreement-spectrum third-moment tensor M3.

Issue #334 moments lane, probe protocol step 2.  Ground-truth arbiter:
probe_agreement_m3_bruteforce.py (same directory, identical JSON schema, diffable
byte-for-byte).  Hypothesis ledger: HYPOTHESES-M3.md.

Setting (exact integer arithmetic, Python stdlib only):
  q an odd prime; domain D = n distinct nonzero elements of F_q;
  code C = all univariate polynomials over F_q of degree < k (q^k of them, incl. 0),
  as evaluation vectors on D;
  a_j(u) = #{p in C : p(x) = u(x) for exactly j of the n points x in D};
  M1[j] = sum_u a_j(u);   M3[j1][j2][j3] = sum_u a_{j1}(u) a_{j2}(u) a_{j3}(u),
  summed over all q^n received words u.  Supported here: k in {2, 3}, n >= k.

Decomposition (every step re-derived from scratch for this file; each is enforced
by an internal assert against closed forms or direct enumeration at small scale,
and the brute-force engine arbitrates the final tensor):

(1) Translation.  Substituting u = v + p3, c = p1 - p3, c' = p2 - p3 (bijections):
      M3[j1,j2,j3] = q^k * sum over ORDERED pairs (c,c') in C^2 of N_{j1,j2,j3}(c,c'),
    where N counts words v with #{x: v=c} = j1, #{x: v=c'} = j2, #{x: v=0} = j3.

(2) Coordinates are independent; per coordinate x the factor depends only on the
    type of (c(x), c'(x))  (z1 marks v(x)=c(x), z2 marks v(x)=c'(x), z3 marks v(x)=0):
      A (c=c'=0)        : z1*z2*z3 + (q-1)
      B (c=0,  c'!=0)   : z1*z3 + z2 + (q-2)     [v=0 agrees with c AND with 0]
      C (c!=0, c'=0)    : z2*z3 + z1 + (q-2)
      D (c=c'!=0)       : z1*z2 + z3 + (q-2)
      E (c,c'!=0, c!=c'): z1 + z2 + z3 + (q-3)
    N(profile) = [z1^j1 z2^j2 z3^j3]  A^a B^b C^c D^d E^e,  profile = (a,b,c,d,e).

(3) Dependent pair classes: (0,0) -> (n,0,0,0,0);  (c,0) -> (n-w,0,w,0,0);
    (0,c') -> (n-w,w,0,0,0);  (c,c) -> (n-w,0,0,w,0);  (c,tc), t != 0,1 ->
    (n-w,0,0,0,w);  w = wt(c) on D.  Needs only the MDS weight distribution
      A_w = C(n,w) * sum_{i=0}^{w-d} (-1)^i C(w,i) (q^{w-d+1-i} - 1),  d = n-k+1,
    cross-checked against the equivalent (q-1)*sum (-1)^i C(w-1,i) q^{w-d-i} form,
    against sum_w A_w = q^k - 1, and against direct enumeration when cheap.

(4) Independent pairs at k=3 organize by the 2-dim subcode V = ker(phi),
    phi = (phi0,phi1,phi2) a point of PG(2,q), with the pairing
      c = alpha + beta*X + gamma*X^2 in V  <=>  alpha*phi0 + beta*phi1 + gamma*phi2 = 0.
    For x != y both in supp(V), x and y land in the same fiber of the basis map
    x -> [c(x):c'(x)] in P^1  <=>  (X-x)(X-y) in V  <=>
      phi0*x*y - phi1*(x+y) + phi2 = 0
    (expand det[[phi0,phi1,phi2],[1,x,x^2],[1,y,y^2]] = (y-x)(phi0*x*y - phi1*(x+y) + phi2);
    (X-x)(X-y) has coefficient vector (xy, -(x+y), 1)).  This is a Moebius involution,
    so fibers have size <= 2 and each x in supp has at most one partner
    y = (phi1*x - phi2)/(phi0*x - phi1).  x is OUTSIDE supp(V) iff phi is the conic
    point ev_x = (1, x, x^2) up to scalar, so A = #common zeros in D is 0 or 1.
    Per-phi fiber data: (A, s = n - A, t2 = #two-element fibers inside D).
    Verified against direct fiber computation from an explicit kernel basis for
    EVERY phi when q <= 13.

(5) Ordered bases <-> ordered distinct triples.  PGL2(q) is sharply 3-transitive on
    P^1 and the GL2 -> PGL2 kernel has size q-1, so for any function f of the fiber
    multiplicities at the three special points [0:1], [1:0], [1:1]:
      sum over ordered bases (c,c') of V of f(m(B-pt), m(C-pt), m(D-pt))
        = (q-1) * sum over ordered triples of DISTINCT P1,P2,P3 in P^1 of
                  f(m_{P1}, m_{P2}, m_{P3}).
    With multiplicity classes n1 = s - 2*t2 points of m=1, n2 = t2 of m=2,
    n0 = (q+1) - n1 - n2 of m=0, the number of ordered distinct triples typed
    (m1,m2,m3) is  n_{m1} * (n_{m2} - [m1=m2]) * (n_{m3} - [m1=m3] - [m2=m3]),
    and the profile fed to N is (a,b,c,d,e) = (A, m1, m2, m3, s - m1 - m2 - m3).
    Verified against full GL2 basis enumeration at small q.

(6) k=2: the only 2-dim subcode is C itself; (A, s, t2) is computed directly from
    the basis (1, X) and ASSERTED to be (0, n, 0) (fibers injective: a deg<=1 poly
    cannot vanish at two distinct points; constants kill common zeros).

Global asserts (any failure exits nonzero):
  * ordered-pair partition  q^{2k} = 1 + 2(q^k-1) + (q^k-1)(q-1) + #V*(q^2-1)(q^2-q),
    #V = (q^3-1)/(q-1) at k=3, #V = 1 at k=2;
  * sum_phi t2(phi) = C(n,2)*(q-1)   [the dual line of phis through a fixed pair
    {x,y} has q+1 points of which exactly the two conic points ev_x, ev_y are
    excluded -- this pins the H5 constant];
  * M3 tensor S3-symmetric;
  * sum_{j3} M3 = q^k * M2 closed form (same machinery at pair level, independent code);
  * sum_{j2,j3} M3 = q^{2k} * M1 closed form;  grand total sum M3 = q^(n+3k).

CLI (identical schema to the brute engine):
  python3 probe_agreement_m3_decomp.py --q 5 --k 2 --domain 1,2,3,4
      [--json-out PATH] [--census]
  --domain subgroup:N = the order-N multiplicative subgroup of F_q* (N | q-1).
  --census adds a "census" key to the JSON: the full t2 histogram over phi plus
  the list of (phi, s, t2) with t2 >= 3 sorted by t2 descending (mechanism data).

Output (stdout, and --json-out PATH if given):
  {"q":int,"n":int,"k":int,"domain":[sorted ints],"M1":{"j":count,...},
   "M3":{"j1,j2,j3":count,...}}    (M3 keys only for nonzero entries)
"""

import argparse
import itertools
import json
import math
import sys

# ----------------------------------------------------------------------------- field/CLI


def is_prime(m: int) -> bool:
    if m < 2:
        return False
    if m % 2 == 0:
        return m == 2
    f = 3
    while f * f <= m:
        if m % f == 0:
            return False
        f += 2
    return True


def prime_factors(m: int) -> set:
    fs = set()
    d = 2
    while d * d <= m:
        while m % d == 0:
            fs.add(d)
            m //= d
        d += 1
    if m > 1:
        fs.add(m)
    return fs


def primitive_root(q: int) -> int:
    fs = prime_factors(q - 1)
    for g in range(2, q):
        if all(pow(g, (q - 1) // p, q) != 1 for p in fs):
            return g
    raise ValueError(f"no primitive root found for q={q} (q not prime?)")


def parse_domain(spec: str, q: int) -> list:
    """Parse --domain: either 'subgroup:N' (order-N subgroup of F_q*) or a comma list."""
    if spec.startswith("subgroup:"):
        N = int(spec.split(":", 1)[1])
        if N <= 0 or (q - 1) % N != 0:
            raise SystemExit(f"error: subgroup order N={N} must satisfy N | q-1 = {q - 1}")
        g = primitive_root(q)
        h = pow(g, (q - 1) // N, q)
        dom, e = [], 1
        for _ in range(N):
            dom.append(e)
            e = (e * h) % q
        if len(set(dom)) != N:
            raise SystemExit(f"error: subgroup construction yielded repeats (N={N}, q={q})")
        return sorted(dom)
    vals = [int(t) % q for t in spec.split(",") if t.strip() != ""]
    if not vals:
        raise SystemExit("error: empty domain")
    if any(v == 0 for v in vals):
        raise SystemExit("error: domain elements must be nonzero in F_q")
    if len(set(vals)) != len(vals):
        raise SystemExit("error: domain elements must be distinct mod q")
    return sorted(vals)


# --------------------------------------------------------------- single-weight distribution


def weight_distribution_mds(q: int, n: int, k: int) -> dict:
    """A_w = #{c in C, c != 0 : wt(c) on D = w}; MDS closed form, two equivalent shapes
    cross-asserted, plus the mass identity sum_w A_w = q^k - 1."""
    d = n - k + 1
    out = {}
    for w in range(d, n + 1):
        main = math.comb(n, w) * sum(
            (-1) ** i * math.comb(w, i) * (q ** (w - d + 1 - i) - 1)
            for i in range(w - d + 1))
        alt = math.comb(n, w) * (q - 1) * sum(
            (-1) ** i * math.comb(w - 1, i) * q ** (w - d - i)
            for i in range(w - d + 1))
        assert main == alt, f"MDS weight-distribution forms disagree at w={w}: {main} != {alt}"
        assert main >= 0, f"A_{w} = {main} < 0"
        if main:
            out[w] = main
    assert sum(out.values()) == q ** k - 1, "sum_w A_w != q^k - 1"
    return out


def weight_distribution_direct(q: int, k: int, domain: list) -> dict:
    """Direct enumeration of all q^k - 1 nonzero codewords via the histogram trick:
    for fixed high coefficients (c_1..c_{k-1}), histogram -(c_1 x + ... ) over x in D;
    then for each constant term c0 the zero count is hist[c0].  Cost q^{k-1}*(n*k + q)."""
    n = len(domain)
    counts = {}
    powtab = [[pow(x, e, q) for x in domain] for e in range(k)]
    for hi in itertools.product(range(q), repeat=k - 1):
        hist = [0] * q
        for i in range(n):
            v = 0
            for e in range(1, k):
                v += hi[e - 1] * powtab[e][i]
            hist[(-v) % q] += 1
        allz = not any(hi)
        for c0 in range(q):
            if c0 == 0 and allz:
                continue  # the zero codeword
            w = n - hist[c0]
            counts[w] = counts.get(w, 0) + 1
    return counts


# ----------------------------------------------------------- N(profile) generating tensors


_N_CACHE = {}


def _expand_a(a: int, q: int) -> dict:
    # (z1*z2*z3 + (q-1))^a
    return {(i, i, i): math.comb(a, i) * (q - 1) ** (a - i) for i in range(a + 1)}


def _expand_b(b: int, q: int) -> dict:
    # (z1*z3 + z2 + (q-2))^b ; term (z1z3)^i z2^j -> key (i, j, i)
    out = {}
    for i in range(b + 1):
        ci = math.comb(b, i)
        for j in range(b - i + 1):
            out[(i, j, i)] = ci * math.comb(b - i, j) * (q - 2) ** (b - i - j)
    return out


def _expand_c(c: int, q: int) -> dict:
    # (z2*z3 + z1 + (q-2))^c ; term (z2z3)^i z1^j -> key (j, i, i)
    out = {}
    for i in range(c + 1):
        ci = math.comb(c, i)
        for j in range(c - i + 1):
            out[(j, i, i)] = ci * math.comb(c - i, j) * (q - 2) ** (c - i - j)
    return out


def _expand_d(d: int, q: int) -> dict:
    # (z1*z2 + z3 + (q-2))^d ; term (z1z2)^i z3^j -> key (i, i, j)
    out = {}
    for i in range(d + 1):
        ci = math.comb(d, i)
        for j in range(d - i + 1):
            out[(i, i, j)] = ci * math.comb(d - i, j) * (q - 2) ** (d - i - j)
    return out


def _expand_e(e: int, q: int) -> dict:
    # (z1 + z2 + z3 + (q-3))^e ; term z1^i z2^j z3^l -> key (i, j, l)
    out = {}
    for i in range(e + 1):
        ci = math.comb(e, i)
        for j in range(e - i + 1):
            cij = ci * math.comb(e - i, j)
            for l in range(e - i - j + 1):
                out[(i, j, l)] = cij * math.comb(e - i - j, l) * (q - 3) ** (e - i - j - l)
    return out


def _pmul3(P: dict, Q: dict) -> dict:
    if len(P) > len(Q):
        P, Q = Q, P
    out = {}
    for (a1, b1, c1), v1 in P.items():
        for (a2, b2, c2), v2 in Q.items():
            key = (a1 + a2, b1 + b2, c1 + c2)
            out[key] = out.get(key, 0) + v1 * v2
    return out


def n_tensor(profile: tuple, q: int) -> dict:
    """{(j1,j2,j3): N_{j1,j2,j3}(profile)} for profile = (a,b,c,d,e); cached."""
    key = (q,) + profile
    if key in _N_CACHE:
        return _N_CACHE[key]
    a, b, c, d, e = profile
    assert min(profile) >= 0, f"negative profile {profile}"
    poly = {(0, 0, 0): 1}
    parts = [_expand_a(a, q), _expand_b(b, q), _expand_c(c, q), _expand_d(d, q)]
    for p in sorted(parts, key=len):
        poly = _pmul3(poly, p)
    poly = _pmul3(poly, _expand_e(e, q))
    total = sum(poly.values())
    assert total == q ** (a + b + c + d + e), \
        f"N({profile}) mass {total} != q^n = {q ** (a + b + c + d + e)}"
    _N_CACHE[key] = poly
    return poly


def verify_n_tensor_brute(q: int, profile: tuple) -> None:
    """Brute check of (2): build a synthetic (c,c') pair realizing the profile and count
    all q^n words v directly.  Gated by the caller (cost q^n * n)."""
    a, b, c, d, e = profile
    n = a + b + c + d + e
    cv = (0,) * a + (0,) * b + (1,) * c + (1,) * d + (1,) * e
    cpv = (0,) * a + (1,) * b + (0,) * c + (1,) * d + (2,) * e
    got = {}
    for v in itertools.product(range(q), repeat=n):
        j1 = sum(1 for i in range(n) if v[i] == cv[i])
        j2 = sum(1 for i in range(n) if v[i] == cpv[i])
        j3 = sum(1 for i in range(n) if v[i] == 0)
        kk = (j1, j2, j3)
        got[kk] = got.get(kk, 0) + 1
    expect = {kk: vv for kk, vv in n_tensor(profile, q).items() if vv}
    assert got == expect, f"N tensor brute mismatch at profile {profile}"


# ------------------------------------------------------------------- pencil data (k = 3)


def iter_pg2(q: int):
    """Canonical representatives of the q^2+q+1 points of PG(2,q)."""
    for b in range(q):
        for c in range(q):
            yield (1, b, c)
    for c in range(q):
        yield (0, 1, c)
    yield (0, 0, 1)


def pencil_data(q: int, domain: list) -> list:
    """Per dual point phi: (phi, A, s, t2) from the Moebius-involution relation of (4)."""
    n = len(domain)
    dset = set(domain)
    inv = [0] * q
    for v in range(1, q):
        inv[v] = pow(v, q - 2, q)
    per_phi = []
    for phi in iter_pg2(q):
        p0, p1, p2 = phi
        # common zero of V on D: phi ~ (1, x, x^2) with x in D
        x0 = p1 if (p0 == 1 and (p1 * p1) % q == p2 and p1 in dset) else None
        A = 0 if x0 is None else 1
        s = n - A
        matched = 0
        for x in domain:
            if x == x0:
                continue
            den = (p0 * x - p1) % q
            if den == 0:
                continue  # within supp(V) this means no partner (see module docstring)
            y = ((p1 * x - p2) * inv[den]) % q
            if y != x and y != x0 and y in dset:
                matched += 1
        assert matched % 2 == 0, f"asymmetric partner relation at phi={phi}"
        per_phi.append((phi, A, s, matched // 2))
    assert len(per_phi) == q * q + q + 1
    return per_phi


def phi_kernel_basis(phi: tuple, q: int) -> tuple:
    """Two independent coefficient triples (alpha,beta,gamma) spanning ker(phi)."""
    p0, p1, p2 = phi
    if p0 != 0:  # canonical p0 == 1
        return ((-p1) % q, 1, 0), ((-p2) % q, 0, 1)
    if p1 != 0:  # (0,1,c)
        return (1, 0, 0), (0, (-p2) % q, 1)
    return (1, 0, 0), (0, 1, 0)  # (0,0,1)


def fiber_data_from_evals(q: int, ev1: tuple, ev2: tuple) -> tuple:
    """Direct (A, s, t2) of the map x -> [c(x):c'(x)] given the two basis eval vectors."""
    fibers = {}
    A = 0
    for u, v in zip(ev1, ev2):
        if u == 0 and v == 0:
            A += 1
            continue
        key = (1, (v * pow(u, q - 2, q)) % q) if u != 0 else (0, 1)
        fibers[key] = fibers.get(key, 0) + 1
    sizes = list(fibers.values())
    assert A <= 1, f"more than one common zero: A={A}"
    assert max(sizes, default=0) <= 2, f"fiber of size > 2: {sizes}"
    return A, len(ev1) - A, sum(1 for m in sizes if m == 2)


def eval_triple(coeffs: tuple, domain: list, q: int) -> tuple:
    al, be, ga = coeffs
    return tuple((al + be * x + ga * x * x) % q for x in domain)


def profile_of_pair(cv: tuple, cpv: tuple) -> tuple:
    a = b = c = d = e = 0
    for u, v in zip(cv, cpv):
        if u == 0:
            if v == 0:
                a += 1
            else:
                b += 1
        elif v == 0:
            c += 1
        elif u == v:
            d += 1
        else:
            e += 1
    return (a, b, c, d, e)


def triple_weights(q: int, A: int, s: int, t2: int) -> dict:
    """{(m1,m2,m3): #ordered distinct triples typed (m1,m2,m3)} for one V; asserts the
    total equals (q+1)q(q-1) = #ordered distinct triples in P^1."""
    n2 = t2
    n1 = s - 2 * t2
    n0 = (q + 1) - n1 - n2
    assert n1 >= 0 and n0 >= 0, f"bad fiber data (A,s,t2)=({A},{s},{t2})"
    ncl = (n0, n1, n2)
    out = {}
    total = 0
    for m1 in range(3):
        for m2 in range(3):
            for m3 in range(3):
                cnt = (ncl[m1]
                       * (ncl[m2] - (m1 == m2))
                       * (ncl[m3] - (m1 == m3) - (m2 == m3)))
                assert cnt >= 0
                total += cnt
                if cnt:
                    out[(m1, m2, m3)] = cnt
    assert total == (q + 1) * q * (q - 1), "triple count total != (q+1)q(q-1)"
    return out


def verify_basis_triple_identity(q: int, domain: list, basis_evals: tuple,
                                 A: int, s: int, t2: int) -> None:
    """Brute check of (5): enumerate ALL ordered bases of V (all GL2 combinations of the
    given basis) and compare the profile histogram against (q-1) * triple weights."""
    ev1, ev2 = basis_evals
    got = {}
    for a in range(q):
        for b in range(q):
            for u in range(q):
                for v in range(q):
                    if (a * v - b * u) % q == 0:
                        continue
                    cv = tuple((a * x + b * y) % q for x, y in zip(ev1, ev2))
                    cpv = tuple((u * x + v * y) % q for x, y in zip(ev1, ev2))
                    pr = profile_of_pair(cv, cpv)
                    got[pr] = got.get(pr, 0) + 1
    expect = {}
    for (m1, m2, m3), cnt in triple_weights(q, A, s, t2).items():
        pr = (A, m1, m2, m3, s - m1 - m2 - m3)
        expect[pr] = expect.get(pr, 0) + cnt * (q - 1)
    assert got == expect, f"ordered-bases vs (q-1)*triples mismatch: {got} != {expect}"


# ----------------------------------------------------------------------- M2 closed form


def m2_closed_form(q: int, k: int, n: int, wd: dict) -> dict:
    """M2[j1][j2] = sum_u a_{j1}(u) a_{j2}(u) by the SAME translation machinery at pair
    level: M2 = q^k * sum_c [z1^j1 z2^j2] (z1z2 + q-1)^{n-w} (z1 + z2 + q-2)^w over the
    weight classes of single codewords c.  Used as the j3-marginal reference for M3."""
    qk = q ** k
    acc = {}
    for w, mult in [(0, 1)] + sorted(wd.items()):
        P = {(i, i): math.comb(n - w, i) * (q - 1) ** (n - w - i) for i in range(n - w + 1)}
        Q = {}
        for i in range(w + 1):
            ci = math.comb(w, i)
            for j in range(w - i + 1):
                Q[(i, j)] = ci * math.comb(w - i, j) * (q - 2) ** (w - i - j)
        for (i1, i2), v1 in P.items():
            for (j1, j2), v2 in Q.items():
                kk = (i1 + j1, i2 + j2)
                acc[kk] = acc.get(kk, 0) + mult * v1 * v2
    M2 = {kk: qk * v for kk, v in acc.items() if v}
    for j1 in range(n + 1):
        srow = sum(v for (a, _), v in M2.items() if a == j1)
        expect = qk * qk * math.comb(n, j1) * (q - 1) ** (n - j1)
        assert srow == expect, f"M2 closed form fails its own M1 marginal at j1={j1}"
    return M2


# ------------------------------------------------------------------------------ assembly


def compute_m3_decomp(q: int, k: int, domain: list, checks: list):
    n = len(domain)
    qk = q ** k

    # (3) single-codeword weight distribution
    wd = weight_distribution_mds(q, n, k)
    checks.append("MDS weight distribution: two closed forms agree; sum_w A_w == q^k - 1")
    if q ** (k - 1) * (n * k + q) <= 3_000_000:
        assert wd == weight_distribution_direct(q, k, domain), \
            "MDS weight-distribution formula != direct enumeration"
        checks.append("MDS weight distribution == direct enumeration over all q^k codewords")

    # (4)/(6) fiber data of the 2-dim subcodes
    if k == 3:
        per_phi = pencil_data(q, domain)
        n_v = len(per_phi)
        assert n_v == (q ** 3 - 1) // (q - 1)
        if q <= 13:
            for (phi, A, s, t2) in per_phi:
                b1, b2 = phi_kernel_basis(phi, q)
                ev = (eval_triple(b1, domain, q), eval_triple(b2, domain, q))
                assert fiber_data_from_evals(q, *ev) == (A, s, t2), \
                    f"relation-based fiber data != direct at phi={phi}"
            checks.append(
                "fiber relation phi0*x*y - phi1*(x+y) + phi2 == 0 matches direct fiber "
                f"computation from explicit kernel bases for all {n_v} phi")
        sum_t2 = sum(t2 for (_, _, _, t2) in per_phi)
        assert sum_t2 == math.comb(n, 2) * (q - 1), \
            f"sum_phi t2 = {sum_t2} != C(n,2)*(q-1) = {math.comb(n, 2) * (q - 1)}"
        checks.append("sum_phi t2(phi) == C(n,2)*(q-1)  [H5 constant pinned: dual line "
                      "minus its 2 conic points]")
    else:  # k == 2: the single V = C with basis (1, X)
        ev = (tuple([1] * n), tuple(domain))
        A, s, t2 = fiber_data_from_evals(q, *ev)
        assert (A, s, t2) == (0, n, 0), f"k=2 fiber data {(A, s, t2)} != (0, n, 0)"
        checks.append("k=2: single V = C has (A, s, t2) == (0, n, 0) by direct computation")
        per_phi = [(None, A, s, t2)]
        n_v = 1

    # (7) ordered-pair partition
    n_dep = 1 + 2 * (qk - 1) + (qk - 1) * (q - 1)
    n_ind = n_v * (q * q - 1) * (q * q - q)
    assert n_dep + n_ind == qk * qk, "ordered-pair partition of q^{2k} fails"
    checks.append("ordered-pair partition q^{2k} == 1 + 2(q^k-1) + (q^k-1)(q-1) "
                  "+ #V*(q^2-1)(q^2-q)")

    # (5) basis <-> triple identity, brute-checked on all/sampled V at small q
    if q <= 13:
        if k == 2:
            sample = [(None, 0, n, 0)]
            basis_for = {None: ((1, 0), (0, 1))}  # placeholder; evals built below
        elif q <= 7:
            sample = per_phi
        else:
            stride = max(1, len(per_phi) // 7)
            sample = per_phi[::stride]
            sample.append(max(per_phi, key=lambda r: r[3]))  # include a max-t2 pencil
        for (phi, A, s, t2) in sample:
            if k == 2:
                ev = (tuple([1] * n), tuple(domain))
            else:
                b1, b2 = phi_kernel_basis(phi, q)
                ev = (eval_triple(b1, domain, q), eval_triple(b2, domain, q))
            verify_basis_triple_identity(q, domain, ev, A, s, t2)
        checks.append(f"ordered-bases == (q-1)*distinct-triples identity brute-checked on "
                      f"{len(sample)} subcode(s) by full GL2 enumeration")

    # ------- assemble S = sum over ordered pairs (c,c') of N(profile) -------
    S = {}

    def add(tensor: dict, mult: int) -> None:
        if mult == 0:
            return
        for kk, v in tensor.items():
            if v:
                S[kk] = S.get(kk, 0) + mult * v

    add(n_tensor((n, 0, 0, 0, 0), q), 1)                      # (0,0)
    for w, aw in sorted(wd.items()):
        add(n_tensor((n - w, 0, w, 0, 0), q), aw)             # (c,0), c != 0
        add(n_tensor((n - w, w, 0, 0, 0), q), aw)             # (0,c')
        add(n_tensor((n - w, 0, 0, w, 0), q), aw)             # (c,c)
        add(n_tensor((n - w, 0, 0, 0, w), q), aw * (q - 2))   # (c,tc), t != 0,1

    # independent pairs: aggregate triple weights over the (A,s,t2) classes
    class_counts = {}
    for (_, A, s, t2) in per_phi:
        kk = (A, s, t2)
        class_counts[kk] = class_counts.get(kk, 0) + 1
    W = {}  # (A, (m1,m2,m3)) -> summed ordered-distinct-triple count over all V
    for (A, s, t2), cnt in class_counts.items():
        for m, c3 in triple_weights(q, A, s, t2).items():
            kk = (A, m)
            W[kk] = W.get(kk, 0) + cnt * c3
    for (A, (m1, m2, m3)), wgt in W.items():
        e = n - A - m1 - m2 - m3
        assert e >= 0, f"negative E count for (A,m)={(A, (m1, m2, m3))}"
        add(n_tensor((A, m1, m2, m3, e), q), wgt * (q - 1))

    # brute verification of N itself on a sample of the profiles actually used
    if q ** n <= 200_000:
        keys = sorted(pr for (qq, *pr) in [k_ for k_ in _N_CACHE] if qq == q)
        keys = [tuple(pr) for pr in keys]
        m = len(keys)
        take = sorted({0, m // 4, m // 2, m - 1}) if q ** n <= 100_000 else [0, m // 2, m - 1]
        for idx in sorted(set(take)):
            verify_n_tensor_brute(q, keys[idx])
        checks.append(f"N(profile) == brute count over all q^n words for "
                      f"{len(set(take))} sampled profiles")

    # full ordered-pair profile histogram against the class decomposition
    if qk <= 1400:
        powtab = [[pow(x, e, q) for e in range(k)] for x in domain]
        evals = [tuple(sum(cf[e] * powtab[i][e] for e in range(k)) % q for i in range(n))
                 for cf in itertools.product(range(q), repeat=k)]
        got = {}
        for cv in evals:
            for cpv in evals:
                pr = profile_of_pair(cv, cpv)
                got[pr] = got.get(pr, 0) + 1
        expect = {}

        def bump(pr, mult):
            if mult:
                expect[pr] = expect.get(pr, 0) + mult

        bump((n, 0, 0, 0, 0), 1)
        for w, aw in wd.items():
            bump((n - w, 0, w, 0, 0), aw)
            bump((n - w, w, 0, 0, 0), aw)
            bump((n - w, 0, 0, w, 0), aw)
            bump((n - w, 0, 0, 0, w), aw * (q - 2))
        for (A, (m1, m2, m3)), wgt in W.items():
            bump((A, m1, m2, m3, n - A - m1 - m2 - m3), wgt * (q - 1))
        assert got == expect, "ordered-pair profile histogram != class decomposition"
        checks.append("profile histogram over ALL q^{2k} ordered codeword pairs == "
                      "class decomposition (brute, end-to-end)")

    M3 = {}
    for kk, v in S.items():
        assert v >= 0
        if v:
            M3[kk] = qk * v
    return M3, wd, per_phi


def run_global_asserts(q: int, k: int, n: int, M3: dict, wd: dict, checks: list) -> None:
    qk = q ** k

    for (j1, j2, j3), v in M3.items():
        for p in ((j2, j1, j3), (j1, j3, j2), (j3, j2, j1), (j2, j3, j1), (j3, j1, j2)):
            assert M3.get(p, 0) == v, f"M3 not S3-symmetric at {(j1, j2, j3)} vs {p}"
    checks.append("M3 tensor is S3-symmetric")

    M2 = m2_closed_form(q, k, n, wd)
    marg2 = {}
    for (j1, j2, _), v in M3.items():
        marg2[(j1, j2)] = marg2.get((j1, j2), 0) + v
    assert marg2 == {kk: qk * v for kk, v in M2.items()}, \
        "sum_{j3} M3 != q^k * M2 closed form"
    checks.append("sum_j3 M3[j1][j2][j3] == q^k * M2 closed form for all (j1,j2)")

    marg1 = {}
    for (j1, _, _), v in M3.items():
        marg1[j1] = marg1.get(j1, 0) + v
    for j1 in range(n + 1):
        expect = qk * qk * qk * math.comb(n, j1) * (q - 1) ** (n - j1)
        assert marg1.get(j1, 0) == expect, f"sum_{{j2,j3}} M3[{j1}] != q^(2k)*M1[{j1}]"
    checks.append("sum_{j2,j3} M3[j1][j2][j3] == q^(2k) * M1 closed form for all j1")

    assert sum(M3.values()) == q ** (n + 3 * k), "total M3 mass != q^(n+3k)"
    checks.append("sum over all (j1,j2,j3) of M3 == q^(n+3k)")


def build_census(per_phi: list) -> dict:
    hist = {}
    for (_, _, _, t2) in per_phi:
        hist[t2] = hist.get(t2, 0) + 1
    high = sorted(((phi, s, t2) for (phi, _, s, t2) in per_phi if t2 >= 3),
                  key=lambda r: (-r[2], r[0] if r[0] is not None else ()))
    return {
        "t2_hist": {str(t2): hist[t2] for t2 in sorted(hist)},
        "high_t2": [{"phi": list(phi), "s": s, "t2": t2} for (phi, s, t2) in high],
    }


# ----------------------------------------------------------------------------------- main


def main() -> int:
    ap = argparse.ArgumentParser(
        description="Decomposition engine for agreement-spectrum moments M1 and M3.")
    ap.add_argument("--q", type=int, required=True, help="odd prime field size")
    ap.add_argument("--k", type=int, required=True, help="degree bound (code = deg < k); 2 or 3")
    ap.add_argument("--domain", type=str, required=True,
                    help="comma list of distinct nonzero elements, or subgroup:N (N | q-1)")
    ap.add_argument("--json-out", type=str, default=None,
                    help="also write the JSON result to this path")
    ap.add_argument("--census", action="store_true",
                    help="add the pencil census (t2 histogram + t2>=3 list) to the JSON")
    args = ap.parse_args()

    q, k = args.q, args.k
    if not is_prime(q) or q == 2:
        raise SystemExit(f"error: q={q} must be an odd prime")
    if k not in (2, 3):
        raise SystemExit(f"error: k={k} unsupported (decomposition implemented for k in {{2,3}})")
    domain = parse_domain(args.domain, q)
    n = len(domain)
    if n < k:
        raise SystemExit(f"error: need n >= k (evaluation injective / MDS), got n={n} < k={k}")

    checks = []
    M3, wd, per_phi = compute_m3_decomp(q, k, domain, checks)
    run_global_asserts(q, k, n, M3, wd, checks)
    for c in checks:
        print(f"[assert ok] {c}", file=sys.stderr)

    qk = q ** k
    result = {
        "q": q,
        "n": n,
        "k": k,
        "domain": domain,
        "M1": {str(j): qk * math.comb(n, j) * (q - 1) ** (n - j) for j in range(n + 1)},
        "M3": {f"{j1},{j2},{j3}": M3[(j1, j2, j3)] for (j1, j2, j3) in sorted(M3)},
    }
    if args.census:
        result["census"] = build_census(per_phi)
    blob = json.dumps(result, separators=(",", ":"))
    print(blob)
    if args.json_out:
        with open(args.json_out, "w") as fh:
            fh.write(blob + "\n")
    return 0


if __name__ == "__main__":
    sys.exit(main())
