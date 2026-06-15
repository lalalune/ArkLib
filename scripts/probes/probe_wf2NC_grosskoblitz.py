#!/usr/bin/env python3
"""wf-NC lane (#407): Gross-Koblitz / p-adic Gamma_p refinement of the period eta_b.

NEW LENS (distinct from section-6 Stickelberger MAGNITUDE no-go):
The section-6 no-go is about |g(chi)| = sqrt(p) (forced ramification / house = sqrt(n)).
Gross-Koblitz expresses the UNIT part of g exactly via Morita's p-adic Gamma function Gamma_p
at the Teichmuller/fractional-part digits.  For q = p (the prize uses q PRIME, f=1):

    g(chi^{-a}) = -pi^{s_p(a)} * Gamma_p( a/(q-1) ) ,   pi^{p-1} = -p,  a=1..q-2

where for f=1 the digit-sum s_p(a) = a (single digit, since a < q-1 = p-1). Hmm, for f=1
the standard statement is g(chi_a) = -pi^a Gamma_p(<a/(p-1)>) ... we test the magnitude/unit
split numerically against the EXACT complex Gauss sum, then test whether the eta_b period
(a SUM of g(chi^j) over a coset) admits archimedean cancellation forced by Gamma_p structure.

Question we decide:
 (Q1) Does GK reproduce g(chi^{-a}) exactly (sanity of our normalization)?
 (Q2) eta_b = (1/m)(-1 + sum_{j=0..m-1} chibar(b)^{j*?} g(chi^{?j})).  Express it via Gamma_p.
 (Q3) Does the DYADIC structure (n=2^mu, the relevant exponents a = j*m, m=(p-1)/n) give a
       special base-p digit pattern that forces sub-trivial max_b|eta_b|, OR does GK only
       re-give |g|=sqrt(p) per term (section-6 trivial) with no SUP handle?
"""
import math, cmath

def isprime(x):
    if x < 2: return False
    if x % 2 == 0: return x == 2
    d = 3
    while d*d <= x:
        if x % d == 0: return False
        d += 2
    return True

def primroot(p):
    fac = set(); m = p-1; d = 2
    while d*d <= m:
        if m % d == 0:
            fac.add(d)
            while m % d == 0: m //= d
        d += 1
    if m > 1: fac.add(m)
    for a in range(2, p):
        if all(pow(a, (p-1)//q, p) != 1 for q in fac): return a

# -------- Morita p-adic Gamma_p, computed p-adically mod p^N (Z_p truncation) --------
def gamma_p_modpN(x_num, x_den, p, N):
    """Morita Gamma_p(x) for x in Z_p given as a p-adic limit; here we evaluate Gamma_p at
    a rational x = x_num/x_den (x_den coprime to p) approximated by its p-adic expansion mod p^N.
    Gamma_p(x) = lim_{n->x, n in Z>=0} (-1)^n * prod_{0<k<n, p notdivides k} k.
    We take n = the residue of x mod p^N lifted to {0,..,p^N-1} (p-adic nearest nonneg integer)."""
    mod = p**N
    inv_den = pow(x_den % mod, -1, mod)
    n = (x_num % mod) * inv_den % mod   # p-adic integer rep of x in {0..p^N-1}
    # product of units < n
    prod = 1
    sign = -1 if (n % 2 == 1) else 1
    # this is O(n) = O(p^N): too big for large p. Only used as a conceptual check for small p^N.
    for k in range(1, n):
        if k % p != 0:
            prod = prod * k % mod
    return (sign * prod) % mod

# -------- archimedean Gauss sum and period (exact-as-float) --------
def gauss_sum(a, p, g0):
    """g(chi^{-a}) with chi(g0)=zeta_{p-1}.  Standard: g(chi) = sum_{t} chi(t) zeta_p^t.
    We compute g(chi^a) = sum_{t=1}^{p-1} chi^a(t) e_p(t), chi(g0^k)=zeta_{p-1}^k."""
    zp = 2j*math.pi/p
    zpm1 = 2j*math.pi/(p-1)
    s = 0+0j
    t = 1
    for k in range(p-1):  # t = g0^k
        s += cmath.exp(zpm1*(a*k)) * cmath.exp(zp*t)
        t = t*g0 % p
    return s

def periods(n, p):
    """eta_b for the n cosets of mu_n? No: eta_b indexed by b in F_p^*, distinct values = m=(p-1)/n.
    eta_b = sum_{x in mu_n} e_p(b x).  Direct (archimedean) ground truth."""
    g0 = primroot(p); m = (p-1)//n
    g = pow(g0, m, p)
    mu = [pow(g, i, p) for i in range(n)]
    zp = 2j*math.pi/p
    out = []
    b = 1
    for c in range(m):  # one b per coset rep g0^c
        s = sum(cmath.exp(zp*(b*x % p)) for x in mu)
        out.append(s); b = b*g0 % p
    return out, m

def period_via_gauss(n, p):
    """eta_b = (1/m)( -1 + sum_{j=0}^{m-1} chibar^{?}(b) g(chi^{j m}) )?
    Standard Gauss-period expansion: the indicator of mu_n = subgroup of index m.
    1_{mu_n}(x) = (1/(p-1)) sum_{chi: chi|mu_n =1} chi(x) over the m characters trivial on mu_n,
    i.e. chi = psi^{n k}, k=0..m-1, psi a generator of the character group.
    eta_b = sum_{x in F_p^*} 1_{mu_n}(x) e_p(b x)
          = (1/m) sum_{k=0}^{m-1} psi^{-n k}(b) * g(psi^{n k})   (with g(chi)=sum chi(t)e_p(t)),
    plus the x=0 correction is none (0 not in F_p^*).  Actually |mu_n|=n, and the projector
    has weight n/(p-1) per char... let's just verify numerically against the direct sum."""
    g0 = primroot(p); m = (p-1)//n
    zpm1 = 2j*math.pi/(p-1)
    # g(psi^{nk}) where psi(g0)=zeta_{p-1}: char index = n*k
    out = []
    b = 1
    # precompute gauss sums for exponents n*k
    gs = {}
    for k in range(m):
        a = (n*k) % (p-1)
        if a not in gs:
            gs[a] = gauss_sum(a, p, g0)
    for c in range(m):  # b = g0^c
        s = 0+0j
        bk = 0  # exponent of b in base g0
        # b = g0^c so psi^{-nk}(b) = zeta_{p-1}^{-n k c}
        for k in range(m):
            a = (n*k) % (p-1)
            s += cmath.exp(-zpm1*(n*k*c)) * gs[a]
        out.append(s/m)
        b = b*g0 % p
    return out, m

if __name__ == "__main__":
    print("=== Q2: verify Gauss-period expansion reproduces direct eta_b ===", flush=True)
    for n in [8, 16]:
        ps = [pp for pp in range(n+1, 600) if isprime(pp) and (pp-1) % n == 0][:3]
        for p in ps:
            d, m = periods(n, p)
            gpe, _ = period_via_gauss(n, p)
            err = max(abs(d[i]-gpe[i]) for i in range(m))
            B = max(abs(z) for z in d)
            print(f"n={n} p={p} m={m}  max|eta|={B:.4f}  B/sqrt(p-n)={B/math.sqrt(p-n):.4f}  GK-expansion err={err:.2e}", flush=True)
