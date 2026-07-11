#!/usr/bin/env python3
"""
wf-D4 (#444): the ORBIT-CLOSURE ASYMMETRY behind "monomial is the worst over-determined direction".

Lever (ActionOrbitGeneralF + ActionOrbitFRI substrate):
  - MONOMIAL direction u1 = x^b, offset u0 = x^a: dilation D_mu (x -> mu*x, mu in mu_n a generator)
    is an EIGENVECTOR action: x^b -> mu^b x^b, x^a -> mu^a x^a, so the affine line
    {x^a + gamma x^b} maps to ITSELF under gamma -> mu^{b-a} gamma.  Hence the bad-gamma
    (explainable) set is CLOSED under the cyclic group <mu^{b-a}> (badSet_orbit_closed).
    => the incidence set is a union of FULL <mu^{b-a}>-orbits: large & aligned.
  - NON-MONOMIAL direction f (>=2 terms): f o D_mu = sum mu^{e_j} c_j x^{e_j} is NOT a scalar
    multiple of f (eigen_forces_monomial), so dilation maps the line to a DIFFERENT direction.
    The bad-gamma set is NOT invariant under any single reparametrization gamma->lambda*gamma.

THIS PROBE measures, EXACTLY (no codeword enumeration, per-witness affine-in-gamma <=1 gamma):
  (1) For the binding monomial: is bad-gamma set invariant under gamma -> mu^{b-a} gamma?  (expect YES)
      and what is the orbit size of <mu^{b-a}>?  (=> incidence is a multiple of orbit size)
  (2) For non-monomial directions: for the SAME dilation lambda=mu^{b1-a} (or any lambda), is the
      bad-gamma set invariant?  (expect NO, generically) and is the incidence STRICTLY SMALLER?

p-independence checked across multiple primes with differing v2(p-1).
"""
import sys, itertools
sys.path.insert(0, 'scripts/probes')
from probe_farline_incidence_exact import find_prime_cong1, left_null
from prize_workspace import get_W


def precompute_nulls(S, p, k, size):
    n = len(S)
    nulls = []
    for R in itertools.combinations(range(n), size):
        V = [[pow(int(S[i]), j, p) for j in range(k)] for i in R]
        P = left_null(V, p)
        if P:
            nulls.append((R, P))
    return nulls


def badset(u0, u1, nulls, p):
    """Return the SET of bad gammas (explainable scalars), exact, <=1 per witness."""
    good = set()
    for R, P in nulls:
        sz = len(R)
        pa = [sum(P[t][ii] * u0[R[ii]] for ii in range(sz)) % p for t in range(len(P))]
        pb = [sum(P[t][ii] * u1[R[ii]] for ii in range(sz)) % p for t in range(len(P))]
        if not any(pb):
            if not any(pa):
                return None  # heavy witness => all gammas
            continue
        i = next(j for j in range(len(pb)) if pb[j])
        g = (-pa[i] * pow(pb[i], p - 2, p)) % p
        if all((pa[t] + g * pb[t]) % p == 0 for t in range(len(pb))):
            good.add(g)
    return good


def mono(b, S, p):
    return [pow(int(x), b, p) for x in S]


def find_generator(S, p, n):
    """Find mu in S with multiplicative order exactly n (a generator of mu_n)."""
    for mu in S:
        m = int(mu) % p
        if m == 1:
            continue
        o = 1
        cur = m
        while cur != 1:
            cur = (cur * m) % p
            o += 1
            if o > n:
                break
        if o == n:
            return m
    return None


def v2(p):
    t = p - 1; c = 0
    while t % 2 == 0:
        t //= 2; c += 1
    return c


def is_orbit_closed(bs, lam, p):
    """Is the bad-gamma set bs invariant under gamma -> lam*gamma (excluding gamma=0 fixed pt)?"""
    if bs is None:
        return True
    return all(((g * lam) % p) in bs for g in bs)


def orbit_size(lam, p):
    o = 1; cur = lam % p
    while cur != 1:
        cur = (cur * lam) % p; o += 1
        if o > p:
            return -1
    return o


def analyze(n, k, size, primes):
    print(f"\n{'='*70}\n n={n} k={k} (rho={k/n}) size={size} (s-k={size-k}) r={n-size} delta={(n-size)/n:.4f}\n{'='*70}", flush=True)
    for plo in primes:
        p = find_prime_cong1(n, plo); S = list(get_W(n, p).S)
        mu = find_generator(S, p, n)
        nulls = precompute_nulls(S, p, k, size)
        print(f"\n p={p} (v2={v2(p)}, mu_n gen={mu}):", flush=True)

        # ---- (1) Best monomial direction & its orbit closure ----
        best = (-1, None, None)
        for b in range(size):            # far monomial exponents (far => b < size? we sweep low)
            for a in range(n):
                if a == b:
                    continue
                bs = badset(mono(a, S, p), mono(b, S, p), nulls, p)
                I = p if bs is None else len(bs)
                if 0 < I < p and I > best[0]:
                    best = (I, (a, b), bs)
        Imono, (a0, b0), bs0 = best
        lam = pow(mu, (b0 - a0) % n, p)        # the eigen reparametrization scalar mu^{b-a}
        osz = orbit_size(lam, p)
        closed = is_orbit_closed(bs0, lam, p)
        print(f"   MONO worst: a={a0} b={b0}  I={Imono}  | dilation lam=mu^{(b0-a0)%n}  orbit_size(<lam>)={osz}"
              f"  bad-set <lam>-CLOSED={closed}  I%orbit={Imono % osz if osz>0 else '?'}", flush=True)

        # ---- (2) Non-monomial (2-term) directions: orbit closure & incidence ----
        gen_best = -1; gen_closed_any = False; tested = 0
        viol_examples = 0
        for b1, b2 in itertools.combinations(range(size), 2):
            for c in (1, p - 1, 2):
                u1 = [(pow(int(x), b1, p) + c * pow(int(x), b2, p)) % p for x in S]
                for a in range(min(n, 8)):
                    bs = badset(mono(a, S, p), u1, nulls, p)
                    I = p if bs is None else len(bs)
                    if not (0 < I < p):
                        continue
                    tested += 1
                    if I > gen_best:
                        gen_best = I
                    # test invariance under the SAME family of dilations lam=mu^{j}
                    any_closed = False
                    for j in range(1, n):
                        lj = pow(mu, j, p)
                        if orbit_size(lj, p) > 1 and is_orbit_closed(bs, lj, p) and len(bs) > 1:
                            any_closed = True; break
                    if any_closed:
                        gen_closed_any = True
                    else:
                        viol_examples += 1
        verdict = "BEATS" if gen_best > Imono else ("ties" if gen_best == Imono else "UNDER")
        print(f"   GEN2 best I={gen_best} ({verdict} mono)  | any 2-term bad-set nontrivially orbit-closed (|bs|>1): "
              f"{gen_closed_any}  (of {tested} far 2-term dirs; {viol_examples} NOT orbit-closed)", flush=True)


if __name__ == '__main__':
    # n=16,k=4 binding (size=6, r=10) FULL — the established binding radius.
    analyze(16, 4, 6, [200003, 786433, 16777259])
    # also the n=16 Johnson rung size=8 (r=8) for contrast
    analyze(16, 4, 8, [200003])
    print("\nDONE")
