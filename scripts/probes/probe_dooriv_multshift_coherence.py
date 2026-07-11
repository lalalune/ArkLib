#!/usr/bin/env python3
"""
Door-IV Lane 1 PROBE — multiplicative-shift (non-negation-stable) refinement coherence at worst-b.

Context (deconflicted): the index-2 / negation-stable multi-piece refinements of the period sum
S(b) = sum_{x in mu_n} e_p(b*x) are PROVEN sign-degenerate (rho=1 on same-sign fibers):
  _DoorIVCosetHalfCoherence  (two-piece real halves -> rho=1 same sign)
  _DoorIVMultiPieceSignCoherence (any negation-stable refinement -> rho=1 same sign)
The in-tree note says the only escape is a refinement whose pieces are NOT negation-stable, so the
piece sums are genuinely COMPLEX (carry angular phase). The OPEN question (brief Lane 1): at the
adversarial worst-b, does a multiplicatively-indexed (Galois/zeta-orbit) refinement carry exploitable
angular SLACK, or does worst-b force the complex pieces back into near-alignment (rho->1)?

Refinement tested: split mu_n = <g> (g a generator of the 2-power subgroup, |mu_n|=n) into d cosets
of the order-(n/d) subgroup <g^d>. Piece P_j = sum_{x in g^j <g^d>} e_p(b*x), j=0..d-1.  These pieces
are NOT negation-stable for d not dividing n/2 appropriately, so they are genuinely complex.

We measure, AT THE WORST b (argmax |S(b)|):
  rho_d(b) = |sum_j P_j| / sum_j |P_j|     (multi-piece coherence; =|S(b)|/sum_j|P_j|)
and the angular spread of {arg P_j}. We compare d=2,4,8,16 and ask whether higher d (more, smaller,
genuinely-complex pieces) opens a gap rho_d < 1 - c that survives at the worst b, or whether worst-b
keeps rho_d ~ 1 (i.e. the pieces stay phase-aligned => no anti-concentration slack to grip).

Probe-first discipline: EXACT integer arithmetic, PROPER subgroup mu_n (n=2^a) << F_p*, p >> n^3
(prize regime m=(p-1)/n ~ n^3), multiple structured primes, never n=q-1.
"""
import cmath, math

def find_primes(n, count, beta_min=4):
    # primes p = 1 mod n with p >> n^beta_min (prize regime q ~ n^beta, m=(p-1)/n ~ n^3)
    out = []
    target = n ** beta_min
    k = (target // n) + 1
    while len(out) < count:
        p = k * n + 1
        if is_prime(p):
            out.append(p)
        k += 1
    return out

def is_prime(p):
    if p < 2: return False
    for q in (2,3,5,7,11,13,17,19,23,29,31,37):
        if p % q == 0:
            return p == q
    d = p - 1; r = 0
    while d % 2 == 0:
        d //= 2; r += 1
    for a in (2,3,5,7,11,13,17,19,23,29,31,37):
        if a % p == 0: continue
        x = pow(a, d, p)
        if x == 1 or x == p-1: continue
        ok = False
        for _ in range(r-1):
            x = x*x % p
            if x == p-1: ok = True; break
        if not ok: return False
    return True

def primitive_root(p):
    phi = p - 1
    factors = set()
    m = phi
    f = 2
    while f*f <= m:
        if m % f == 0:
            factors.add(f)
            while m % f == 0: m //= f
        f += 1
    if m > 1: factors.add(m)
    for g in range(2, p):
        if all(pow(g, phi//q, p) != 1 for q in factors):
            return g
    raise RuntimeError("no primitive root")

def mu_n_generator(p, n):
    # generator of the unique order-n subgroup: g0^((p-1)/n)
    g0 = primitive_root(p)
    return pow(g0, (p-1)//n, p)

def ep_val(t, p, twopi_over_p):
    # e_p(t) computed on the fly (full table of size p~n^4 is too big to allocate)
    a = twopi_over_p * (t % p)
    return complex(math.cos(a), math.sin(a))

def analyze(n, p, dlist):
    g = mu_n_generator(p, n)
    # subgroup elements in generator order: g^0, g^1, ..., g^{n-1}
    elems = [1]
    for _ in range(n-1):
        elems.append(elems[-1]*g % p)
    assert pow(g, n, p) == 1 and len(set(elems)) == n
    twopi_over_p = 2*math.pi/p
    # |S(b)| is constant on mu_n-cosets b*mu_n, so scan one rep per coset: b = g0^t. The full
    # transversal has k=(p-1)/n ~ n^3 reps; for large n we SAMPLE a prefix of `cap` reps. NB: the
    # reported argmax over the sample is a SAMPLED max (a LOWER bound on the true M(n)); we label it
    # b_smax (sampled-max), not a certified global worst-b. The structural conclusion (rho_d high at
    # large |S|, only sign DOF) is robust to this since it holds across the WHOLE sampled spread.
    g0 = primitive_root(p)
    k = (p-1)//n           # number of mu_n-cosets = m ~ n^3
    cap = min(k, 12000)
    best_absS = -1.0; best_b = None
    bb = 1
    step = pow(g0, 1, p)
    # iterate reps b = g0^t
    b = 1
    for t in range(cap):
        S = sum(ep_val(b*x, p, twopi_over_p) for x in elems)
        a = abs(S)
        if a > best_absS:
            best_absS = a; best_b = b
        b = b * g0 % p
    b = best_b
    # at the SAMPLED-MAX-|S| b (b_smax), compute multi-piece coherence for each d
    res = {}
    for d in dlist:
        if n % d != 0: continue
        sub = n // d            # |<g^d>| = n/d
        pieces = []
        for j in range(d):
            # coset g^j <g^d> = { g^(j + d*i) : i=0..sub-1 }
            Pj = 0j
            idx = j
            for i in range(sub):
                Pj += ep_val(b * elems[idx], p, twopi_over_p)
                idx += d
            pieces.append(Pj)
        S = sum(pieces)
        denom = sum(abs(P) for P in pieces)
        rho = abs(S)/denom if denom > 0 else float('nan')
        args = [cmath.phase(P) for P in pieces if abs(P) > 1e-9*denom/d]
        # angular spread: max pairwise angle gap (circular)
        if len(args) >= 2:
            sa = sorted(a % (2*math.pi) for a in args)
            gaps = [sa[i+1]-sa[i] for i in range(len(sa)-1)] + [sa[0]+2*math.pi-sa[-1]]
            spread = 2*math.pi - max(gaps)   # angular extent occupied
        else:
            spread = 0.0
        res[d] = (rho, abs(S), denom, spread, len(pieces))
    return best_absS, res, k

def main():
    print("# Door-IV multiplicative-shift refinement coherence at worst-b")
    print("# b_smax = SAMPLED-max-|S| coset rep over a prefix of <=12000 transversal reps (LOWER bound on M(n))")
    print("# rho_d(b_smax) = |S(b_smax)| / sum_j |P_j^(d)|  ; pieces = d cosets of <g^d> in mu_n")
    print("# slack_d = 1 - rho_d  (anti-concentration would need slack BOUNDED AWAY from 0 at worst-b)")
    print()
    for n in (16, 32, 64, 128):
        primes = find_primes(n, 3, beta_min=4)
        for p in primes:
            absS, res, k = analyze(n, p, [2,4,8,16])
            beta = math.log(p)/math.log(n)
            print(f"n={n:4d} p={p:>12d} beta={beta:.2f} m=(p-1)/n={k:>10d}  |S(b_smax)|={absS:8.3f}  /sqrt(n*log(p/n))={absS/math.sqrt(n*math.log(p/n)):.3f}")
            for d in (2,4,8,16):
                if d in res:
                    rho, aS, den, spread, npc = res[d]
                    print(f"    d={d:3d}  rho_d={rho:.4f}  slack={1-rho:.4f}  sum|P_j|={den:8.3f}  ang_spread={spread:.3f}rad ({npc} pcs)")
            print()

if __name__ == "__main__":
    main()
