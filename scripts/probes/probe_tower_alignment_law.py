#!/usr/bin/env python3
"""Probe (#407): the TOWER-ALIGNMENT LAW at the true maximizer (prize regime).

Exact recursion (derived):  F_mu(t) = F_{mu-1}(t) + F_{mu-1}(t * eta_mu),
where F_mu(t) = sum_{x in mu_{2^mu}} e_p(t x),  eta_mu = primitive 2^mu-th root,
and mu_{2^{mu-1}} = (mu_{2^mu})^2 (the squares).  F_0(t) = e_p(t).

Trivial bound: B_M <= 2 B_{M-1}  =>  B_M <= n  (NO cancellation).
Conjecture  : B_M ~ C*sqrt(n*log(p/n))  requires the two halves to be
              ORTHOGONAL (Pythagorean, sqrt(2)/level) at MOST levels, with
              constructive ALIGNMENT only at ~log(p/n) top levels.

This probe finds the TRUE coset-maximizer b* (exact scan, chunked) in the
prize regime (proper subgroup, large prime, n ~ p^{1/4}) and traces the tower
DOWN from b*, reporting at each level mu the alignment cos-angle between the
two child half-sums and the magnitude-growth factor |F_mu|/|F_{mu-1}|.

PRE-REGISTERED QUESTIONS:
 (Q1) B / sqrt(n*log(p/n)) -- bounded constant across n?  (law test)
 (Q2) #ALIGNED levels (cos > 0.7) along the maximizer path -- does it grow
      like log(p/n) = (beta-1) log2(n), or like M = log2(n) (=> refutation)?
 (Q3) growth factor per level: ~sqrt(2) (orthogonal) generically, ~2 (aligned)
      only near the top?
"""
import sys, math, cmath
import numpy as np


def is_prime(n):
    if n < 2: return False
    for p in (2,3,5,7,11,13,17,19,23,29,31,37):
        if n % p == 0: return n == p
    d = n-1; r = 0
    while d % 2 == 0: d//=2; r+=1
    for a in (2,3,5,7,11,13,17,19,23,29,31,37):
        x = pow(a,d,n)
        if x in (1,n-1): continue
        for _ in range(r-1):
            x = x*x % n
            if x == n-1: break
        else: return False
    return True


def find_prime(n, beta_target):
    """smallest prime p ~ n^beta_target with n | p-1."""
    base = int(round(n ** beta_target))
    base -= base % n
    base += 1            # p == 1 mod n
    p = base
    while not is_prime(p):
        p += n
    return p


def primitive_root(p):
    """a generator of F_p^*."""
    if p == 2: return 1
    phi = p-1
    facs = []
    m = phi; d = 2
    while d*d <= m:
        if m % d == 0:
            facs.append(d)
            while m % d == 0: m//=d
        d += 1
    if m > 1: facs.append(m)
    for g in range(2, p):
        if all(pow(g, phi//q, p) != 1 for q in facs):
            return g
    raise RuntimeError


def subgroup(p, n):
    """mu_n = <eta>, eta = primitive n-th root; return sorted-by-exponent list."""
    g = primitive_root(p)
    eta = pow(g, (p-1)//n, p)
    xs = [1]
    for _ in range(n-1):
        xs.append(xs[-1]*eta % p)
    assert pow(eta, n, p) == 1 and pow(eta, n//2, p) != 1
    assert len(set(xs)) == n
    return g, eta, xs


def find_maximizer(p, n, xs):
    """exact: max over the (p-1)/n cosets of |sum_{x in mu_n} e_p(c x)|.
    coset reps = g^j, j = 0 .. (p-1)/n - 1.  Chunked numpy."""
    g = primitive_root(p)
    ncos = (p-1)//n
    xs_arr = np.array(xs, dtype=np.int64)
    two_pi_over_p = 2.0*math.pi/p
    best = -1.0; best_c = None
    # coset reps c = g^j ; iterate via running product in chunks
    CH = max(1, min(10_000_000 // n, ncos))
    c = 1  # g^0
    g_pow_CH = pow(g, CH, p)
    j = 0
    # we need the actual c values; build chunk reps by repeated *g mod p
    reps = np.empty(CH, dtype=np.int64)
    while j < ncos:
        m = min(CH, ncos - j)
        # fill reps[0:m] = c*g^0 .. c*g^{m-1}
        cc = c
        for i in range(m):
            reps[i] = cc
            cc = cc*g % p
        R = reps[:m]
        # phases: outer (m x n) of R*xs mod p  -> angle -> sum exp
        prod = (R[:,None] * xs_arr[None,:]) % p            # int64 m x n
        ang = prod.astype(np.float64) * two_pi_over_p
        S = np.cos(ang).sum(axis=1) + 1j*np.sin(ang).sum(axis=1)
        mags = np.abs(S)
        idx = int(np.argmax(mags))
        if mags[idx] > best:
            best = float(mags[idx]); best_c = int(R[idx])
        # advance c by g^m
        c = c * pow(g, m, p) % p
        j += m
    return best, best_c


def F_mu(t, p, eta_top, n):
    """F over mu_{2^mu} where mu_{2^mu} = <eta>, eta of order 2^mu; here we pass
    the full subgroup; for sub-levels we slice the squares."""
    pass


def tower_trace(p, n, xs, bstar):
    """Trace the recursion from the TOP subgroup down to level 1 at t=bstar.
    At level mu, mu_{2^mu} = {xs[i] : i in step*range}, step = n // 2^mu.
    F_mu(t) = sum over those.  Child halves at level mu->mu-1:
       even-index squares = F_{mu-1}(t),  odd = F_{mu-1}(t*eta_mu) shape.
    We instead directly compute, for each level, the two half-sums and their
    alignment, by the recursion F_mu(t)=A+B with
       A = sum_{x in squares} e_p(t x),  B = sum_{x in nonsquares} e_p(t x)."""
    t = bstar
    twp = 2.0*math.pi/p
    def esum(elts):
        a = np.array(elts, dtype=np.int64)
        ang = ((t*a) % p).astype(np.float64)*twp
        return complex(np.cos(ang).sum(), np.sin(ang).sum())
    M = int(round(math.log2(n)))
    rows = []
    # level mu uses subgroup mu_{2^mu} = elements xs[i] with i multiple of n//2^mu
    for mu in range(M, 0, -1):
        size = 1 << mu
        step = n // size
        elts = [xs[i*step] for i in range(size)]   # mu_{2^mu} = <eta^step>
        # split into squares (even idx in this subgroup's own ordering) and nonsquares
        squares = elts[0::2]      # = mu_{2^{mu-1}}
        nonsq   = elts[1::2]      # = eta_mu * mu_{2^{mu-1}}
        A = esum(squares); B = esum(nonsq); Fmu = A+B
        # alignment cos between A and B
        if abs(A) > 1e-12 and abs(B) > 1e-12:
            cosang = (A.real*B.real + A.imag*B.imag)/(abs(A)*abs(B))
        else:
            cosang = float('nan')
        rows.append((mu, abs(Fmu), abs(A), abs(B), cosang))
    return rows


def main():
    print("="*92)
    print("TOWER-ALIGNMENT LAW probe (#407) -- true maximizer, prize regime n ~ p^{1/4}")
    print("="*92)
    beta = 4.0
    configs = [(16, 4.0), (32, 4.0), (64, 4.0), (128, 4.0), (256, 4.0)]
    print(f"\n{'n':>5} {'p':>14} {'p/n':>12} {'B':>9} {'sqrtN':>8} "
          f"{'sqrt(NlogP/n)':>14} {'B/sqrtN':>9} {'B/sqrt(Nlog)':>13} {'#align':>7} {'M':>4}")
    summary = []
    for n, b in configs:
        p = find_prime(n, b)
        g, eta, xs = subgroup(p, n)
        B, bstar = find_maximizer(p, n, xs)
        sqrtN = math.sqrt(n)
        logfac = math.log(p/n)
        sqrtNlog = math.sqrt(n*logfac)
        rows = tower_trace(p, n, xs, bstar)
        M = int(round(math.log2(n)))
        naligned = sum(1 for (_,_,_,_,c) in rows if (c==c and c > 0.7))
        print(f"{n:>5} {p:>14} {p//n:>12} {B:>9.2f} {sqrtN:>8.2f} "
              f"{sqrtNlog:>14.2f} {B/sqrtN:>9.3f} {B/sqrtNlog:>13.3f} {naligned:>7} {M:>4}")
        summary.append((n, p, B, sqrtN, sqrtNlog, rows, M, naligned, bstar))

    print("\n" + "="*92)
    print("PER-LEVEL TOWER TRACE at the maximizer b*  (mu: |F_mu|  |A| |B|  cos(A,B))")
    print("  cos~+1 => constructive ALIGNMENT (factor up to 2);  cos~0 => ORTHOGONAL (factor sqrt2)")
    print("="*92)
    for (n,p,B,sqrtN,sqrtNlog,rows,M,naligned,bstar) in summary:
        print(f"\nn={n}, p={p}, b*={bstar}, B={B:.2f}, sqrt(n)={sqrtN:.2f}")
        prev = None
        for (mu, Fmu, A, Bv, cosang) in rows:
            growth = (Fmu/prev) if prev else float('nan')
            tag = "ALIGN" if (cosang==cosang and cosang>0.7) else ("ORTHO" if cosang==cosang and abs(cosang)<0.3 else "")
            print(f"   mu={mu:>2}: |F|={Fmu:>8.2f}  |A|={A:>8.2f} |B|={Bv:>8.2f}  "
                  f"cos={cosang:>+6.3f}  growth(|F_mu|/|F_mu-1|)={growth:>5.3f} {tag}")
            prev = Fmu

    print("\n" + "="*92)
    print("READING: Q2 -- if #align ~ (beta-1)*log2(n) = log(p/n)/log2, law holds;")
    print("              if #align ~ M = log2(n) (aligned ALL levels), B ~ n => REFUTED.")
    print("="*92)
    return 0


if __name__ == "__main__":
    sys.exit(main())
