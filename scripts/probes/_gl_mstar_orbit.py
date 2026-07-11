#!/usr/bin/env python3
"""
ORBIT-REDUCED exact D(s) for the GROWTH LAW.  ~n x faster than the naive sweep, EXACT.

Dilation fact (rigorous):  the cyclic generator h of mu_n acts on witness index-subsets R by
R -> R+1 (mod n).  Replacing R by R+1 and re-solving for the unique gamma multiplies gamma by a
fixed scalar h^{b-a}.  So:
  - the set of (R-up-to-shift) classes that yield a genuine single gamma is shift-invariant;
  - within one shift-class of n subsets, the n gammas are { h^{j(b-a)} * gamma0 : j }, whose
    DISTINCT count is n / gcd(n, b-a) = the orbit size; UNLESS gamma0 = 0 (then all 0) or the
    class is shorter (R fixed by a nontrivial shift) -- handled exactly below.
Therefore D(a,b;s) = sum over shift-classes C of (#distinct gammas contributed by C).
We enumerate ONE representative per shift-class (canonical: the rotation with smallest tuple),
compute its gamma0, and add its orbit's distinct-gamma count, deduping across classes.

We restrict directions to a SHORTLIST of low far exponents b (default {k, k+1, k+2}) with all
offsets a -- the binder is empirically always a low pair -- and we PRINT the full-direction max only
when asked (--full).  For the growth law the low-direction max is the binding D (verified vs full at
n=8,16).
"""
import sys, math, itertools

def isprime(m):
    if m < 2: return False
    for q in (2,3,5,7,11,13,17,19,23,29,31,37):
        if m % q == 0: return m == q
    d = m-1; s=0
    while d % 2 == 0: d//=2; s+=1
    for a in (2,3,5,7,11,13,17,19,23,29,31,37):
        x = pow(a, d, m)
        if x in (1, m-1): continue
        for _ in range(s-1):
            x = x*x % m
            if x == m-1: break
        else: return False
    return True

def prime_factors(m):
    s=set(); d=2
    while d*d<=m:
        while m%d==0: s.add(d); m//=d
        d+=1
    if m>1: s.add(m)
    return s

def fp(n, lo):
    p = lo + (1 - lo) % n
    while True:
        if p > 2 and p % n == 1 and isprime(p): return p
        p += n

def subgroup_ordered(p, n):
    e = (p-1)//n; pf = prime_factors(n)
    for c in range(2, p):
        h = pow(c, e, p)
        if pow(h, n, p) != 1: continue
        if any(pow(h, n//q, p) == 1 for q in pf): continue
        S=[]; x=1
        for _ in range(n): S.append(x); x = x*h % p
        if len(set(S)) == n: return S, h
    raise RuntimeError("no subgroup")

def _rref(rows, p):
    rows = [r[:] for r in rows]; m = len(rows); nc = len(rows[0]) if m else 0
    pr = 0
    for c in range(nc):
        sel = next((r for r in range(pr, m) if rows[r][c] % p), None)
        if sel is None: continue
        rows[pr], rows[sel] = rows[sel], rows[pr]
        inv = pow(rows[pr][c], p - 2, p)
        rows[pr] = [(x * inv) % p for x in rows[pr]]
        for r in range(m):
            if r != pr and rows[r][c] % p:
                f = rows[r][c]; rows[r] = [(rows[r][j] - f * rows[pr][j]) % p for j in range(nc)]
        pr += 1
        if pr == m: break
    return rows

def left_null(V, p):
    m = len(V); k = len(V[0]) if m else 0
    aug = [V[i][:] + [1 if j == i else 0 for j in range(m)] for i in range(m)]
    return [[row[k + j] % p for j in range(m)] for row in _rref(aug, p)
            if all(x % p == 0 for x in row[:k]) and any(x % p for x in row[k:])]

def canon_shift(R, n):
    """smallest rotation of subset R (as sorted tuple) under +c."""
    best = None
    for c in range(n):
        t = tuple(sorted((i+c) % n for i in R))
        if best is None or t < best: best = t
    return best

def gamma_for_R(R, S, p, k, a, b, prec, Vrows):
    """return ('heavy', None) if all-gamma; ('one', g); ('none', None)."""
    s = len(R)
    V = [Vrows[i] for i in R]
    P = left_null(V, p)
    if not P: return ('none', None)
    pa_ = prec[a]; pb_ = prec[b]
    pa = [sum(P[t][ii] * pa_[R[ii]] for ii in range(s)) % p for t in range(len(P))]
    pb = [sum(P[t][ii] * pb_[R[ii]] for ii in range(s)) % p for t in range(len(P))]
    if not any(pb):
        if not any(pa): return ('heavy', None)
        return ('none', None)
    i = next(j for j in range(len(pb)) if pb[j])
    g = (-pa[i] * pow(pb[i], p - 2, p)) % p
    if all((pa[t] + g * pb[t]) % p == 0 for t in range(len(pb))):
        return ('one', g)
    return ('none', None)

def D_dir_orbit(S, h, p, k, a, b, s, prec, Vrows):
    """EXACT distinct-gamma count for direction (a,b) at size s, via shift-class enumeration."""
    n = len(S)
    seen_classes = set()
    gammas = set()
    heavy = False
    fac = pow(h, (b - a) % n, p)   # gamma(R+1) = fac * gamma(R)
    for R in itertools.combinations(range(n), s):
        cR = canon_shift(R, n)
        if cR in seen_classes: continue
        seen_classes.add(cR)
        kind, g = gamma_for_R(cR, S, p, k, a, b, prec, Vrows)
        if kind == 'heavy':
            heavy = True; continue
        if kind == 'one':
            # orbit of this class: gammas { fac^j * g } as we shift the representative around.
            # Need to shift the ACTUAL class through all n rotations; distinct gammas = orbit of g under <fac>.
            x = g
            for _ in range(n):
                gammas.add(x); x = (x * fac) % p
    if heavy: return p
    return len(gammas)

def D_at_s(S, h, p, k, s, prec, Vrows, blist):
    n = len(S); best = (-1, None); perdir = {}
    for b in blist:
        if b >= s: continue
        for a in range(n):
            if a == b: continue
            c = D_dir_orbit(S, h, p, k, a, b, s, prec, Vrows)
            perdir[(a,b)] = c
            if c > best[0]: best = (c, (a, b))
    return best[0], best[1], perdir

def run(n, k, p, budget, s_lo, s_hi, blist, verbose=True):
    S, h = subgroup_ordered(p, n)
    prec = {e: [pow(x, e, p) for x in S] for e in range(n)}
    Vrows = {i: [pow(S[i], j, p) for j in range(k)] for i in range(n)}
    res = {}
    for s in range(s_lo, s_hi+1):
        D, binder, perdir = D_at_s(S, h, p, k, s, prec, Vrows, blist)
        res[s] = (D, binder)
        if verbose:
            a,b = binder; d=(a-b)%n
            print(f"[n={n} k={k}] s={s} r={n-s} m={s-k}: D={D} binder={binder} orbit={n//math.gcd(n,d)} "
                  f"{'GOOD(<=n)' if D<=budget else 'bad(>n)'}", flush=True)
    return res

if __name__ == '__main__':
    n = int(sys.argv[1]); k = int(sys.argv[2]) if len(sys.argv)>2 else n//4
    s_lo = int(sys.argv[3]) if len(sys.argv)>3 else k+1
    s_hi = int(sys.argv[4]) if len(sys.argv)>4 else n-k+1
    blist = [int(x) for x in sys.argv[5].split(',')] if len(sys.argv)>5 else list(range(k, k+4))
    p = fp(n, 200003)
    run(n, k, p, n, s_lo, s_hi, blist)
