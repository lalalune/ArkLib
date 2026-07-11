#!/usr/bin/env python3
"""
ANGLE B: decompose the over-det far-line incidence  I = D  into  #orbits * orbit_size.

Crossing law (OrbitCountCrossingLaw.lean):  I_pencil = z + S * O   where
  z = [gamma=0 in B]  (fixed point, 0 or 1),
  S = orbit size = n / gcd(b-a, n),
  O = #orbits (the distinct nonzero gamma-orbits).
The budget test  I <= n  is equivalent (off fixed point)  to  O <= gcd(b-a,n) = d.

This probe extracts O EXPLICITLY at each radius s, for the binding direction, and asks:
  - is O bounded / poly / O(1) at the binding radius (-> window delta*)?
  - or does O grow (-> reduces to the wall)?
  - and CRITICALLY: does the O-bound say anything BEYOND m* ~ n/4 growth law,
    or is "O <= d" the SAME content (because d and m* are tied)?

We report, per s: D (total incidence), the binding direction (a,b), d=gcd(b-a,n),
S=n/d (orbit size), O = #distinct-nonzero-gamma-orbits, z, and the reconstruction D = z + S*O.
We ALSO report O at the binding s* (first GOOD s) and just below it.
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
    best = None
    for c in range(n):
        t = tuple(sorted((i+c) % n for i in R))
        if best is None or t < best: best = t
    return best

def gamma_for_R(R, S, p, k, a, b, prec, Vrows):
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

def decompose_dir(S, h, p, k, a, b, s, prec, Vrows):
    """Return (D, O, z, orbsize, gammas_set). D = total distinct gammas; O = #nonzero orbits;
    z = 1 if 0 is a bad gamma else 0; orbsize = n/gcd(b-a,n)."""
    n = len(S)
    seen_classes = set()
    gammas = set()
    heavy = False
    fac = pow(h, (b - a) % n, p)
    for R in itertools.combinations(range(n), s):
        cR = canon_shift(R, n)
        if cR in seen_classes: continue
        seen_classes.add(cR)
        kind, g = gamma_for_R(cR, S, p, k, a, b, prec, Vrows)
        if kind == 'heavy':
            heavy = True; continue
        if kind == 'one':
            x = g
            for _ in range(n):
                gammas.add(x); x = (x * fac) % p
    if heavy:
        return (p, None, None, None, None)
    d = math.gcd((b - a) % n, n)
    orbsize = n // d
    z = 1 if 0 in gammas else 0
    nonzero = gammas - {0}
    # group nonzero gammas into orbits under <fac>
    orbits = set()
    visited = set()
    for g in nonzero:
        if g in visited: continue
        orb = []
        x = g
        for _ in range(n):
            if x in nonzero and x not in visited:
                visited.add(x); orb.append(x)
            x = (x * fac) % p
        if orb:
            orbits.add(min(orb))
    O = len(orbits)
    return (len(gammas), O, z, orbsize, gammas)

def run(n, k, p, budget, s_lo, s_hi, blist, alist=None):
    S, h = subgroup_ordered(p, n)
    prec = {e: [pow(x, e, p) for x in S] for e in range(n)}
    Vrows = {i: [pow(S[i], j, p) for j in range(k)] for i in range(n)}
    print(f"# n={n} k={k} p={p} budget(=n)={budget}")
    print(f"# {'s':>3} {'m':>3} | {'D':>6} {'binder':>9} {'d':>3} {'S':>4} {'O':>5} {'z':>2} | D=z+S*O? | O<=d? | GOOD?")
    rows = []
    if alist is None:
        alist = list(range(n))
    for s in range(s_lo, s_hi+1):
        best = (-1, None, None, None, None, None)
        for b in blist:
            if b >= s: continue
            for a in alist:
                if a == b: continue
                D, O, z, orbsize, gammas = decompose_dir(S, h, p, k, a, b, s, prec, Vrows)
                if D > best[0]:
                    best = (D, (a,b), O, z, orbsize, gammas)
        D, binder, O, z, orbsize, gammas = best
        a,b = binder; d = math.gcd((b-a)%n, n)
        recon = (z + orbsize*O) if O is not None else None
        ok = (recon == D) if recon is not None else "HEAVY"
        odle = (O <= d) if O is not None else "-"
        good = D <= budget
        print(f"  {s:>3} {s-k:>3} | {D:>6} {str(binder):>9} {d:>3} {orbsize:>4} "
              f"{str(O):>5} {str(z):>2} | {str(ok):>6} | {str(odle):>5} | {'GOOD' if good else 'bad'}", flush=True)
        rows.append((s, s-k, D, binder, d, orbsize, O, z, good))
    # report binding
    first_good = next((r for r in rows if r[8]), None)
    if first_good:
        s_star = first_good[0]
        below = next((r for r in rows if r[0]==s_star-1), None)
        print(f"\n# BINDING: s*={s_star} (m*={s_star-k}={(s_star-k)}), n/4={n//4}")
        print(f"#   at s* : O={first_good[6]} d={first_good[4]} (O<=d: {first_good[6]<=first_good[4] if first_good[6] is not None else 'HEAVY'})")
        if below:
            print(f"#   at s*-1: O={below[6]} d={below[4]} D={below[2]} (the LAST bad row)")
    return rows

if __name__ == '__main__':
    n = int(sys.argv[1]); k = int(sys.argv[2]) if len(sys.argv)>2 else n//4
    s_lo = int(sys.argv[3]) if len(sys.argv)>3 else k+1
    s_hi = int(sys.argv[4]) if len(sys.argv)>4 else n-k+1
    blist = [int(x) for x in sys.argv[5].split(',')] if len(sys.argv)>5 else list(range(k, k+4))
    p = fp(n, 200003)
    run(n, k, p, n, s_lo, s_hi, blist)
