#!/usr/bin/env python3
"""
LANE LC2 (#407) — DECISIVE v2(p-1)-gating test of delta* location.

Mission premise (from wf-LC + live [c.22:46]): floor-failure is v2(p-1)-GATED not beta-gated;
delta* a clean function of v2 and n.  The live SELF-CORRECTION [00:33:32] says this is a
beta-CONFOUND (E2(mu_n)=3n(n-1) is v2-BLIND).  This probe ADVERSARIALLY resolves it on the
ACTUAL delta*-binding object (exact far-line incidence I(a,b;r), p-independent count), not on E2.

For fixed n, k (rho), we sweep MANY primes p = 1 mod n stratified by v2(p-1).  For each p:
  - compute monomial-max binding incidence I_max(r) at each radius r (= the FarCosetExplosion count)
  - find delta*-crossing radius r* = first r where I_max crosses budget B = n (rho-budget proxy)
  - record (v2(p-1), beta=log_n p, I_max at binding r, r*).
Then test: does I_max / r* correlate with v2(p-1) at FIXED n?  (controls beta by reporting both.)

The incidence count is p-independent BY CONSTRUCTION (affine-in-gamma, no char-sum), so the ONLY
way v2 could gate delta* is if it changes WHICH directions are heavy (in_RS coincidences mod p).
We test that directly: do the heavy directions / their incidence change across v2-classes?

EXACT integer arithmetic mod p.  No sampling on the verdict (full monomial sweep).
"""
import itertools

def isprime(x):
    if x < 2: return False
    if x % 2 == 0: return x == 2
    d = 3
    while d*d <= x:
        if x % d == 0: return False
        d += 2
    return True

def v2(m):
    c = 0
    while m % 2 == 0:
        m //= 2; c += 1
    return c

def proot(p):
    # factor p-1
    m = p-1; fac = []
    d = 2
    while d*d <= m:
        if m % d == 0:
            fac.append(d)
            while m % d == 0: m //= d
        d += 1
    if m > 1: fac.append(m)
    for g in range(2, p):
        if all(pow(g, (p-1)//f, p) != 1 for f in fac):
            return g

def setup(n, p):
    g = proot(p); h = pow(g, (p-1)//n, p)
    return [pow(h, i, p) for i in range(n)]

def ddk(vals, pts, k, p):
    xs = pts[:k+1]; vs = list(vals[:k+1])
    for j in range(1, k+1):
        for i in range(k, j-1, -1):
            vs[i] = (vs[i]-vs[i-1]) * pow((xs[i]-xs[i-j]) % p, p-2, p) % p
    return vs[k]

def in_RS(vals, pts, k, p):
    s = len(pts)
    if s <= k: return True
    for st in range(s-k):
        if ddk(vals[st:st+k+1], pts[st:st+k+1], k, p) != 0: return False
    return True

def incidence(u0, u1, mu, k, p, combos):
    gam = set()
    for R in combos:
        pts = [mu[i] for i in R]; u0R = [u0[i] for i in R]; u1R = [u1[i] for i in R]
        if in_RS(u1R, pts, k, p):
            if in_RS(u0R, pts, k, p): return p
            continue
        a0 = ddk(u0R, pts, k, p); a1 = ddk(u1R, pts, k, p)
        if a1 % p == 0: continue
        g = (-a0 * pow(a1, p-2, p)) % p
        if in_RS([(u0R[i]+g*u1R[i]) % p for i in range(len(R))], pts, k, p): gam.add(g)
    return len(gam)

def mono_max_incidence(n, k, p, mu, r):
    """Max over monomial directions (a,b), a,b in [k,n), of binding incidence at radius r."""
    combos = list(itertools.combinations(range(n), n-r))
    best = 0; arg = None
    mv = {b: [pow(x, b, p) for x in mu] for b in range(k, n)}
    for a in range(k, n):
        for b in range(k, n):
            if a == b: continue
            I = incidence(mv[a], mv[b], mu, k, p, combos)
            if I < p and I > best: best = I; arg = (a, b)
    return best, arg

def primes_by_v2(n, count_per_class, target_v2_classes, pstart):
    """Collect primes p=1 mod n grouped by v2(p-1)."""
    out = {c: [] for c in target_v2_classes}
    p = pstart - (pstart % n) + 1
    while p < pstart + 4_000_000 and any(len(out[c]) < count_per_class for c in target_v2_classes):
        if p > 1 and isprime(p) and (p-1) % n == 0:
            c = v2(p-1)
            if c in out and len(out[c]) < count_per_class:
                out[c].append(p)
        p += n
    return out

def run(n, k, rho_label):
    print("="*78)
    print(f"n={n} k={k} ({rho_label})  budget B={n}")
    print("="*78)
    # binding radius: pick r so that combos are feasible and incidence is in the crossing band.
    # use the reframe's binding radius geometry: n-r = k+ (s-k>=2) ; try r near n - (k+2)..
    rlist = [n - (k+2), n - (k+1)]
    rlist = [r for r in rlist if 0 < r < n]
    # v2 classes: n=16 -> p-1 divisible by 16 so v2>=4; gather a spread.
    base_v2 = v2(n)
    classes = [base_v2, base_v2+1, base_v2+2, base_v2+3]
    byv2 = primes_by_v2(n, 3, classes, 4129)
    for r in rlist:
        print(f"\n-- binding radius r={r} (witness size s=n-r={n-r}, s-k={n-r-k}) --")
        rows = []
        for c in classes:
            for p in byv2[c]:
                mu = setup(n, p)
                I, arg = mono_max_incidence(n, k, p, mu, r)
                beta = __import__('math').log(p)/__import__('math').log(n)
                rows.append((c, p, beta, I, arg))
                print(f"   v2(p-1)={c}  p={p:8d}  beta={beta:5.2f}  I_max={I:4d}  arg={arg}  {'>B' if I>n else '<=B'}")
        # verdict: within fixed n, does I depend on v2?
        byc = {}
        for c, p, beta, I, arg in rows:
            byc.setdefault(c, []).append(I)
        vals = {c: sorted(set(v)) for c, v in byc.items()}
        allI = set(I for _,_,_,I,_ in rows)
        v2blind = len(allI) == 1
        print(f"   => distinct I across ALL v2/primes: {sorted(allI)}  "
              f"{'v2-BLIND (and p-blind): delta* NOT v2-gated' if v2blind else 'VARIES — inspect'}")
        # if it varies, is the variation explained by v2 or by something else?
        for c in classes:
            if c in vals:
                print(f"       v2={c}: I-values={vals[c]}")

if __name__ == '__main__':
    run(16, 4, "rho=1/4")
    run(16, 2, "rho=1/8 (smaller k, larger window)")
