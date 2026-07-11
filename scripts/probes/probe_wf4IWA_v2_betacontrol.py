#!/usr/bin/env python3
"""
LANE wf4IWA (#444) — beta-CONTROLLED disentanglement of the v2(p-1) drift in the BGK floor period.

Follow-up to probe_wf4IWA_v2strat_bgkperiod.py: at n=32 the class-MEANS of M/sqrt(n) drift up with
v2 (3.30->3.84 over v2 5..13), but high-v2 primes were also the larger primes (beta confound), and
within-class scatter > across-class spread. This probe DECIDES whether the residual drift is v2 or beta:

  TEST A (fix beta band, vary v2):  collect primes p=1 mod n with beta=log_n p in a NARROW band
     [b0, b0+db], group by v2(p-1). If M/sqrt(n) class-means are flat across v2  => NOT v2-gated.
  TEST B (fix v2, vary beta):  collect primes of a SINGLE v2 class over a WIDE beta range. If
     M/sqrt(n) rises with beta  => the drift is the well-known BGK log(p)=beta*log(n) factor (the
     sup-norm grows like sqrt(2 n ln q)), i.e. a BETA effect, not v2.

The BGK prediction: M ~ sqrt(2 n ln q) = sqrt(2 n * beta * ln n), so M/sqrt(n) ~ sqrt(2 beta ln n)
depends ONLY on beta (and n), NOT on v2. This probe checks that prediction directly.

EXACT complex character sum over the order-n subgroup, vectorized numpy. mu_n thin (n=q^{1/beta}).
"""
import math, sys
import numpy as np

def isprime(x):
    if x < 2: return False
    if x % 2 == 0: return x == 2
    if x % 3 == 0: return x == 3
    d = 5
    while d*d <= x:
        if x % d == 0 or x % (d+2) == 0: return False
        d += 6
    return True

def v2(m):
    c = 0
    while m % 2 == 0:
        m //= 2; c += 1
    return c

def proot(p):
    m = p-1; fac = []; d = 2
    while d*d <= m:
        if m % d == 0:
            fac.append(d)
            while m % d == 0: m //= d
        d += 1
    if m > 1: fac.append(m)
    for g in range(2, p):
        if all(pow(g, (p-1)//f, p) != 1 for f in fac): return g

def period_stats(n, p):
    g = proot(p); h = pow(g, (p-1)//n, p)
    xs = []; cur = 1
    for _ in range(n):
        xs.append(cur); cur = (cur*h) % p
    xs = np.array(xs, dtype=np.int64)
    m = (p-1)//n
    CAP = 50000
    if m <= CAP:
        js = np.arange(m, dtype=np.int64)
    else:
        rng = np.random.default_rng(7)
        js = np.unique(np.concatenate([np.arange(2000, dtype=np.int64),
                                       rng.integers(0, m, size=CAP-2000)]))
    breps = np.array([pow(g, int(j), p) for j in js], dtype=np.int64)
    bx = (breps[:, None]*xs[None, :]) % p
    ang = (2.0*np.pi/p)*bx
    eta = np.cos(ang).sum(axis=1) + 1j*np.sin(ang).sum(axis=1)
    mag = np.abs(eta)
    return mag.max(), len(js), m

def collect(n, pred, need, pstart, pwin):
    out = []
    p = pstart - (pstart % n) + 1
    end = pstart + pwin
    while p < end and len(out) < need:
        if p > 2 and isprime(p) and (p-1) % n == 0 and pred(p):
            out.append(p)
        p += n
    return out

def test_A(n, b0, db, per_class):
    print("="*82)
    print(f"TEST A (n={n}): FIX beta in [{b0:.2f},{b0+db:.2f}], vary v2(p-1). Is M/sqrt(n) flat across v2?")
    print("="*82)
    plo = int(n**b0); phi = int(n**(b0+db))
    base = v2(n)
    byv2 = {}
    p = plo - (plo % n) + 1
    while p < phi and sum(len(v) for v in byv2.values()) < per_class*8:
        if p > 2 and isprime(p) and (p-1) % n == 0:
            c = v2(p-1)
            byv2.setdefault(c, [])
            if len(byv2[c]) < per_class:
                byv2[c].append(p)
        p += n
    sn = math.sqrt(n)
    means = {}
    for c in sorted(byv2):
        if not byv2[c]: continue
        vals = []
        for p in byv2[c]:
            mx, sm, m = period_stats(n, p)
            vals.append(mx/sn)
        means[c] = sum(vals)/len(vals)
        print(f"   v2={c:2d}: M/sqrt(n) mean={means[c]:.3f}  vals={[f'{v:.3f}' for v in vals]}")
    if len(means) >= 2:
        spread = max(means.values())-min(means.values())
        print(f"   => beta-CONTROLLED across-v2 spread = {spread:.3f}  "
              f"({'FLAT: not v2-gated' if spread < 0.25 else 'residual v2 structure - inspect'})")
    return means

def test_B(n, want_v2, betas, per):
    print("="*82)
    print(f"TEST B (n={n}): FIX v2(p-1)={want_v2}, vary beta {betas}. Does M/sqrt(n) rise with beta (BGK log factor)?")
    print("="*82)
    sn = math.sqrt(n)
    for b in betas:
        plo = int(n**b)
        ps = collect(n, lambda p: v2(p-1)==want_v2, per, plo, max(2_000_000, int(n**b)))
        if not ps:
            print(f"   beta~{b}: none"); continue
        vals = [period_stats(n, p)[0]/sn for p in ps]
        bgk = math.sqrt(2*b*math.log(n))   # sqrt(2 beta ln n) prediction for M/sqrt(n)
        print(f"   beta~{b:.1f}: M/sqrt(n) mean={sum(vals)/len(vals):.3f}  "
              f"(BGK sqrt(2 beta ln n)={bgk:.3f})  primes={ps[:3]}{'...' if len(ps)>3 else ''}")

if __name__ == '__main__':
    n = int(sys.argv[1]) if len(sys.argv) > 1 else 32
    # TEST A: narrow beta band ~ [3.2,3.35], vary v2
    test_A(n, 3.2, 0.15, per_class=4)
    # TEST B: fix a low v2 class, sweep beta
    test_B(n, v2(n)+1, [3.0, 3.5, 4.0, 4.5], per=3)
