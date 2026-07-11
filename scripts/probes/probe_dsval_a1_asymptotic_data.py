#!/usr/bin/env python3
"""
A1 ASYMPTOTIC DATA  (issue #407, single open value).

Exact char-0 WORST-DIRECTION over-determined far-line incidence delta*(n,rho) for
RS[mu_n, k=rho*n], mu_n = n-th roots of unity (n=2^a), computed over a big prime
q >> n^4 with q == 1 mod n (proper subgroup, NEVER q-1; over-det band is proven
p-independent -- we re-verify across multiple primes).

Object (faithful to FarCosetExplosion / probe_farline_incidence_exact):
  I(a,b; w) = #{ gamma in F_q : x^a + gamma*x^b agrees with SOME deg-<k poly
                on SOME w-subset of mu_n }.
  For a fixed w-subset R (|R|=w>k): the condition
      x^a|_R + gamma x^b|_R  in  RS[R,k] = col(Vandermonde_R)
  is AFFINE in gamma. Using the left null space P of the w x k Vandermonde_R:
      P x^a|_R + gamma P x^b|_R = 0.
    - if P x^b|_R = 0 and P x^a|_R = 0  -> R "saturated": ALL gamma (return q)
    - else exactly <= 1 gamma per R.
  I = q if any R saturated, else |union of single gammas| over all w-subsets.

  Worst direction: I(w) = max over k<=a<b<n of I(a,b;w)  (also report a<b general).
  delta*(n,rho) = 1 - w*/n, w* = smallest w in (k, n) with I(w) <= budget = n.
  (I is monotone non-increasing in w, so the first crossing is the sup-delta crossing.)

Speed: divided-difference RS-membership test, O(w) per subset; w* is small (~k+few),
so #subsets = C(n, w*) is tractable for n<=32 (and sampled for n=64).
"""
import itertools, sys
from math import comb, log2

def isprime(x):
    if x < 2: return False
    d = x - 1; s = 0
    while d % 2 == 0: d //= 2; s += 1
    for a in [2,3,5,7,11,13,17,19,23,29,31,37]:
        if a % x == 0: continue
        y = pow(a, d, x)
        if y in (1, x-1): continue
        ok = False
        for _ in range(s-1):
            y = y*y % x
            if y == x-1: ok = True; break
        if not ok: return False
    return True

def factor(x):
    f = {}; d = 2
    while d*d <= x:
        while x % d == 0: f[d] = f.get(d,0)+1; x //= d
        d += 1
    if x > 1: f[x] = f.get(x,0)+1
    return f

def proot(p):
    fs = set(factor(p-1))
    for g in range(2, p):
        if all(pow(g, (p-1)//q, p) != 1 for q in fs): return g

def setup(n, plo):
    """big prime q==1 mod n, q>=plo; mu = n-th roots of unity. Avoid high-v2 (Fermat-ish)."""
    p = plo + (1 - plo) % n
    if p < plo: p += n
    while True:
        if isprime(p):
            # faithfulness: avoid q-1 being an excessive power of 2 (high v2 ~ Fermat artifact);
            # require v2(q-1) not absurdly large vs n. (q==1 mod n forces v2>=log2 n; cap extra.)
            v = p - 1; v2 = 0
            while v % 2 == 0: v //= 2; v2 += 1
            if v2 <= int(log2(n)) + 4:
                g = proot(p); h = pow(g, (p-1)//n, p)
                mu = [pow(h, i, p) for i in range(n)]
                assert len(set(mu)) == n and pow(mu[1], n, p) == 1
                return p, mu
        p += n

def make_member(p, mu, k):
    inv = lambda z: pow(z, p-2, p)
    invc = {}  # cache inverses of (mu[i]-mu[j])
    def ddk(vals, idx):
        # k-th divided difference of vals over points mu[idx] (len k+1)
        vs = list(vals)
        for j in range(1, k+1):
            for i in range(k, j-1, -1):
                key = (idx[i], idx[i-j])
                d = invc.get(key)
                if d is None:
                    d = inv((mu[idx[i]] - mu[idx[i-j]]) % p); invc[key] = d
                vs[i] = (vs[i] - vs[i-1]) * d % p
        return vs[k]
    def in_RS(vals, idx):
        w = len(idx)
        if w <= k: return True
        for st in range(w - k):
            if ddk(vals[st:st+k+1], idx[st:st+k+1]) != 0: return False
        return True
    return ddk, in_RS

def incidence(a, b, n, mu, k, p, w, member, cap=None):
    """Exact I(a,b;w); returns (count, saturated_bool). count==p means saturated.

    If cap is given, returns early once |distinct gamma| > cap (count then is a lower
    bound > cap, sufficient to know the direction exceeds a budget == cap)."""
    ddk, in_RS = member
    MUa = [pow(x, a, p) for x in mu]; MUb = [pow(x, b, p) for x in mu]
    inv = lambda z: pow(z, p-2, p)
    gam = set()
    for R in itertools.combinations(range(n), w):
        idx = list(R)
        u1 = [MUb[i] for i in R]
        if in_RS(u1, idx):
            # x^b itself in RS on R -> if x^a also in, saturated
            u0 = [MUa[i] for i in R]
            if in_RS(u0, idx): return p, True
            continue
        u0 = [MUa[i] for i in R]
        # one candidate gamma from the FIRST violated k-window, then full check
        # find a window where ddk(u1)!=0
        gm = None
        for st in range(w - k):
            a1 = ddk(u1[st:st+k+1], idx[st:st+k+1])
            if a1 % p:
                a0 = ddk(u0[st:st+k+1], idx[st:st+k+1])
                gm = (-a0 * inv(a1)) % p; break
        if gm is None: continue
        if in_RS([(u0[i] + gm*u1[i]) % p for i in range(w)], idx):
            gam.add(gm)
            if cap is not None and len(gam) > cap:
                return len(gam), False
    return len(gam), False

def worst_incidence(n, mu, k, p, w, member, restrict_far=True, budget=None):
    """max over FAR directions (a,b), k<=a<b<n, of I(a,b;w). Returns (max,(a,b),nfar).

    A direction is EXCLUDED (non-far at this w) if it SATURATES: some w-subset on which
    BOTH x^a and x^b lie in RS[k] (the 'far-coset law' I=badcount holds only for far
    directions; a saturating direction is a near direction and is not part of the
    worst-case far incidence). We report n_excluded for transparency.

    If budget is given, early-exit as soon as any far direction exceeds budget
    (the w is rejected; exact max not needed -- returns the exceeding direction).
    """
    best = (-1, None)
    nfar = 0
    lo = k if restrict_far else 0
    for a in range(lo, n):
        for b in range(a+1, n):
            c, sat = incidence(a, b, n, mu, k, p, w, member, cap=budget)
            if sat:
                nfar += 1
                continue
            if c > best[0]: best = (c, (a,b))
            if budget is not None and c > budget:
                return best[0], best[1], nfar  # reject early
    return best[0], best[1], nfar

def delta_star(n, k, plo=None, budget=None, verbose=True):
    """exact delta*; scan w upward from k+1, first w with worst incidence<=budget."""
    if plo is None: plo = max(200003, 4*n*n*n*n + 7)  # q >> n^4
    if budget is None: budget = n
    p, mu = setup(n, plo)
    member = make_member(p, mu, k)
    rows = []
    wstar = None
    for w in range(k+1, n):
        mx, st, nex = worst_incidence(n, mu, k, p, w, member, budget=budget)
        rows.append((w, 1-w/n, mx, st, nex))
        if verbose:
            print(f"    w={w:>2} delta={1-w/n:.4f}  worstFarI={mx:>7}  dir={st}  "
                  f"(excluded {nex} non-far dirs)", flush=True)
        if mx >= 0 and mx <= budget:
            wstar = w; break
    ds = (1 - wstar/n) if wstar is not None else None
    return ds, wstar, p, rows

def verify_pindep(n, k, w, primes):
    """re-verify worst incidence at fixed (n,k,w) is identical across big primes."""
    out = []
    for plo in primes:
        p, mu = setup(n, plo)
        member = make_member(p, mu, k)
        mx, st, nex = worst_incidence(n, mu, k, p, w, member)
        out.append((mx, st, p))
    return out

if __name__ == '__main__':
    print("=" * 78)
    print("A1: exact char-0 worst-direction delta*(n,rho) over mu_n, budget=n, q>>n^4")
    print("=" * 78)
    table = {}
    plan = []
    # n=8,16 at rho in {1/2,1/4} (k must be integer >=1)
    for n in [8, 16, 32]:
        for denom in [2, 4, 8]:
            k = n // denom
            if k >= 1 and k < n:
                plan.append((n, k, 1/denom))
    for (n, k, rho) in plan:
        print(f"\n--- n={n} k={k} rho={rho} (mu_{n} roots of unity) ---", flush=True)
        ds, wstar, p, rows = delta_star(n, k, verbose=True)
        table[(n, rho)] = (ds, wstar, p)
        print(f"  => delta*(n={n},rho={rho}) = {ds}  (w*={wstar}, q={p})", flush=True)

    print("\n" + "=" * 78)
    print("SUMMARY TABLE  delta*(n,rho)")
    print("=" * 78)
    print(f"{'n':>4} {'rho':>6} {'delta*':>9} {'1-rho':>7} {'gap=1-rho-d*':>13} "
          f"{'gap*log2n':>10} {'gap*n':>8} {'w*':>4}")
    for (n, rho), (ds, wstar, p) in sorted(table.items()):
        if ds is None: continue
        gap = (1-rho) - ds
        print(f"{n:>4} {rho:>6.4f} {ds:>9.4f} {1-rho:>7.4f} {gap:>13.4f} "
              f"{gap*log2(n):>10.4f} {gap*n:>8.2f} {wstar:>4}")
