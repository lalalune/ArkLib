#!/usr/bin/env python3
"""
probe_444_worstcoset_quotient_structure.py  (#444, door-(iv) Lane 1 / Lane 3 constraint)

SHARP ADVERSARIAL FOLLOW-UP to probe_444_worstb_set_arithmetic.py.

That probe showed the near-max set W = {b!=0 : |eta_b| >= (1-tau)M} is ALWAYS exactly a union of
full mu_n-COSETS (muOrbit=True, |W|/n integer) and negation-symmetric. BUT THAT IS NOT NEW
STRUCTURE: it is FORCED by the PROVEN coset-invariance eta_{cb}=eta_b for c in mu_n (commit
9909ef905, _SpectralCosetInvariance) + eta_{-b}=conj(eta_b). So |eta_b| is literally a function
on the QUOTIENT F_p^* / mu_n  ~=  Z_m,  m=(p-1)/n.

THE ONLY PLACE EXPLOITABLE ADDITIVE STRUCTURE COULD LIVE is the worst-COSET set in Z_m:
  Wq = { j in Z_m : coset g^j has |eta| >= (1-tau)M }   (g a fixed generator of F_p^*).
A door-(iv) anti-concentration lever that is NOT moment / NOT completion would need Wq to be
additively structured IN Z_m (AP, interval, small-sumset / |Wq+Wq| small, dilate-closed),
OR the magnitude profile |eta(g^j)| over j in Z_m to be a structured (e.g. low-Fourier-complexity)
sequence a moment-free bound could grip.

We measure, at the genuine prize regime (proper thin mu_n, p>>n^3, p==1 mod n, m ODD, NEVER n=q-1):
  - |Wq| and the QUOTIENT sumset ratio |Wq+Wq|/|Wq| in Z_m.
  - longest AP in Wq (Z_m); dilation-closure of Wq under mult-by-t in Z_m^*.
  - Fourier l-infinity of the magnitude profile f(j)=|eta(g^j)| on Z_m: concentrated (structured)
    or flat (spread)?  Spread => no moment-free structural grip.
NO moment of eta, NO completion, NO Lean.
"""
import cmath, math
import numpy as np

def isprime(x):
    if x < 2: return False
    for q in (2,3,5,7,11,13,17,19,23,29,31,37,41,43,47):
        if x % q == 0: return x == q
    d = x-1; r = 0
    while d % 2 == 0: d //= 2; r += 1
    for a in (2,3,5,7,11,13,17,19,23,29,31,37):
        if a >= x: continue
        y = pow(a, d, x)
        if y == 1 or y == x-1: continue
        ok = False
        for _ in range(r-1):
            y = y*y % x
            if y == x-1: ok = True; break
        if not ok: return False
    return True

def find_prime_thin(n, beta, odd_m=True):
    target = int(n**beta); mod = n
    start = (target // mod) * mod + 1
    best = None
    for k in range(0, 2000000):
        for cand in (start + k*mod, start - k*mod):
            if cand > n and isprime(cand):
                mm = (cand-1) // n
                if (mm % 2 == 1) or (not odd_m):
                    return cand
                if best is None: best = cand
    return best

def prim_root(p):
    x = p-1; fs = set(); d = 2
    while d*d <= x:
        while x % d == 0: fs.add(d); x //= d
        d += 1
    if x > 1: fs.add(x)
    for g in range(2, p):
        if all(pow(g, (p-1)//f, p) != 1 for f in fs): return g
    return None

def longest_ap_mod(S, m):
    Sset = set(S); best = 1
    Sl = sorted(S)
    if len(Sl) < 2: return len(Sl)
    for a in Sl:
        for d in range(1, m):
            L = 1; x = (a + d) % m
            while x in Sset:
                L += 1; x = (x + d) % m
                if L > best: best = L
                if L > len(Sl): break
        if best >= len(Sl): break
    return best

def analyze(n, beta, odd_m=True):
    p = find_prime_thin(n, beta, odd_m)
    if p is None:
        print(f"  n={n} beta={beta}: no prime"); return
    m = (p-1) // n
    g = prim_root(p)
    if m * n > 8_000_000:
        print(f"  n={n} p={p} m={m}: m*n={m*n} too big, skip"); return
    w = cmath.exp(2j*math.pi/p)
    gm = pow(g, m, p)
    mu = [pow(gm, t, p) for t in range(n)]
    mag = np.empty(m)
    gj = 1
    for j in range(m):
        s = 0j
        for x in mu:
            s += w**((gj*x) % p)
        mag[j] = abs(s)
        gj = (gj*g) % p
    M = mag.max()
    odd_str = "ODD" if m % 2 == 1 else "even"
    print(f"  n={n} p={p} m={m} {odd_str} beta_eff={math.log(p,n):.2f}  M={M:.4f} M/sqrtn={M/math.sqrt(n):.3f}")
    neg_in_mu = ((p-1) in set(mu))
    for tau in (0.02, 0.05, 0.10):
        thr = (1-tau)*M
        Wq = [j for j in range(m) if mag[j] >= thr]
        kq = len(Wq)
        if kq == 0: continue
        Wset = set(Wq)
        sums = set()
        for a in Wq:
            for b in Wq:
                sums.add((a+b) % m)
        sumratio = len(sums)/kq
        ap = longest_ap_mod(Wq, m) if kq <= 4000 else -1
        dil = False
        if 1 < kq < m:
            for t in range(2, min(m, 50)):
                if math.gcd(t, m) == 1:
                    if set((t*a) % m for a in Wq) == Wset:
                        dil = True; break
        print(f"    tau={int(tau*100)}%: |Wq|={kq:4d}  fracQuot={kq/m:.4f}  |Wq+Wq|/|Wq|={sumratio:.2f}  longestAP_Zm={ap}  dilClosed={dil}  (-1 in mu_n={neg_in_mu})")
    f = mag - mag.mean()
    F = np.abs(np.fft.fft(f))
    F0 = F[1:]
    linf = F0.max()
    l2 = math.sqrt((F0**2).sum())
    top5 = sorted((F0**2).tolist(), reverse=True)[:5]
    tot = (F0**2).sum()
    print(f"    mag-profile Fourier: ||hatf||_inf/||hatf||_2 = {linf/l2:.4f}  (flat baseline ~ {1/math.sqrt(m/2):.4f}); top5-freq-mass-frac={[round(t/tot,4) for t in top5]}")

if __name__ == "__main__":
    print("=== probe_444_worstcoset_quotient_structure: is the worst-COSET set additively structured in Z_m? ===")
    for (n, beta) in [(8,4.0),(8,4.5),(8,5.0),(16,4.0),(16,4.5),(32,4.0),(64,4.0)]:
        analyze(n, beta, odd_m=True)
    print("=== done ===")
