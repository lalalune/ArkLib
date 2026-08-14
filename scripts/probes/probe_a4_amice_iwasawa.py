# A4 [amice-iwasawa]: does the dilation-tower period interpolate to a p-adic measure with
# bounded Iwasawa mu/lambda invariants, and does that bound the ARCHIMEDEAN sup M(mu_n)?
#
# Period: f(b) = sum_{x in mu_n} e_p(bx),  e_p(z) = exp(2*pi*i*z/p).  Recursion f_{i+1}(b)=f_i(b)+f_i(zeta b).
#
# THE A4 LEMMA (precise form being tested):
#   Along the dilation tower the values { f(b_0 * zeta^j) : j } are samples of a function
#   F: Z_2 -> C_p (after Dwork twist e_p -> Teichmuller/Dwork pi) which is a p-adic MEASURE
#   (continuous => Amice transform A_F(T) entire of finite order with bounded mu,lambda).
#   IF bounded, the p-adic-analytic norm gives |f(b)| <= sqrt(2 n log(p/n)).
#
# TWO honest horns to separate:
#  HORN 1 (p-adic norm is trivial): in C_p the period's p-adic absolute value |f(b)|_p is determined
#     by 2-adic/p-adic valuation, and is ALREADY small (often a unit or v_p-graded) -- but this says
#     NOTHING about the archimedean |f(b)|_inf. => reduces-to-magnitude (the known obstruction).
#  HORN 2 (Mahler/Amice interpolation): does j -> f(b_0 zeta^j) extend 2-adic-continuously? Measure
#     Mahler coefficient decay a_k = sum_{j} (-1)^{k-j} C(k,j) f(b_0 zeta^j). For a MEASURE we need
#     |a_k|_p bounded (Amice: measure <=> bounded Mahler coeffs). lambda-invariant = #(roots of A_F).
#
# Decisive test: compute BOTH the 2-adic interpolation data (Mahler coeffs of the period along the
# dilation orbit) AND track whether ANY function of that 2-adic data tracks the archimedean sup.
# If the 2-adic data is bounded (measure exists) but uncorrelated with arch sup -> reduces-to-magnitude.

import math, cmath
import numpy as np

def isprime(x):
    if x<2: return False
    for q in [2,3,5,7,11,13,17,19,23,29,31,37]:
        if x%q==0: return x==q
    d=x-1; s=0
    while d%2==0: d//=2; s+=1
    for a in [2,3,5,7,11,13,17,19,23,29,31,37]:
        y=pow(a,d,x)
        if y in (1,x-1): continue
        ok=False
        for _ in range(s-1):
            y=y*y%x
            if y==x-1: ok=True; break
        if not ok: return False
    return True

def fac(x):
    f=set(); d=2
    while d*d<=x:
        while x%d==0: f.add(d); x//=d
        d+=1
    if x>1: f.add(x)
    return f

def proot(p):
    fs=fac(p-1)
    for g in range(2,p):
        if all(pow(g,(p-1)//q,p)!=1 for q in fs): return g

def find_prime(n, beta):
    # prize-shaped: p PRIME, p > n^beta, n | p-1, p NOT n+1 (proper subgroup, p-1 > n*log scale)
    target = n**beta
    p = target | 1
    while True:
        if isprime(p) and (p-1)%n==0 and (p-1)//n > 1:
            return p
        p += 2

def vp(x, p):
    # p-adic valuation of an integer x
    if x==0: return 10**9
    v=0
    while x%p==0: x//=p; v+=1
    return v

# ---- Build mu_n and the period f(b) over F_p (archimedean) ----
def setup(n, p):
    g = proot(p)
    h = pow(g, (p-1)//n, p)          # generator of mu_n
    mu = [pow(h, i, p) for i in range(n)]
    # dilation by zeta = primitive n-th root: zeta = h itself acts as multiplication mod p mapping mu_n->mu_n.
    # The tower dilation b->zeta b uses zeta a 2-power root; here we use multiplication by h (order n=2^k).
    zeta = h
    return g, h, mu, zeta

def period(b, mu, p):
    return sum(cmath.exp(2j*math.pi*((b*x)%p)/p) for x in mu)

print("="*100)
print("A4 amice-iwasawa: 2-adic interpolation of the dilation-tower period vs archimedean sup")
print("="*100)

for (n, beta) in [(8,4),(16,4),(8,5),(16,5),(32,4)]:
    p = find_prime(n, beta)
    g,h,mu,zeta = setup(n, p)
    lnpn = math.log(p/n)
    floor = math.sqrt(n*lnpn)

    # archimedean sup over ALL b!=0
    sups = []
    for b in range(1, p):
        sups.append(abs(period(b, mu, p)))
    March = max(sups)
    bstar = 1 + int(np.argmax(sups))

    print(f"\n n={n} beta={beta} p={p} (ln(p/n)={lnpn:.2f})  M_arch={March:.4f}  floor=sqrt(n ln)={floor:.4f}  ratio={March/floor:.4f}")

    # ---- HORN 2: the dilation orbit of the WORST b (b -> zeta b -> zeta^2 b ... order n) ----
    # values along the orbit; for a 2-adic MEASURE we'd interpolate j in Z_2 by f(b* zeta^j).
    orbit_b = [(bstar * pow(zeta, j, p)) % p for j in range(n)]
    fvals = [period(bb, mu, p) for bb in orbit_b]   # complex (archimedean) period along orbit
    arch_orbit = [abs(v) for v in fvals]

    # Mahler/finite-difference coefficients of the ARCHIMEDEAN sequence (this is the candidate "measure")
    # a_k = sum_{j=0}^{k} (-1)^{k-j} C(k,j) f(orbit_j)
    # For a 2-adic measure we need these to be 2-adically bounded; archimedean magnitude is irrelevant to that.
    # We report archimedean |a_k| (does it blow up = NOT entire of finite arch order) AND the fact that
    # the period is an algebraic integer in Z[zeta_p] so its 2-adic structure is governed by mod-2 reduction.
    a = []
    for k in range(min(n, 12)):
        s = 0
        for j in range(k+1):
            s += ((-1)**(k-j)) * math.comb(k,j) * fvals[j]
        a.append(s)
    mahler_arch = [abs(v) for v in a]
    print(f"   dilation orbit arch |f|: min={min(arch_orbit):.3f} max={max(arch_orbit):.3f}  (M_arch is attained on orbit: {abs(max(arch_orbit)-March)<1e-6})")
    print(f"   Mahler |a_k| (arch) k=0..{len(a)-1}: " + " ".join(f"{v:.2f}" for v in mahler_arch))

    # ---- HORN 1: the genuine p-adic side. The period f(b) = sum_{x in mu_n} zeta_p^{bx}, zeta_p a p-th
    # root of unity, is an algebraic integer in Z[zeta_p]. Its p-adic valuation (via the prime above p,
    # where zeta_p - 1 is the uniformizer, v(zeta_p -1)=1/(p-1)) is the genuine 2-adic/p-adic datum.
    # The norm to Q of (f(b)) is an integer; v_p of that norm is the genuine p-adic invariant.
    # Compute exact integer: N(b) = f(b)*conj-products... too big. Instead compute the algebraic-integer
    # mod small primes to get the 2-adic Newton-polygon-ish datum.
    # Cheap surrogate: the period reduces mod the prime (zeta_p-1) to n mod p (since each zeta_p^{bx}=1).
    # So f(b) ≡ n (mod (zeta_p -1)) for EVERY b -> p-adic size of f(b) is GENERICALLY a unit times n.
    # This is exactly horn 1: the p-adic norm is ~ constant (=n, independent of b) => CANNOT separate worst b.
    print(f"   HORN 1 check: f(b) ≡ n = {n} (mod (zeta_p-1)) for all b (p-adic leading term b-INDEPENDENT) => p-adic size cannot distinguish worst b")

print("\n" + "="*100)
print("SUMMARY DIAGNOSIS printed inline; the load-bearing question: does ANY 2-adic-bounded functional")
print("of the orbit track M_arch, or is the p-adic leading term b-independent (=n) -> reduces-to-magnitude.")
print("="*100)
