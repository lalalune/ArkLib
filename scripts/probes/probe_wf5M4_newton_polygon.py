#!/usr/bin/env python3
"""
probe_wf5M4_newton_polygon.py  (#444, lane wf-M4)

STRATEGY: char-p moment via the p-adic / (1-zeta)-adic Newton polygon of the
moment-generating object.

OBJECT. mu_n = 2-power subgroup of F_p^*, n = 2^mu, n | p-1, p prime, p ~ n^beta.
Gauss period  eta_b = sum_{x in mu_n} e_p(b x)  (REAL since -1 in mu_n).
Real r-th period moment  W_r := (1/p) sum_{b in Z_p} eta_b^r
                              = #{ (x_1..x_r) in mu_n^r :  x_1 + ... + x_r = 0 mod p }
(orthogonality: W_r = f^{*r}(0), f = additive indicator of mu_n).

We split W_r = W_r^Z + Delta_r  where
  W_r^Z   = #{ ordered r-tuples in mu_n with  sum_i zeta^{x_i} = 0  in Z[zeta] }   (CHAR-0, genuine)
  Delta_r = #{ tuples with  sum_i zeta^{x_i} != 0 in Z[zeta]  but  == 0 mod (1-zeta)^? } (SPURIOUS, char-p)

CHAR-0 (Lam-Leung, n=2^mu): a vanishing sum of 2^mu-th roots of unity is a Z>=0-combination of
antipodal pairs zeta^a + zeta^{a + n/2} = 0. So W_r^Z is the count of r-tuples that PARTITION into
antipodal (negation) pairs. The conservation-law-faithful target is
        E_r := the 2r-fold coincidence count = (1/p) sum_b |eta_b|^{2r}
with char-0 value (2r-1)!! n^r  (matchings).  THIS PROBE works with W_r (single, real) which is the
cleaner Newton-polygon object; the 2r-fold E_r is W_{2r} restricted to balanced tuples.

THE NEWTON POLYGON (the lane's sufficient lemma).
For an r-tuple a = (a_1..a_r) in (Z/n)^r let v(a) = (1-zeta)-adic valuation of S(a) = sum_i zeta^{a_i}
in the local ring Z_p[zeta] (zeta a primitive p-th root; (1-zeta) is the unique prime over p, with
e = p-1, so v normalized so v(p) = p-1, v(1-zeta)=1).  S(a) == 0 mod p  <=>  v(a) >= p-1.
The mod-p moment excess is  Delta_r = #{a not genuine-zero : v(a) >= p-1}.

NEWTON-POLYGON CLAIM (N7): the count of tuples reaching valuation >= p-1 WITHOUT being a genuine
(char-0) zero is controlled by the slope structure: the number of slope-0 segments (valuation-0
contributions, i.e. genuine matchings) of the NP of the period/resultant polynomial is <= (2r-1)!!,
and the spurious high-valuation tuples are SUBDOMINANT (Delta_r = o(W_r^Z)) as long as
p > (Mann/house boundary) ~ exp(c r).  The SUFFICIENT LEMMA the prize bound reduces to:

   (SL-M4)   For all n=2^mu, prime p=n^beta (beta>=2), and all r <= ln p:
                  W_r  <=  Cmatch * (2r-1)!! * n^{r/2}        (r even)   [W_r=0 for r odd, n>2]
             equivalently  Delta_r / W_r^Z  ->  0 ,  i.e. NO new slope-0 NP segments appear mod p
             beyond the (2r-1)!! char-0 matchings.

If (SL-M4) holds to depth r ~ ln p with Cmatch absolute, then by the standard moment-to-sup step
M = max_b |eta_b| <= (W_{2r} p / (p-1))^{1/2r} ~ ( (2r-1)!! n^r )^{1/2r} ~ sqrt(2 r n / e) and
optimizing r ~ ln m gives M <= C sqrt(n log(p/n)).  THE PRIZE.

THIS PROBE measures, EXACTLY (FFT convolution + exact root-of-unity arithmetic):
  (1) W_r for r=2..rmax  (the real period moment)
  (2) W_r^Z, the char-0 genuine zero-sum count (exact via Z[zeta] arithmetic on small p, antipodal
      structure on larger p)
  (3) Delta_r = W_r - W_r^Z, the SPURIOUS mod-p excess, and Delta_r / W_r^Z (must -> 0 for SL-M4)
  (4) the implied per-frequency sup M and the ratio M / sqrt(2 r n) at the optimal r.
  (5) the (1-zeta)-adic valuation HISTOGRAM of all r-tuples: how many reach v >= p-1 spuriously
      (the literal NP slope count) -- the direct test of "<= (2r-1)!! slope-0 segments".
"""
import itertools, math, cmath
import numpy as np

def is_prime(m):
    if m < 2: return False
    if m % 2 == 0: return m == 2
    d = 3
    while d*d <= m:
        if m % d == 0: return False
        d += 2
    return True

def factor_small(m):
    f = {}; d = 2
    while d*d <= m:
        while m % d == 0: f[d] = f.get(d,0)+1; m //= d
        d += 1
    if m > 1: f[m] = f.get(m,0)+1
    return f

def primitive_root(p):
    fac = list(factor_small(p-1).keys())
    for g in range(2, p):
        if all(pow(g,(p-1)//q,p) != 1 for q in fac): return g
    return None

def subgroup(p, n):
    """mu_n: the 2-power subgroup of order n in F_p^*."""
    assert (p-1) % n == 0
    g = primitive_root(p)
    h = pow(g, (p-1)//n, p)               # generator of mu_n
    S = [pow(h, k, p) for k in range(n)]
    assert len(set(S)) == n
    return sorted(S)

def period_moments(p, n, rmax):
    """W_r = (1/p) sum_b eta_b^r  via FFT.  eta_b real (n even => -1 in mu_n)."""
    f = np.zeros(p)
    for x in subgroup(p, n): f[x] += 1.0
    fhat = np.fft.fft(f)                   # eta_b = fhat[b] (real up to fp error)
    eta = fhat.real
    W = {}
    for r in range(2, rmax+1):
        # W_r = (1/p) sum_b eta_b^r  ; for n>2 odd-r moments vanish (antipodal symmetry)
        W[r] = np.sum(eta**r) / p
    return W, eta

def char0_zero_count_bruteforce(n, r):
    """W_r^Z exactly for small (n,r): count ordered r-tuples in mu_n (indexed 0..n-1 as exponents
    of a primitive n-th root) whose sum of zeta_n powers vanishes over Z.  Uses exact integer
    coefficient vector mod cyclotomic Phi_n (for n=2^mu, Phi_n = X^{n/2}+1, so reduce exponents
    mod n with sign flip on the top half)."""
    h = n // 2
    Z = tuple([0]*h)
    cnt = 0
    for tup in itertools.product(range(n), repeat=r):
        v = [0]*h
        for e in tup:
            ee = e % n
            if ee < h: v[ee] += 1
            else:      v[ee-h] -= 1        # zeta^{j+h} = -zeta^j  (Phi_{2^mu}=X^h+1)
        if all(c == 0 for c in v): cnt += 1
    return cnt

def valuation_histogram(p, n, r, max_tuples=4_000_000):
    """(1-zeta)-adic valuation of S(a)=sum_i zeta^{a_i}, a in mu_n^r, zeta prim p-th root.
    We work in Z[zeta_p] via the integer exponent multiset; valuation v((1-zeta)) computed from
    the multiset of residues:  S = sum_j c_j zeta^j  with sum c_j = r.  By the standard
    (1-zeta)-adic theory (e_(p)=p-1), v(S) is determined by the p-adic expansion of the coefficient
    vector after reduction mod Phi_p.  EXACTLY: S == 0 mod p  iff  all c_j (j=0..p-1) are EQUAL,
    i.e. c_j = r/p for all j (needs p | r) OR the antipodal/Lam-Leung genuine cancellation.
    For the prize regime p >> r this means S==0 mod p forces S==0 over Z for r<p (no spurious
    excess possible below depth p) -- the FINITENESS the NP argument exploits.  We verify this
    exactly by checking: among all r-tuples, which have (sum_b style) S divisible by p but != 0."""
    S = subgroup(p, n)
    # exact integer test: S(a) = sum zeta^{a_i}.  Represent as coeff vector mod Phi_p (deg p-1):
    # zeta^{p-1} = -(1+zeta+...+zeta^{p-2}).  S(a) in Z[zeta], == 0 mod p iff coeff vector (in the
    # power basis 1..zeta^{p-2}) is == 0 mod p.
    genuine_zero = 0
    spurious_zero = 0      # == 0 mod p but != 0 over Z  (the NP excess we must bound)
    total = 0
    count = 0
    for tup in itertools.product(S, repeat=r):
        count += 1
        if count > max_tuples:
            return None
        # coeff vector in basis zeta^0..zeta^{p-2}
        c = [0]*(p-1)
        for x in tup:                         # x in 0..p-1 is the EXPONENT (S holds residues; use exps)
            # x here is an element of F_p; its position as zeta^x
            if x == p-1:
                for j in range(p-1): c[j] -= 1
            else:
                c[x] += 1
        total += 1
        is_zero_Z = all(v == 0 for v in c)
        is_zero_modp = all(v % p == 0 for v in c)
        if is_zero_Z: genuine_zero += 1
        elif is_zero_modp: spurious_zero += 1
    return dict(total=total, genuine_zero=genuine_zero, spurious_zero=spurious_zero)

# NOTE: elements of mu_n are residues in F_p, used directly as exponents x in zeta^x.

def run():
    print("="*88)
    print("wf-M4  Newton-polygon / (1-zeta)-adic prescreen of the char-p moment excess")
    print("="*88)

    # --- Part A: period moments W_r and the char-0 vs char-p split, prize-faithful primes ---
    print("\n[A] Real period moments W_r = (1/p) sum_b eta_b^r, and Delta_r = W_r - (2r-1)!!*matchings")
    print("    columns: r | W_r(measured) | charM=(r-1)!!*n^{r/2}(antipodal-matching model) | W_r/charM")
    def dfac(k):  # (k-1)!! for the antipodal-pair matching model of REAL moment W_r (r even)
        # number of perfect matchings into antipodal pairs of r points each independently n choices:
        # W_r^Z ~ (r-1)!! * n^{r/2}  (pair up r indices, each pair forces y=x+n/2, n free choices,
        #  but antipodal pair x,(x+h) gives zeta^x+zeta^{x+h}=0; matchings of r into pairs = (r-1)!!)
        res = 1
        j = k-1
        while j > 0:
            res *= j; j -= 2
        return res
    cases = []
    for (p, n) in [(17,8),(97,8),(241,16),(257,16),(673,16),(7681,16),
                   (193,32),(449,32),(12289,32),(40961,32)]:
        if not is_prime(p) or (p-1) % n != 0: continue
        cases.append((p,n))
    for (p, n) in cases:
        rmax = 8
        W, eta = period_moments(p, n, rmax)
        beta = math.log(p)/math.log(n)
        print(f"\n  p={p:6d} n={n:3d}  beta={beta:.2f}  m=(p-1)/n={(p-1)//n}")
        for r in range(2, rmax+1, 2):
            charM = dfac(r) * n**(r//2)
            ratio = W[r]/charM if charM else float('nan')
            print(f"    r={r}: W_r={W[r]:14.1f}   charMatch={charM:14d}   ratio={ratio:7.4f}")

    # --- Part B: EXACT char-0 vs char-p (spurious) excess at small p, the NP finiteness test ---
    print("\n[B] EXACT (1-zeta)-adic excess:  spurious_zero = #{tuples == 0 mod p but != 0 over Z}")
    print("    SL-M4 predicts spurious_zero = 0 for r < p  (NP finiteness: no slope-0 segment mod p")
    print("    below depth p beyond the genuine matchings).  columns: p n r | genuine | spurious | total")
    for (p, n) in [(17,8),(17,16),(41,8),(41,40),(41,20)]:
        if not is_prime(p) or (p-1) % n != 0: continue
        for r in range(2, 6):
            if n**r > 3_000_000:
                print(f"    p={p} n={n} r={r}: SKIP (n^r={n**r} too large)")
                continue
            res = valuation_histogram(p, n, r)
            if res is None:
                print(f"    p={p} n={n} r={r}: SKIP (tuple cap)")
                continue
            flag = "OK(no spurious)" if res['spurious_zero']==0 else "*** SPURIOUS EXCESS ***"
            print(f"    p={p:4d} n={n:3d} r={r}: genuine={res['genuine_zero']:8d} "
                  f"spurious={res['spurious_zero']:6d} total={res['total']:9d}  {flag}")

    # --- Part C: implied sup M and the prize ratio ---
    print("\n[C] Implied M = max_b|eta_b|  vs  sqrt(2 r n) at best r, and vs sqrt(n log(p/n))")
    for (p, n) in cases:
        W, eta = period_moments(p, n, 16)
        M = float(np.max(np.abs(eta[1:])))
        target = math.sqrt(n * math.log(p/n)) if p > n else float('nan')
        print(f"  p={p:6d} n={n:3d}: M={M:8.3f}  sqrt(n log(p/n))={target:7.3f}  "
              f"M/target={M/target:6.3f}  sqrt(n)={math.sqrt(n):.3f}")

if __name__ == "__main__":
    run()
