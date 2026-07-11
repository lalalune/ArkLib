#!/usr/bin/env python3
"""
Door-(iv) Lane 1 — arithmetic ANTI-CONCENTRATION of the additive phase set
    A_b = { (b * y) mod p : y in mu_n }    (mu_n = order-n 2-power subgroup of F_p*)

The period is eta_b = sum_{y in mu_n} e_p(b*y). |eta_b| is large iff the residues
A_b are concentrated (small-ball) on a short arc / coherent residue band mod p; it is
small iff A_b is anti-concentrated (well spread, Weyl-equidistributed) mod p.

The brief's live question: is there a small-ball / Littlewood-Offord-type spread bound
for A_b that does NOT route through multiplicative energy? Probe the ACTUAL spread of the
phase set at the WORST b, in the prize regime (PROPER mu_n, p >> n^3, multiple primes incl
Fermat-type), and ask:
  (Q1) Worst-b concentration: max over short windows [t, t+p/n) of #{A_b in window}.
       If eta is order sqrt(n*log), the worst window holds ~ ? points. Concentrated?
  (Q2) Is the SPREAD thinness-essential? Compare to random same-size additive set.
  (Q3) Does a NON-energy small-ball quantity (max single-residue gap / longest empty arc /
       window-count L-infinity) carry the sqrt-cancellation, or does it saturate (linear)?

probe-first, NEVER n=q-1, EXACT integer/complex arithmetic.
"""
import cmath, math, random

def is_prime(n):
    if n < 2: return False
    for q in (2,3,5,7,11,13,17,19,23,29,31,37):
        if n % q == 0: return n == q
    d=n-1; r=0
    while d%2==0: d//=2; r+=1
    for a in (2,3,5,7,11,13,17,19,23,29,31,37):
        x=pow(a,d,n)
        if x in (1,n-1): continue
        for _ in range(r-1):
            x=x*x%n
            if x==n-1: break
        else: return False
    return True

def find_prime_with_subgroup(n, beta, start=None):
    """Find prime p ~ n^beta with n | p-1 (so order-n subgroup exists), p prime."""
    target = int(round(n**beta))
    # need p = k*n + 1 prime, p close to target, p >> n^3 ideally
    k0 = max(2, target // n)
    for dk in range(0, 200000):
        for k in (k0+dk, k0-dk):
            if k < 2: continue
            p = k*n + 1
            if p > n and is_prime(p):
                return p
    return None

def subgroup_mu_n(p, n):
    """Return the order-n subgroup of F_p* as a list of residues."""
    # find a generator g of F_p*, then h = g^((p-1)/n) has order n
    pm1 = p-1
    # factor pm1
    f = {}
    m = pm1
    d = 2
    while d*d <= m:
        while m % d == 0:
            f[d]=f.get(d,0)+1; m//=d
        d += 1
    if m>1: f[m]=f.get(m,0)+1
    def is_gen(g):
        for q in f:
            if pow(g, pm1//q, p) == 1: return False
        return True
    g = 2
    while not is_gen(g): g += 1
    h = pow(g, pm1//n, p)
    mu = []
    cur = 1
    for _ in range(n):
        mu.append(cur); cur = cur*h % p
    assert len(set(mu))==n, "mu_n not order n"
    return mu

def eta(b, mu, p):
    s = 0j
    for y in mu:
        s += cmath.exp(2j*math.pi*((b*y)%p)/p)
    return s

def worst_b(mu, p, n):
    best=-1.0; bb=1
    # scan over coset representatives is enough (eta constant on b*mu_n) but
    # for robustness scan a healthy sample of b
    seen=set()
    cand = list(range(1, min(p, 4000)))
    if p > 4000:
        cand += [random.randrange(1,p) for _ in range(4000)]
    for b in cand:
        v=abs(eta(b,mu,p))
        if v>best: best=v; bb=b
    return bb, best

def window_concentration(A, p, w):
    """max number of points of A (residues mod p) inside any half-open arc of length w."""
    A = sorted(A)
    n = len(A)
    # circular sliding window
    ext = A + [a+p for a in A]
    best=0; j=0
    for i in range(n):
        # count points in [A[i], A[i]+w)
        while j < i+n and ext[j] < A[i]+w:
            j+=1
        best=max(best, j-i)
    return best

def longest_gap(A, p):
    A=sorted(A); n=len(A)
    g=0
    for i in range(n):
        nxt = A[(i+1)%n] + (p if i+1==n else 0)
        g=max(g, nxt-A[i])
    return g

def main():
    random.seed(12345)
    print("=== Door-iv phase-set anti-concentration probe (proper mu_n, prize regime) ===")
    print(f"{'n':>4} {'beta':>4} {'p':>10} {'worstb':>8} {'|eta|':>8} {'sqrt(n)':>8} "
          f"{'M/sqn':>7} {'win_p/n':>8} {'rand_win':>9} {'gap/(p/n)':>10}")
    for n, beta in [(16,4.0),(16,4.5),(32,4.0),(32,4.5),(64,4.0),(64,4.5),(128,4.0),
                    (16,99)]:  # 99 => Fermat 65537 special-case below
        if beta==99:
            p=65537
            if (p-1)%n: continue
        else:
            p=find_prime_with_subgroup(n,beta)
            if p is None: continue
        mu=subgroup_mu_n(p,n)
        bb,M=worst_b(mu,p,n)
        A=[(bb*y)%p for y in mu]
        w=p//n  # natural scale: if uniform, expect ~1 point per window of size p/n
        wc=window_concentration(A,p,w)
        # random control: n random distinct residues
        Arand=random.sample(range(p), n)
        wcr=window_concentration(Arand,p,w)
        lg=longest_gap(A,p)
        sqn=math.sqrt(n)
        print(f"{n:>4} {beta:>4} {p:>10} {bb:>8} {M:>8.3f} {sqn:>8.3f} "
              f"{M/sqn:>7.3f} {wc:>8} {wcr:>9} {lg/(p/n):>10.3f}")

if __name__=="__main__":
    main()
