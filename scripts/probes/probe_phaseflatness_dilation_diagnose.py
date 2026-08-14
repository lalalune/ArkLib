#!/usr/bin/env python3
"""
TOOL 2 NEW-ANGLE DIAGNOSIS (#444): is the strong prize-period dilation correlation D(lambda)~0.5
a GENUINE exploitable structure, or the known negation symmetry (-1 in mu_n) = same wall?

We pin down WHICH lambda carries the ~0.5 correlation and what it means:
  - eta is constant on cosets of mu_n; index coset reps by t (rep g^t), so eta_t := eta_{g^t}.
  - the multiplicative dilation lambda on t corresponds to b -> g^lambda?  No: dilation lambda
    on the EXPONENT t means coset c -> c^lambda (Frobenius-like power map on F_p^*/mu_n).
  - lambda = -1 mod m is the map c -> c^{-1} (inversion).  Since -1 in mu_n, eta_{c} relates to
    eta_{-c}=conj(eta_c).  The STRONG lambda we test against this.
KEY TEST: does the strong-lambda correlation let us BOUND max|eta| below the BGK scale?  If the
correlated lambda is an INVOLUTION pairing values eta_t = (phase) eta_{lambda t}, it only relates
values pairwise -> it does NOT reduce the MAX (a permutation of values preserves the max).  So
'strong dilation correlation' is NOT sup-norm-exploitable.  We CONFIRM this by:
  (a) identifying the strong lambda and checking lambda^2 == 1 mod m (involution = pairing only);
  (b) checking the correlation is a PHASE relation |eta_t| == |eta_{lambda t}| (max-preserving);
  (c) HD-doubling lambda=2 correlation when gcd(2,m)=1 (m odd) -> measure, expect ~ noise.
"""
import math, cmath

def is_prime(m):
    if m < 2: return False
    i = 2
    while i*i <= m:
        if m % i == 0: return False
        i += 1
    return True

def find_prime_cong1(n, lo):
    p = lo + (1 - lo) % n
    while True:
        if p > 2 and p % n == 1 and is_prime(p): return p
        p += n

def primitive_root(p):
    phi = p-1; factors=set(); nn=phi; d=2
    while d*d<=nn:
        if nn%d==0:
            factors.add(d)
            while nn%d==0: nn//=d
        d+=1
    if nn>1: factors.add(nn)
    for g in range(2,p):
        if all(pow(g,phi//f,p)!=1 for f in factors): return g

def analyze(p, n):
    g = primitive_root(p)
    H = [pow(pow(g,(p-1)//n,p), i, p) for i in range(n)]
    eta = {}
    for b in range(1, p):
        eta[b] = sum(cmath.exp(2j*math.pi*(b*x % p)/p) for x in H)
    m = (p-1)//n
    et = [eta[pow(g, t, p)] for t in range(m)]
    mags = [abs(v) for v in et]
    denom = sum(v*v for v in mags)
    # all dilation correlations
    res = []
    for lam in range(2, m):
        if math.gcd(lam, m) != 1: continue
        s = sum(et[t]*et[(lam*t)%m].conjugate() for t in range(m))
        res.append((abs(s)/denom, lam))
    res.sort(reverse=True)
    strong_val, strong_lam = res[0]
    # diagnose strong lambda
    invol = (strong_lam*strong_lam) % m == 1
    # is it max-preserving? check |eta_t| vs |eta_{lambda t}|
    mag_preserved = max(abs(mags[t] - mags[(strong_lam*t)%m]) for t in range(m))
    # HD-doubling lambda=2 (only if gcd(2,m)=1, i.e. m odd)
    d2 = None
    if math.gcd(2, m) == 1:
        s2 = sum(et[t]*et[(2*t)%m].conjugate() for t in range(m))
        d2 = abs(s2)/denom
    # negation lambda = m-1 ( = -1, inversion c->c^{-1})
    sm1 = sum(et[t]*et[((m-1)*t)%m].conjugate() for t in range(m))
    dm1 = abs(sm1)/denom
    print(f"  n={n} p={p} m={m}:")
    print(f"    strongest dilation: lambda={strong_lam}  D={strong_val:.4f}  "
          f"(m/2={m//2}, m/2+1={m//2+1})")
    print(f"      lambda^2 mod m == 1 ? {invol}  (involution => pairs values, MAX-PRESERVING)")
    print(f"      |eta_t| vs |eta_(lambda t)| max abs diff = {mag_preserved:.3e}  "
          f"({'magnitude-preserving (does NOT lower max)' if mag_preserved<1e-6 else 'changes magnitudes'})")
    print(f"    HD-doubling D(lambda=2) = {d2 if d2 is not None else 'n/a (m even)'}   "
          f"inversion D(lambda=-1=m-1) = {dm1:.4f}   noise ~ {1/math.sqrt(m):.4f}")
    # also: how many lambdas exceed 3x noise?  (is the structure SPARSE = few strong, or DIFFUSE)
    thresh = 3/math.sqrt(m)
    nstrong = sum(1 for v,l in res if v > thresh)
    print(f"    # dilations with D>3/sqrt(m)={thresh:.3f}: {nstrong} of {len(res)}  "
          f"({'SPARSE structure' if nstrong < 0.1*len(res) else 'diffuse'})")
    return strong_lam, strong_val, invol, mag_preserved, d2, dm1

if __name__ == '__main__':
    print("PRIZE-PERIOD dilation structure: exploitable or known symmetry?")
    print("="*70)
    for n in [8, 16]:
        # need m odd to test HD lambda=2: pick p with (p-1)/n odd
        for lo in [2003, 5003, 10007, 50021]:
            p = find_prime_cong1(n, lo)
            m = (p-1)//n
            if m % 2 == 1:   # m odd -> can test HD-doubling lambda=2
                analyze(p, n)
                break
        else:
            analyze(find_prime_cong1(n, 2003), n)
    print("="*70)
    print("If strong-lambda is an INVOLUTION that PRESERVES magnitudes, it only permutes the")
    print("period values -> CANNOT lower the max -> NOT sup-norm-exploitable = same BGK wall.")
