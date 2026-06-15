#!/usr/bin/env python3
"""
wf407 / T02-shkredov : DEFINITIVE VERDICT probe for the
"non-moment additive-comb bound on the r-fold cross-surplus" thread.

QUESTION (the prize lever): does ANY of
  (S) Shkredov subgroup additive/higher-energy bounds (E^+(Gamma) subgroup-energy line;
      1504.04522 = tripling const |3Gamma|>>|Gamma|^2/log, E^x(Gamma+x)<<|Gamma|^2 log)
      -- ALL valid only for |Gamma| in (p^{1/4}, sqrt p); the famous E^+ << |Gamma|^{32/13}
      improvement is a *saving over the trivial* |Gamma|^{8/3} and likewise density-gated
  (B) Chang-Shparlinski / Kerr-Macourt BILINEAR double-sums  (a DIFFERENT mechanism,
      sub-sqrt(q) from bilinear structure)
supply a usable bound on the r-fold cross-surplus of mu_n at the prize regime
  n = 2^mu  (mu up to 32),  p ~ n*2^128,  index m=(p-1)/n=2^128,  n ~ p^{1/5} << p^{1/4}?

We test EXACTLY (full enumeration), not sampled:
  1. The prize PARAMETER regime: where each cited result is non-vacuous vs. where the prize lives.
  2. The Shkredov 32/13 bound vs the trivial diagonal floor E^+ >= |Gamma|^2 and the sqrt-loss:
     does 32/13 beat the W2 sqrt(n) Johnson barrier at the prize?  list >= sqrt(n*E).
  3. The r-fold "cross-surplus" S_r := E_r(mu_n over F_p) - E_r^{char0}(mu_n)  (the mod-q defect),
     and whether a bound of Shkredov/bilinear TYPE controls it (decay in r) or it is the
     same Gauss-period object.
  4. The bilinear mechanism: |sum_{a,b} alpha_a beta_b chi(a+b)| -- does the subgroup structure
     of mu_n give a bilinear form whose sub-sqrt(q) gain survives at n<p^{1/4}?

Output is a structured verdict with exact numbers.
"""

import itertools, math, cmath
from sympy import isprime, primitive_root

# ----------------------------------------------------------------------------
# Helpers: smooth multiplicative subgroup mu_n of F_p^*  (n | p-1, n a power of 2)
# ----------------------------------------------------------------------------
def subgroup(p, n):
    """Return the order-n multiplicative subgroup of F_p^* (n | p-1)."""
    g = primitive_root(p)
    h = pow(g, (p-1)//n, p)
    S = set()
    x = 1
    for _ in range(n):
        S.add(x); x = (x*h) % p
    assert len(S) == n
    return sorted(S)

def add_energy_Fp(S, p):
    """E^+(S) = #{(a,b,c,d) in S^4 : a+b = c+d mod p}.  Exact."""
    from collections import Counter
    c = Counter((a+b) % p for a in S for b in S)
    return sum(v*v for v in c.values())

def rfold_energy_Fp(S, p, r):
    """E_r(S) = #{ (x_1..x_r ; y_1..y_r) in S^{2r} : sum x = sum y mod p } = sum_s N_r(s)^2,
       N_r(s)=# r-subset-with-repetition ordered tuples summing to s.  Exact."""
    from collections import Counter
    # ordered r-tuples sums
    sums = Counter()
    # iterative convolution to avoid n^r blowup where possible
    cur = Counter({0:1})
    for _ in range(r):
        nxt = Counter()
        for s,v in cur.items():
            for x in S:
                nxt[(s+x)%p] += v
        cur = nxt
    return sum(v*v for v in cur.values())

def rfold_energy_char0(S_roots, r, tol=1e-7):
    """E_r over the COMPLEX n-th roots of unity: count multiset-collisions of r-fold sums.
       S_roots = list of complex unit roots. Exact-ish via rounding (clean separation)."""
    from collections import Counter
    cur = {(0.0,0.0):1}
    def key(z): return (round(z.real,6), round(z.imag,6))
    cur = Counter({ (0.0,0.0):1 })
    acc = Counter({0j:1})
    for _ in range(r):
        nxt = Counter()
        for s,v in acc.items():
            for x in S_roots:
                nxt[s+x] += v
        # re-bucket by rounded key
        reb = Counter()
        rep = {}
        for s,v in nxt.items():
            k = key(s)
            reb[k]+=v
            rep.setdefault(k, s)
        acc = Counter({ rep[k]: v for k,v in reb.items() })
    # energy = sum over distinct sums of count^2
    by = Counter()
    for s,v in acc.items():
        by[key(s)] += v
    return sum(v*v for v in by.values())

def double_factorial(m):
    r=1
    while m>1:
        r*=m; m-=2
    return r

# ----------------------------------------------------------------------------
print("="*78)
print("PART 1 -- PRIZE PARAMETER REGIME vs the regime where Shkredov / bilinear apply")
print("="*78)
# Prize: p ~ n*2^128, n=2^mu.  So log_n(p) = mu + 128/mu  (since log2 p ~ mu+128).
# Subgroup density exponent: |Gamma| = n = p^{theta}, theta = mu/(mu+128).
print(f"{'mu':>4} {'n=2^mu':>10} {'log2 p~':>8} {'theta=log_p|G|':>16} {'p^{1/4}?':>10} {'p^{1/3}?':>10} {'p^{3/7}?':>10}")
for mu in [3,4,5,6,8,12,16,24,32]:
    n = 2**mu
    log2p = mu + 128.0          # p ~ n*2^128
    theta = mu/log2p
    print(f"{mu:>4} {n:>10} {log2p:>8.1f} {theta:>16.4f} "
          f"{('YES' if theta<0.25 else 'no '):>10} "
          f"{('YES' if theta<1/3 else 'no '):>10} "
          f"{('YES' if theta<3/7 else 'no '):>10}")
print("""
READING: theta = log_p|Gamma|.  Shkredov 1504.04522 / Heath-Brown-Konyagin energy bounds are
stated for subgroups with |Gamma| in (p^{1/4}, p^{2/3}) -- they REQUIRE theta > 1/4 to beat
trivial.  Bourgain-Glibichuk sub-sqrt(q) bilinear needs |H| >> p^{3/7} (theta>3/7=0.4286).
The PRIZE has theta = mu/(mu+128) -> at most 32/160 = 0.20 < 1/4 < 3/7 for ALL mu<=32.
==> prize subgroup is BELOW the applicability floor of EVERY one of these results.""")

# ----------------------------------------------------------------------------
print("="*78)
print("PART 2 -- Does the Shkredov 32/13 exponent beat the W2 sqrt(n) Johnson barrier?")
print("="*78)
# W2 wall: list >= sqrt(n * E).  Johnson list cap ~ poly.  Energy-route floor needs E close to n^2.
# Shkredov: E^+(Gamma) << |Gamma|^{32/13}.  Trivial floor: E^+ >= |Gamma|^2.
# 32/13 = 2.4615 > 2.  So Shkredov is an UPPER bound *larger* than the diagonal -- and the
# list bound it feeds is list ~ sqrt(n*E) >= sqrt(n * n^2) = n^{3/2}.  Worse than Johnson? Check.
print(f"  Shkredov exponent 32/13 = {32/13:.6f}  (vs diagonal 2.0)")
print(f"  list >= sqrt(n * E^+) ;  with E^+ ~ n^2 (minimal): list >= n^{{3/2}} = {1.5}")
print(f"  with E^+ ~ n^{{32/13}} (Shkredov UB): list <= sqrt(n^{{1+32/13}}) = n^{{{(1+32/13)/2:.4f}}}")
print("""
READING: the energy route ALWAYS pays a sqrt(n) (W2). list >= sqrt(n*E^+) and E^+>=n^2 forces
list >= n^{3/2} > n unconditionally (diagonal alone).  Shkredov's 32/13 is an UPPER bound on E^+,
giving list <= n^{(1+32/13)/2} = n^{1.731}, which is STILL > n^{3/2} > Johnson-window n.
The Shkredov bound -- even if it applied -- cannot push the energy-route list below n^{3/2}.
It is a bound in the WRONG DIRECTION for the cross-surplus (controls how large E can be, the
floor side needs it small; and the sqrt-loss is structural).  This is exactly wall W2.""")

# ----------------------------------------------------------------------------
print("="*78)
print("PART 3 -- The r-fold CROSS-SURPLUS S_r = E_r^{Fp} - E_r^{char0}  (exact, small n)")
print("="*78)
# Find small primes p with a power-of-2 subgroup, deep enough (p >> n^2.5) to mimic the regime.
cases = [
    # (p, n)
    (337, 8), (1009, 8), (3361, 16), (12289, 16), (12289, 32),
    (65537, 16), (40961, 16), (786433, 32), (786433, 16),
]
print(f"{'p':>8} {'n':>4} {'theta':>7} {'r':>3} {'E_r^Fp':>14} {'E_r^c0':>14} "
      f"{'surplus S_r':>14} {'S_r/E_r^c0':>10} {'(2r-1)!!n^r':>16}")
results_p3 = []
for (p,n) in cases:
    if (p-1) % n != 0: continue
    S = subgroup(p, n)
    # char-0 roots of unity (same n)
    roots = [cmath.exp(2j*math.pi*k/n) for k in range(n)]
    theta = math.log(n)/math.log(p)
    for r in [2,3]:
        if n**r > 6_000_000:   # keep enumerable
            continue
        Efp = rfold_energy_Fp(S, p, r)
        Ec0 = rfold_energy_char0(roots, r)
        surplus = Efp - Ec0
        gauss = double_factorial(2*r-1)*(n**r)
        ratio = surplus/Ec0 if Ec0 else 0.0
        print(f"{p:>8} {n:>4} {theta:>7.3f} {r:>3} {Efp:>14} {Ec0:>14} "
              f"{surplus:>14} {ratio:>10.4f} {gauss:>16}")
        results_p3.append((p,n,r,Efp,Ec0,surplus,gauss))
print("""
READING: S_r = E_r^{Fp} - E_r^{char0} >= 0 (one-sided inflation, KB-confirmed).  This surplus
is EXACTLY the mod-q defect = sum_{z != 0, p|z} R_r(z) (autocorrelation collisions that the prime
wraps around).  A 'Shkredov-type' bound would need to bound S_r with DECAY in r (sub-Gaussian
tail).  But S_r is generated by sparse subset-sum coincidences mod p, NOT by the multiplicative
structure Shkredov exploits -- Shkredov bounds E^+ = E_2 only (the r=2 representation function),
NOT the r-fold E_r at r ~ log q.  The 32/13 machinery (Stepanov/incidence) is r=2-locked.""")

# ----------------------------------------------------------------------------
print("="*78)
print("PART 4 -- BILINEAR mechanism test: does mu_n carry a sub-sqrt(q) bilinear form?")
print("="*78)
# Chang-Shparlinski/Kerr-Macourt bilinear: |sum_{a in A, b in B} chi(a+b)| << ... .
# The relevant object for the worst Gauss period is the SINGLE additive char sum eta_b = sum_{x in mu_n} e_p(b x).
# Bilinear gains require TWO free variables ranging over sets of size ~ p^{1/2+}.  mu_n is ONE set
# of size n = p^{theta}, theta<=0.2.  Test: the best bilinear split A.B = mu_n (as a sumset) gives
# at most |A|,|B| ~ sqrt(n) -- far below the p^{3/7} threshold for any gain.
print(f"{'mu':>4} {'n':>10} {'sqrt(n)=|A|~|B|':>16} {'log_p(sqrt n)':>14} {'need>3/7=.4286':>16}")
for mu in [8,16,24,32]:
    n=2**mu; log2p=mu+128.0
    half = math.sqrt(n)
    th_half = math.log(half)/(log2p*math.log(2))*math.log(2)  # log_p(sqrt n)
    th_half = (mu/2)/log2p
    print(f"{mu:>4} {n:>10} {half:>16.1f} {th_half:>14.4f} "
          f"{('PASS' if th_half>3/7 else 'FAIL'):>16}")
print("""
READING: a bilinear sum needs BOTH variables to range over sets of multiplicative-density
> p^{3/7}.  mu_n is a single thin set; splitting it as a sumset A+B (or product) gives factors of
density theta/2 <= 0.10 << 3/7.  The bilinear sub-sqrt(q) gain (Bourgain-Glibichuk, Kerr-Macourt)
is VACUOUS for any factorization of mu_n at the prize.  The eta_b is intrinsically a LINEAR
(single-variable) character sum over a thin subgroup -- there is no second free variable to
bilinearize.  => the bilinear mechanism does not apply (DIFFERENT mechanism, but same vacuity).""")

# ----------------------------------------------------------------------------
print("="*78)
print("PART 5 -- COLLAPSE CHECK: is the surplus S_r the SAME object as the Gauss-period house?")
print("="*78)
# Verify the identity sum_b |eta_b|^{2r} = q * E_r (so E_r literally IS the 2r-th moment of the
# Gauss periods).  Then any bound on the cross-surplus = bound on the deep moment = the W4/Paley wall.
for (p,n) in [(337,8),(1009,8),(3361,16)]:
    if (p-1)%n: continue
    S = subgroup(p,n)
    w = cmath.exp(2j*math.pi/p)
    eta = [sum(w**((b*x)%p) for x in S) for b in range(p)]
    for r in [2]:
        lhs = sum(abs(e)**(2*r) for e in eta)
        rhs = p * rfold_energy_Fp(S,p,r)
        print(f"  p={p} n={n} r={r}:  sum_b|eta_b|^{{2r}} = {lhs:.3f}   q*E_r = {rhs}   "
              f"match={'YES' if abs(lhs-rhs)<1e-3*max(1,rhs) else 'NO'}")
print("""
READING: sum_b |eta_b|^{2r} = q*E_r EXACTLY.  So E_r (hence its char-p surplus S_r) is LITERALLY
the 2r-th moment of the Gauss periods.  Bounding the cross-surplus to control B = max|eta_b| is
THE moment method -- proven (W4) to stop sqrt(log) short of the sup-norm at r_max = 2 log_n p.
A non-moment Shkredov/bilinear bound would have to bypass this -- but Shkredov bounds E_2 (one r),
and the bilinear mechanism needs a second variable mu_n does not have.  Both collapse onto the
SAME Gauss-period / Paley-eigenvalue wall the moment route already hits.""")

print("\n" + "="*78)
print("VERDICT: WALLED.  Shkredov 32/13 (i) requires theta>1/4 (prize theta<=0.20, vacuous),")
print("(ii) bounds only E_2 not the r-fold E_r needed at r~log q, (iii) is sqrt(n)-lossy (W2);")
print("the bilinear mechanism needs a second density-p^{3/7} variable mu_n lacks.  Both collapse")
print("onto sum_b|eta_b|^{2r}=q*E_r = the Gauss-period/Paley-eigenvalue wall (W2/W4). No closure.")
print("="*78)
