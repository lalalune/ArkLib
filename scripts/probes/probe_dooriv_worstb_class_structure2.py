#!/usr/bin/env python3
"""
door-(iv) worst-b class structure — FOLLOWUP, artifact-corrected.

probe v1 found chi2(worst_b)=+1 for every prime, BUT that was a SCAN ARTIFACT: I enumerated
b=g^j and j happened to be even (=> b a QR by construction) and one rep per coset doesn't
sample BOTH QR classes per coset evenly. Here:

 - eta_b is mu_n-INVARIANT only up to the coset; but |eta_{b}| for b and b' in the SAME mu_n
   coset are EQUAL (since mu_n*x just permutes the sum). So |eta| is genuinely a function on
   the quotient Z_k, k=(p-1)/n. The QR class of a coset rep is well-defined mod the QR class
   of mu_n itself.
 - KEY: mu_n (n=2^a) consists of 2^a-th roots of unity. Is mu_n subset of QR? An element is a
   QR iff it's a square iff its index is even. mu_n = <g^k>, k=(p-1)/n. g^k is a QR iff k even.
   k=(p-1)/n; p-1 = n * k, p odd so p-1 even. k = (p-1)/n. For n=2^a and p-1 = 2^a * k', the
   2-adic valuation of p-1 is exactly v2 since p == 1 + n*(odd) typically => k odd => g^k is a
   NON-residue => mu_n is NOT inside QR, mu_n hits both classes. Then chi2 is NOT constant on a
   coset and "chi2(worst coset)" is ill-defined. So the v1 'always +1' is meaningless.

CORRECT class question on the QUOTIENT Z_k: index j of worst coset. Bias to test:
 (A) v_2(j)  — 2-adic valuation of the worst coset index (is worst-j 2-adically deep / shallow?)
 (B) j mod small d (d=3,5,...) — residue bias of worst index
 (C) is the GAP between the top few coset indices structured (arithmetic progression? small gcd?)

If worst-j is 2-adically deep (high v2) or sits in an AP, that's exploitable structure.
If v2(worst-j) ~ Geometric(1/2) (= uniform random integer) and residues are flat, CLASS-BLIND.
EXACT int phases, proper mu_n, p>>n^3, multiple structured primes, FULL coset scan where feasible.
"""
import cmath, math

def is_prime(m):
    if m < 2: return False
    for q in (2,3,5,7,11,13,17,19,23,29,31,37):
        if m % q == 0: return m == q
    d=m-1; r=0
    while d%2==0: d//=2; r+=1
    for a in (2,3,5,7,11,13,17,19,23,29,31,37):
        x=pow(a,d,m)
        if x==1 or x==m-1: continue
        ok=False
        for _ in range(r-1):
            x=x*x%m
            if x==m-1: ok=True; break
        if not ok: return False
    return True

def find_primes(n, beta, count):
    primes=[]; kk=max(1, n**beta//n)
    while len(primes)<count:
        p=kk*n+1
        if p>n**3 and is_prime(p): primes.append(p)
        kk+=1
    return primes

def mu_n_and_g(p,n):
    pm1=p-1; fs=set(); m=pm1; d=2
    while d*d<=m:
        while m%d==0: fs.add(d); m//=d
        d+=1
    if m>1: fs.add(m)
    g=next(c for c in range(2,p) if all(pow(c,pm1//q,p)!=1 for q in fs))
    h=pow(g,pm1//n,p); mu=[]; cur=1
    for _ in range(n): mu.append(cur); cur=cur*h%p
    return g, mu

def eta2(p,mu,b):
    s=0j; t=2*math.pi/p
    for x in mu:
        s+=cmath.exp(1j*((b*x%p)*t))
    return s.real*s.real+s.imag*s.imag

def v2(x):
    if x==0: return 99
    v=0
    while x%2==0: x//=2; v+=1
    return v

def run(n, beta=4, nprimes=5):
    primes=find_primes(n,beta,nprimes)
    print(f"\n=== n={n} beta={beta} primes={primes} ===")
    all_top_j=[]; v2_worst=[]
    for p in primes:
        g,mu=mu_n_and_g(p,n)
        k=(p-1)//n
        full = k<=120000
        # P2 FIX (codex): for large k, sample coset indices UNIFORMLY across the WHOLE quotient
        # Z_k (not the first-40k prefix) so the argmax + residue statistics are not prefix-biased.
        if full:
            J_indices = range(k)
        else:
            import random
            random.seed(0xC0FFEE ^ p)            # reproducible
            J_indices = sorted(random.sample(range(k), 40000))
        vals=[]
        for j in J_indices:
            b = pow(g, j, p)                      # exact: b = g^j mod p
            vals.append((eta2(p,mu,b), j))
        vals.sort(reverse=True)
        topj=[j for _,j in vals[:12]]
        worst_j=topj[0]
        all_top_j.extend(topj)
        # P2 FIX (codex): EXCLUDE the worst_j==0 Fermat zero-index artifact (v2(0)=99) from the
        # 2-adic-valuation aggregate, matching the 'excluded' claim in the writeup.
        if worst_j != 0:
            v2_worst.append(v2(worst_j))
        # gaps / AP test among top 6
        t6=sorted(topj[:6])
        diffs=[t6[i+1]-t6[i] for i in range(len(t6)-1)]
        g_gcd=0
        for d in diffs: g_gcd=math.gcd(g_gcd,d)
        scan = 'FULL' if full else 'rand40k/k'
        print(f"  p={p} scan={scan} k={k}: worst_j={worst_j} v2={v2(worst_j)}  "
              f"top6_j={t6}  top6_gap_gcd={g_gcd}")
    # aggregate v2 distribution of worst-j vs Geometric(1/2) expectation (mean=1); artifact excluded
    mean_v2 = (sum(v2_worst)/len(v2_worst)) if v2_worst else float('nan')
    # j mod 3 distribution of top set
    mod3=[j%3 for j in all_top_j]
    f3=[mod3.count(r)/len(mod3) for r in range(3)]
    print(f"  >>> n={n}: mean v2(worst_j)={mean_v2:.2f} (uniform-random int -> 1.00)  "
          f"top-set j%3 dist={['%.2f'%x for x in f3]} (flat=0.33)")
    return mean_v2, f3

if __name__=="__main__":
    print("door-(iv) worst-COSET-INDEX arithmetic (artifact-corrected, quotient Z_k)")
    R=[]
    for n in [16,32,64,128]:
        R.append((n,)+run(n))
    print("\n========== VERDICT ==========")
    print(" n   mean-v2(worst_j)   j%3 dist of top set")
    for n,mv,f3 in R:
        print(f" {n:4d}   {mv:.2f}            {['%.2f'%x for x in f3]}")
    print("\nmean-v2 ~ 1.00 (Geometric/2) AND flat j%3 (~0.33) => worst-coset index is")
    print("ARITHMETICALLY UNSTRUCTURED in the quotient => no class/AP lever for door-(iv).")
    print("A high mean-v2 (2-adically deep) or a locked j%3 => exploitable structure to formalize.")
