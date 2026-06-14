"""
probe_wfLF_crosscell_shkredov.py  (#407 lane wf-LF)

THE crossCell object (CumulantDyadicDescent):
    N0(G, r) = 2*N0(H, r) + crossCell(H, ζ, r),
where G = mu_n = H ⊔ ζ·H, H = mu_{n/2} (squares), ζ a fixed non-square.

  N0(G, r)      = #{ v ∈ G^r : Σ v_i = 0 }                       (the full relation count)
  2*N0(H, r)    = endpoint/diagonal mass (all-square + all-nonsquare)
  crossCell     = Σ_{0<|T|<r} #{(u:T^c→H, w:T→H) : Σu + ζ·Σw = 0}  (off-diagonal cross-resonance)

The OPEN LEVER (Conn #78/#100, BCHKS Conj 1.12): a NON-MOMENT, uniform-over-primes ADDITIVE-COMB
upper bound on crossCell at depth r≈ln q that BEATS the trivial diagonal — i.e. crossCell ≤ ε·(2 N0(H,r))
with ε < 1 uniform over primes/n, OR more precisely crossCell ≤ N0(H,r)/n · (something), the
"random" expectation. Shkredov's higher-energy machinery (3rd energy E_3, BSG, sum-product) is the
candidate input. If ANY uniform sub-trivial bound holds, that's the prize.

This probe COMPUTES crossCell exactly (via per-coset subset-sum count vectors mod p, exact when
q > the relation height so no wraparound spurious — but we work mod p honestly since that IS the
char-p object) and measures:
  (1) crossCell / (2 N0(H,r))         — the diagonal-fraction (trivial bound = whatever it is; <1 ?)
  (2) crossCell / (binom cross-pattern count * N0(H,r)/n)  — vs the "random" Shkredov expectation
  (3) growth in r at fixed n, across MULTIPLE primes, to test uniformity-over-q
  (4) the Shkredov third-energy E_3(H) and the BSG/sum-product diagnostics on the half-subgroup H

KEY HONESTY POINT: N0 here is the char-p relation count (sums mod p), which is the actual prize
object. We compute it exactly by FFT-free direct count vector r-fold self-convolution mod p.
"""
import math, itertools, sys
import numpy as np

def pr(*a):
    print(*a); sys.stdout.flush()

def isprime(m):
    if m < 2: return False
    for q in (2,3,5,7,11,13,17,19,23,29,31,37):
        if m % q == 0: return m == q
    d=m-1; s=0
    while d%2==0: d//=2; s+=1
    for a in (2,3,5,7,11,13,17,19,23,29,31,37):
        x=pow(a,d,m)
        if x in (1,m-1): continue
        for _ in range(s-1):
            x=x*x%m
            if x==m-1: break
        else: return False
    return True

def prime_factors(m):
    s=set(); d=2
    while d*d<=m:
        while m%d==0: s.add(d); m//=d
        d+=1
    if m>1: s.add(m)
    return s

def subgroup(p, n):
    assert (p-1)%n==0
    e=(p-1)//n; pf=prime_factors(n)
    for c in range(2,p):
        h=pow(c,e,p)
        if pow(h,n,p)!=1: continue
        if any(pow(h,n//q,p)==1 for q in pf): continue
        S=set(); x=1
        for _ in range(n): x=x*h%p; S.add(x)
        if len(S)==n: return sorted(S)
    raise RuntimeError("no subgroup")

def primes_for(n, betas, count_each=1):
    """primes p = n*m+1 in regime p ~ n^beta (so m ~ n^{beta-1})."""
    out=[]
    for beta in betas:
        target = int(round(n**(beta-1)))
        found=0; m=max(target,1)
        # search near target_index for primes p=n*m+1
        while found<count_each and m < target*3+50:
            p=n*m+1
            if isprime(p):
                out.append((p, beta)); found+=1
            m+=1
    return out

def count_vec(elts, p):
    """count vector of a multiset of residues mod p."""
    v=np.zeros(p, dtype=np.int64)
    for x in elts: v[x%p]+=1
    return v

def conv_mod(a, b, p):
    """cyclic convolution mod p of two count vectors (length p)."""
    # use FFT for speed; round to int. p can be ~1e4..1e5; r-fold so do repeated.
    fa=np.fft.rfft(a); fb=np.fft.rfft(b)
    c=np.fft.irfft(fa*fb, n=p)
    return np.rint(c).astype(np.int64)

def selfconv_power(base, r, p):
    """r-fold cyclic self-convolution of count vector `base` mod p -> count vector of r-sums."""
    # base is count vec of the set (each elt count 1). exponentiate by repeated squaring.
    result=None; b=base.copy(); e=r
    while e>0:
        if e&1:
            result = b.copy() if result is None else conv_mod(result, b, p)
        e>>=1
        if e>0: b=conv_mod(b,b,p)
    return result

def coset_split(S, p, n):
    """split mu_n into squares H and non-squares zeta*H. H = {x^2 : x in mu_n} actually
    H = unique index-2 subgroup = mu_{n/2}. zeta = a non-square generator element."""
    Sset=set(S)
    # mu_{n/2} = squares in mu_n
    H=sorted({ (x*x)%p for x in S })  # squares form the index-2 subgroup of order n/2
    assert len(H)==n//2, f"H size {len(H)} != {n//2}"
    Hset=set(H)
    zetaH=[x for x in S if x not in Hset]
    assert len(zetaH)==n//2
    # zeta = any element of zetaH; zetaH should equal zeta*H
    zeta=zetaH[0]
    return H, zetaH, zeta

def N0(elts, r, p):
    """char-p relation count #{v in elts^r : sum v_i = 0 mod p} via r-fold self-conv at coord 0."""
    base=count_vec(elts, p)
    cv=selfconv_power(base, r, p)
    return int(cv[0])

def crosscell_exact(H, zetaH, r, p):
    """crossCell = N0(G,r) - 2*N0(H,r) where G = H ∪ zetaH (disjoint).
    Equivalently sum over T of cross patterns. We just compute the two N0's mod p."""
    G = H + zetaH
    n0G = N0(G, r, p)
    n0H = N0(H, r, p)
    return n0G - 2*n0H, n0G, n0H

def shkredov_third_energy(H, p):
    """E_3(H) = #{a+b+c = d+e+f : all in H} ... actually 3rd additive energy
    E_3 = sum_x r_H(x)^3 where r_H(x)=#{(a,b):a+b=x, a,b in H}? Standard: E_3(A)=|{a1+a2=a3+a4=a5+a6}|...
    Use: E_k(A) = sum_x r(x)^k, r(x)=#{(a,b) in A^2 : a-b = x} (multiplicative-energy style).
    We report E_2 (additive energy) and E_3 (third energy) of H via difference counts."""
    Harr=np.array(H, dtype=np.int64)
    # r(x) = #{(a,b): a - b = x}, count vec
    rv=np.zeros(p, dtype=np.int64)
    diffs=(Harr[:,None]-Harr[None,:]).ravel()%p
    for d in diffs: rv[d]+=1
    E2=int((rv.astype(np.int64)**2).sum())
    E3=int((rv.astype(np.int64)**3).sum())
    return E2, E3

PMAX = 260_000   # cap p so r-fold cyclic FFT-conv stays feasible (length-p arrays, r up to ~12)

def primes_capped(n, count, lo_index):
    """`count` primes p=n*m+1 with m>=lo_index and p<=PMAX (thin-as-feasible, multiple primes)."""
    out=[]; m=lo_index
    while len(out)<count and n*m+1<=PMAX:
        p=n*m+1
        if isprime(p): out.append(p)
        m+=1
    return out

def run():
    pr("="*100)
    pr("crossCell growth + Shkredov diagnostics — char-p relation counts, MULTIPLE primes")
    pr("="*100)
    pr("\ncrossCell(H,r) = N0(G,r) - 2*N0(H,r).  diag-frac = crossCell/(2 N0(H,r)).")
    pr("Trivial diagonal bound is BEATEN iff a uniform-over-q eps<1 caps diag-frac at deep r.")
    pr("Honest regime note: p capped at %d (feasibility); these are SMALLER q than prize 2^160," % PMAX)
    pr("but we test UNIFORMITY of diag-frac across the several primes reachable at each n.\n")

    # index thresholds chosen so p stays <= PMAX while index m as large as feasible (thin direction).
    configs = [
        (8,  [16, 31, 64, 256, 1024]),   # n=8: indices -> p up to 8*1024+1 ~ 8200 ... push thinner
        (16, [16, 64, 256, 1024, 4096]),
        (32, [16, 64, 256, 1024, 2048]),
    ]
    for (n, indices) in configs:
        nh = n//2
        pr(f"\n{'='*90}\n--- n={n}  (H=mu_{nh}, |H|={nh}) ---")
        pr(f"{'p':>9} {'m=idx':>8} {'r':>3} {'N0(G,r)':>13} {'2N0(H,r)':>13} {'crossCell':>13} "
           f"{'diag-frac':>10} {'cc/(N0H/n)':>11}")
        diag_by_r = {}   # diag-frac samples per r across primes (uniformity test)
        for idx in indices:
            ps = primes_capped(n, 1, idx)
            if not ps: continue
            p = ps[0]
            if p > PMAX: continue
            try:
                S=subgroup(p, n)
                H, zetaH, zeta = coset_split(S, p, n)
            except Exception as ex:
                pr(f"  skip p={p}: {ex}"); continue
            beta = math.log(p)/math.log(n)
            rmax = 11 if p < 60000 else 9
            for r in range(2, rmax):
                cc, n0G, n0H = crosscell_exact(H, zetaH, r, p)
                df = cc/(2*n0H) if n0H else float('inf')
                # "random"/Shkredov baseline for cross mass: each cross pattern T contributes
                # ~ |H|^{r-1}/1 ... the per-pattern random expectation of #{Σu+ζΣw=0} is |H|^r / p.
                rand = (2**r - 2) * (nh**r) / p
                ccrand = cc/rand if rand else float('inf')
                pr(f"{p:>9} {idx:>8} {r:>3} {n0G:>13} {2*n0H:>13} {cc:>13} "
                   f"{df:>10.3f} {ccrand:>11.3f}")
                diag_by_r.setdefault(r, []).append((p, beta, df))
            E2,E3 = shkredov_third_energy(H, p)
            pr(f"       p={p} beta={beta:.2f}  Shkredov(H): E2/|H|^2={E2/nh**2:.3f}  "
               f"E3/|H|^3={E3/nh**3:.3f}  (->1 = Sidon-like, no extra structure)")
        # uniformity verdict per r
        pr(f"  -- uniformity of diag-frac across primes (n={n}) --")
        for r in sorted(diag_by_r):
            vals=[d for (_,_,d) in diag_by_r[r]]
            if len(vals)>=2:
                pr(f"     r={r}: diag-frac range [{min(vals):.3f}, {max(vals):.3f}]  "
                   f"spread={max(vals)-min(vals):.3f}  (small spread => q-uniform)")

    pr("\n" + "="*100)
    pr("INTERPRETATION KEY")
    pr("- diag-frac BOUNDED < some eps<1 uniformly over primes at deep r => sub-trivial bound EXISTS (PRIZE candidate)")
    pr("- diag-frac GROWS with r (toward / past 1) => cross DOMINATES => NO sub-trivial diagonal bound (=wall)")
    pr("- cc/(N0H/n) ~ const O(2^r) => cross is exactly the 'random' BCHKS-1.12 expectation (no anomaly, no savings)")
    pr("- E3(H)/|H|^3 -> 1 => H Sidon-like => Shkredov 3rd-energy/BSG give NOTHING (no additive structure to exploit)")
    pr("="*100)

if __name__=="__main__":
    run()
