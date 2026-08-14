"""
#444 §6.5 — PROBE: is the over-det vanishing-subset generating function Z(t)=exp(Sum_r I_r t^r/r) RATIONAL,
and where are its poles? (the sole-unfinished §6.5 structural derivation: m* growth law from pole structure)

OBJECT (exact, char-0 / exact-cyclotomic, PROPER mu_n = n-th roots of unity, n=2^a):
  For mu_n embedded as primitive n-th roots of unity, a subset S of Z/n has power sums
  p_j(S) = Sum_{i in S} zeta^{i*j}  (zeta = exp(2 pi i /n)).  "vanishing-(e1..e_d)" = e_1(S)=..=e_d(S)=0
  <=> p_1(S)=..=p_d(S)=0 (Newton, char 0).  We compute the EXACT count over Z (cyclotomic integers),
  which is the char-0 / large-p value (p-independent above the Sidon threshold per in-tree results).

We measure two sequences and test rationality of their ordinary generating functions:
  (A) V_r(n) = #{S subset Z/n : p_1(S)=..=p_r(S)=0}        (the vanishing-depth-r subset count)
  (B) the coset-closed count C(n/d, *) baseline for comparison.

RATIONALITY TEST: a power series Sum a_k t^k is rational with denominator deg <= D iff the Hankel
determinants H_k^{(D+1)} vanish for all k (equivalently the sequence satisfies a linear recurrence of
order <= D with constant coeffs). We test whether {V_r(n)}_r (for fixed n, r=0..n) or {V_d(n)}_n
(fixed depth d, n=2^a) is linear-recurrent => generating function rational => pole structure readable.

We work in EXACT cyclotomic arithmetic via Gaussian/cyclotomic integers: represent zeta^i exactly as a
vector in Z[zeta_n] = Z[x]/(Phi_n(x)), Phi_n(x)=x^{n/2}+1 for n=2^a. Power sum p_j(S) is a vector; it is
0 iff all coords 0. PROPER subgroup, exact, NEVER full group.
"""
import itertools, sys
from math import comb
from functools import lru_cache

def phi_reduce(vec, half):
    # reduce a length-up-to-(2*half) coeff list mod x^half + 1  (n=2^a => Phi_n = x^{half}+1, half=n/2)
    out = [0]*half
    for i,c in enumerate(vec):
        if c==0: continue
        idx = i % (2*half)
        sign = 1
        if idx >= half:
            idx -= half; sign = -1
        out[idx] += sign*c
    return out

def zeta_pow(e, half):
    # zeta^e as a vector in Z[x]/(x^half+1), zeta=x.  e mod 2*half, x^half=-1.
    e %= (2*half)
    v=[0]*half
    if e<half: v[e]=1
    else: v[e-half]=-1
    return v

def powersum_vanishes_upto(S, n, r):
    """Return True iff p_1(S)=...=p_r(S)=0 over Z[zeta_n], n=2^a."""
    half = n//2
    for j in range(1, r+1):
        acc=[0]*half
        for i in S:
            v = zeta_pow((i*j) % n, half)
            for t in range(half): acc[t]+=v[t]
        if any(acc): 
            return False
    return True

def V_r(n, r):
    """Exact count of subsets S of Z/n with p_1..p_r vanishing (char 0)."""
    cnt=0
    idx=list(range(n))
    for size in range(0, n+1):
        for S in itertools.combinations(idx, size):
            if powersum_vanishes_upto(S, n, r):
                cnt+=1
    return cnt

def berlekamp_massey(seq):
    """Return minimal linear recurrence order over Q for integer seq, or None if none of order<len/2."""
    # rational BM via fractions
    from fractions import Fraction
    s=[Fraction(x) for x in seq]
    ls, cur = [], []
    lf=0; ld=Fraction(0)
    for i in range(len(s)):
        t=Fraction(0)
        for j in range(len(cur)): t+=cur[j]*s[i-1-j]
        d=s[i]-t
        if d==0: continue
        if not cur:
            cur=[Fraction(0)]*(i+1); lf=i; ld=d; continue
        coef=d/ld
        nc=[Fraction(0)]*(i-lf-1)+[coef]+[-coef*x for x in ls]
        if len(cur)<len(nc):
            t2=cur[:]; cur=nc; 
            if len(nc)-len(t2) > 0:
                ls=t2; lf=i; ld=d
        else:
            for j in range(len(nc)): cur[j]+=nc[j]
    return cur

if __name__=="__main__":
    print("=== §6.5 over-det vanishing-subset count V_r(n) (EXACT char-0 cyclotomic, n=2^a, proper mu_n) ===",flush=True)
    # depth-by-depth at fixed small n we can fully enumerate: n=8 (256 subsets), n=16 (65536 subsets)
    for n in [4, 8, 16]:
        row=[]
        for r in range(0, n//2+2):
            row.append(V_r(n,r))
        print(f"n={n:2d}: V_r for r=0..{n//2+1} = {row}",flush=True)
        # Berlekamp-Massey on the r-sequence (does it satisfy a short linear recurrence => rational GF in t?)
        bm=berlekamp_massey(row)
        print(f"      BM recurrence (order {len(bm)}): coeffs={ [str(c) for c in bm] }",flush=True)
    print("DONE",flush=True)
