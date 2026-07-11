#!/usr/bin/env python3
"""
probe_p2_wrap_relation_structure.py  (#444 — P2: structure of the r=2 wrap excess A_2)

The r=2 excess A_2 is ZERO except at highly-2-adic primes (n=32: p with A_2=384, n=64: 1536).
A_2=384=12*32 at n=32; A_2=1536=24*64 at n=64. The "12" and "24" suggest a STRUCTURED orbit count.
This probe identifies the EXACT cyclotomic relation zeta^a+zeta^b-zeta^c-zeta^d that wraps at the
spike prime, to see if A_2 is bounded by an ELEMENTARY orbit count (=> unconditional O(n) bound)
or is genuinely arithmetic-dependent (=> reduces to the cyclotomic norm-divisibility wall).

If A_2 = (orbit of ONE short relation) * (multiplicity), it is O(n) and the soft ceiling
E_2 = 3n^2 + O(n) is PROVABLE elementarily. If the relations proliferate with p, it is the wall.
"""
import sys, os, math
from collections import Counter
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from probe_407_anom_worst_rtraj_n32 import Ep, roots_modp, is_prime

def proper_band_primes(n, blo, bhi, cap):
    lo = max(int(n**blo), n**3 + 1); hi = int(n**bhi)
    out = []; m = max(2, lo//n)
    while m*n + 1 <= hi and len(out) < cap:
        p = m*n + 1
        if p >= lo and p > n**3 and is_prime(p): out.append(p)
        m += 1
    return out

def char0_zero(i,j,k,l,n):
    """Is zeta^i+zeta^j-zeta^k-zeta^l == 0 in Z[zeta_n]? For n=2^m: {i,j}={k,l} OR {i,j},{k,l}
    are antipodal pairs (a,a+n/2). The multiset {i,j} minus {k,l} must telescope via zeta^{n/2}=-1."""
    # zeta^i+zeta^j = zeta^k+zeta^l in C iff {i,j}={k,l} (sums of 2 distinct unit vectors equal
    # iff same multiset) -- UNLESS pairs are antipodal giving 0=0. zeta^i+zeta^j=0 iff j=i+n/2.
    h = n//2
    lhs = Counter([i%n, j%n]); rhs = Counter([k%n, l%n])
    if lhs == rhs: return True
    # both sides zero (antipodal)
    lz = (j%n == (i+h)%n); rz = (l%n == (k+h)%n)
    if lz and rz: return True
    return False

def main():
    print("="*100)
    print("P2 r=2 WRAP RELATION STRUCTURE: identify the cyclotomic relations causing A_2 at spike primes.")
    print("="*100)
    for n in [32, 64]:
        E20 = 3*n*n - 3*n
        ps = proper_band_primes(n, 3.5, 4.5, 300 if n==32 else 150)
        # find spike prime (max A_2)
        best=(0,None)
        for p in ps:
            mu=roots_modp(n,p); a2=Ep(mu,p,2)-E20
            if a2>best[0]: best=(a2,p)
        a2,p = best
        mu = roots_modp(n,p)
        v2 = 0; x=p-1
        while x%2==0: x//=2; v2+=1
        print(f"\nn={n}: spike prime p={p} (v2(p-1)={v2}, beta={math.log(p)/math.log(n):.3f}), A_2={a2}={a2//n}*n")
        # enumerate wrap relations: i+j==k+l mod p but NOT char-0 zero, count by relation TYPE
        reltypes = Counter()
        examples = {}
        cnt = 0
        for i in range(n):
            for j in range(n):
                for k in range(n):
                    for l in range(n):
                        if (mu[i]+mu[j]-mu[k]-mu[l])%p==0 and not char0_zero(i,j,k,l,n):
                            cnt += 1
                            # normalize relation by rotation (subtract min exponent) to find orbit
                            base = min(i,j,k,l)
                            rel = tuple(sorted([(i-base)%n, (j-base)%n]) ) , tuple(sorted([(k-base)%n,(l-base)%n]))
                            # canonical: the difference pattern
                            d = tuple(sorted([(i-k)%n,(i-l)%n,(j-k)%n,(j-l)%n]))
                            reltypes[d]+=1
                            if d not in examples: examples[d]=(i,j,k,l)
        print(f"  total wrap quadruples (ordered) = {cnt} (matches A_2={a2}: {cnt==a2})")
        print(f"  distinct difference-patterns = {len(reltypes)}; each pattern's orbit count:")
        for d,c in sorted(reltypes.items(), key=lambda kv:-kv[1])[:6]:
            i,j,k,l = examples[d]
            print(f"    pattern{d}: {c} occurrences; ex (i,j,k,l)=({i},{j},{k},{l}) -> "
                  f"roots {mu[i]}+{mu[j]}-{mu[k]}-{mu[l]} = {(mu[i]+mu[j]-mu[k]-mu[l])} = {(mu[i]+mu[j]-mu[k]-mu[l])//p}*p")
    print("\nVERDICT: if few patterns x phi(n)-orbit => A_2=O(n), soft ceiling ELEMENTARILY provable.")
    print("="*100)

if __name__ == "__main__":
    main()
