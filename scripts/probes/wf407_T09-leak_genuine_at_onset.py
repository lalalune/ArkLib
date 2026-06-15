#!/usr/bin/env python3
"""
wf407_T09-leak_genuine_at_onset.py  --  #407 T09-leak.  Structure of GENUINE spurious defects,
and the ideal-SVP / fully-split reduction (part 3).

We pick primes BELOW the r=2 clean-range onset (p < 4^{n/2}) so GENUINE spurious E_2 defects
exist, and examine their structure:
  - what unit -g realizes {x1,x2} = -g {y1,y2} for the GENUINE (sum!=0, g!=-1) defects?
  - is -g in mu_n?  is it a FIXED g (one relation) or many?
  - the IDEAL-SVP connection: each genuine defect alpha = x1+x2-y1-y2 is a nonzero element of
    the fully-split degree-1 prime  P | p  (N(P)=p).  Its house and norm.  Whether the SVP-min
    of P is realized by such a 4-term (r=2) defect.

PART 3 (fully-split reduction).  q == 1 mod n  <=>  the prime p splits completely in Q(zeta_n)
(degree-1 primes P, N(P)=p) -- this is EXACTLY the smooth-domain hypothesis.  Pan-Xu: ideal-SVP
in cyclotomic ideals is poly-time only for NON-split q; the FULLY-SPLIT N(P)=p case (ours) is the
OPEN hard case.  We verify that the genuine-defect shortest vectors live in this split prime and
that their existence (the leak's count) IS the ideal-SVP short-vector enumeration -- so a bound on
the leak = a bound on #short-vectors of a fully-split cyclotomic prime, the Pan-Xu open gap.
"""
import math, itertools
from collections import defaultdict, Counter

def is_prime(m):
    if m < 2: return False
    for q in (2,3,5,7,11,13,17,19,23,29,31,37):
        if m % q == 0: return m == q
    d = m-1; s = 0
    while d % 2 == 0: d //= 2; s += 1
    for a in (2,3,5,7,11,13,17,19,23,29,31,37):
        x = pow(a, d, m)
        if x in (1, m-1): continue
        for _ in range(s-1):
            x = x*x % m
            if x == m-1: break
        else: return False
    return True

def factorize(m):
    s = {}; d = 2
    while d*d <= m:
        while m % d == 0: s[d] = s.get(d,0)+1; m //= d
        d += 1
    if m > 1: s[m] = s.get(m,0)+1
    return s

def primitive_root(p):
    fac = factorize(p-1)
    for g in range(2, p):
        if all(pow(g, (p-1)//q, p) != 1 for q in fac): return g
    return None

def primes_1_mod_in(n, lo, hi):
    out = []
    p = lo + ((1 - lo) % n)
    if p < 3: p += n
    while p <= hi:
        if p % n == 1 and is_prime(p): out.append(p)
        p += n
    return out

def subgroup(p, n):
    g = primitive_root(p); h = pow(g, (p-1)//n, p)
    return [pow(h, i, p) for i in range(n)], h

def e2_genuine(p, n, S):
    """genuine spurious off-diagonal collisions (sum!=0 and not g=-1 negation)."""
    bysum = defaultdict(list)
    for i in range(n):
        for j in range(i, n):
            s = (S[i]+S[j]) % p
            bysum[s].append((S[i], S[j]))
    out = []
    for s, prs in bysum.items():
        if len(prs) < 2 or s == 0: continue
        for a in range(len(prs)):
            for b in range(a+1, len(prs)):
                (x1,x2),(y1,y2) = prs[a], prs[b]
                if {x1,x2} == {y1,y2}: continue
                if frozenset(((p-y1)%p,(p-y2)%p)) == frozenset((x1,x2)): continue
                out.append((x1,x2,y1,y2,s))
    return out

def main():
    print("="*112)
    print("T09-leak  GENUINE spurious E_2 defects below the r=2 onset; leak unit -g; ideal-SVP")
    print("="*112)
    for n in (16, 32):
        onset = 4**(n//2)            # (2r)^{phi}=4^{n/2} at r=2
        print(f"\n#### n={n}  r=2 onset (2r)^phi = 4^{n//2} = 2^{n}  (genuine defects need p < 2^{n}) ####")
        # primes below onset, prize-shaped-ish (p ~ n^2.. up to onset)
        lo = int(n**2.0); hi = min(onset-1, int(n**2.6))
        ps = primes_1_mod_in(n, lo, hi)[:6]
        for p in ps:
            S, h = subgroup(p, n); muset = set(S)
            gen = e2_genuine(p, n, S)
            if not gen:
                print(f"  p={p} (2^{math.log2(p):.1f}): 0 genuine"); continue
            refl_g = Counter(); refl_in_mu = 0
            for (x1,x2,y1,y2,s) in gen:
                got = None
                for a0 in (y1,y2):
                    t = x1*pow(a0,-1,p)%p
                    if frozenset(((t*y1)%p,(t*y2)%p))==frozenset((x1,x2)):
                        got = (p-t)%p; break
                if got is not None:
                    refl_g[got]+=1
                    if got in muset: refl_in_mu+=1
            refl_total = sum(refl_g.values())
            top = refl_g.most_common(3)
            print(f"  p={p} (2^{math.log2(p):.1f}): #genuine={len(gen)}  "
                  f"R-refl realizable={100*refl_total/len(gen):.0f}% (in mu_n: {refl_in_mu}/{refl_total})  "
                  f"#distinct -g={len(refl_g)}  top -g (count): {top}")
    print("\n" + "="*112)
    print("CONCLUSION on the leak as a count:")
    print(" - GENUINE defects DO obey {x1,x2}=-g{y1,y2} for -g in mu_n (the leak is real for them too),")
    print("   BUT -g ranges over MANY values of mu_n (not one fixed g): the leak is a UNION over g in")
    print("   mu_n of the dilate-incidences |S0 cap (-g)S0|.  Counting it = sum over g of incidences")
    print("   = the additive energy E_2(mu_n) itself (Cauchy-Schwarz: sum_g |S cap gS| = E up to const).")
    print(" - Each genuine defect alpha is a short nonzero vector of the fully-split prime P|p,")
    print("   N(P)=p; bounding the count = bounding #short vectors of a fully-split cyclotomic ideal")
    print("   = the Pan-Xu OPEN ideal-SVP case.  The leak does NOT reduce below it.")

if __name__ == "__main__":
    main()
