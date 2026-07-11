#!/usr/bin/env python3
"""
probe_407_ld_plateau_thinness_robust.py  (#444 LD-radius lane, rule-6 hardened)

Follow-up to probe_407_ld_plateau_thinness.py. That probe found:
  - the n-plateau QUANTIZATION (max_dir incidence = exactly n on a plateau, then drops) is
    thinness-essential (random domains give irregular non-plateau profiles), BUT
  - the resulting s* (= LD radius) is NOT robustly smaller for smooth vs random (n=8,k=2 smooth
    LARGER; n=8,k=3 EQUAL) on a SINGLE random draw + single prime.

This probe HARDENS that to a rule-6-clean verdict:
  (A) q-invariance: run smooth s* across MULTIPLE prize-band primes (incl. Fermat-type) — s* must be
      p-independent for the subgroup (the engine's claim).
  (B) random distribution: run MANY random draws (21), report the DISTRIBUTION of random s* (min/med/max),
      so the comparison smooth-vs-random is apples-to-apples, not a 1-draw artifact.
  (C) the PLATEAU-VALUE thinness claim: count how many random draws produce a clean "=n plateau" vs how
      many give irregular profiles — to confirm the quantization is genuinely subgroup-specific.

Conclusion target: either (i) smooth s* is ROBUSTLY <= min over random draws (=> mu_n suppresses the LD
radius, a live thinness-essential lever toward the floor), or (ii) smooth s* sits INSIDE the random
distribution (=> the LD radius is not thinness-separated even though the plateau quantization is — a
mapped wall, rule-4: the quantization is a red herring for s*).

Exact integer arithmetic, proper subgroup, prize band, never n=q-1. Python-only => axiom-clean trivially.
"""
import sys, random, math
from itertools import combinations
sys.path.insert(0,'scripts/probes')
from probe_407_ld_plateau_thinness import (is_prime, proot, factor, divdiff_k, in_rs,
                                           incidence_dir, s_star)

def primes_band(n, beta, count=3):
    base=n**beta; p=base-(base%n)+1
    if p<=n: p+=n
    out=[]
    while len(out)<count:
        if p%n==1 and is_prime(p): out.append(p)
        p+=n
    return out

def main():
    print("="*78)
    print("LD-radius s* + plateau thinness — ROBUST (multi-prime q-invariance + 21 random draws)")
    print("="*78)
    random.seed(20260615)
    for (n,k,beta) in [(8,2,4),(8,3,4),(8,2,5)]:
        budget=n
        sJ = k + math.sqrt(k*n)
        primes = primes_band(n,beta,3)
        # (A) smooth s* across primes
        smooth_sstars=[]
        smooth_prof=None
        for p in primes:
            g=proot(p); m=(p-1)//n; h=pow(g,m,p)
            assert pow(h,n,p)==1 and pow(h,n//2,p)!=1
            mu=[pow(h,i,p) for i in range(n)]
            s_s, prof_s = s_star(mu,k,p,budget)
            smooth_sstars.append((p,s_s))
            if smooth_prof is None: smooth_prof=prof_s
        q_invariant = len(set(s for _,s in smooth_sstars))==1
        # (B) 21 random draws at the FIRST prime
        p0=primes[0]
        rand_sstars=[]; rand_clean_plateau=0
        for _ in range(21):
            while True:
                dom_r=random.sample(range(1,p0), n)
                sset=set(dom_r)
                if not all((x*y%p0) in sset for x in dom_r[:3] for y in dom_r[:3]):
                    break
            s_r, prof_r = s_star(dom_r,k,p0,budget)
            rand_sstars.append(s_r)
            # clean "=n plateau": some s has maxI exactly == n (the quantization), then drops to <=budget
            vals=[v for v in prof_r.values() if v!='HEAVY']
            if any(v==n for v in vals):
                rand_clean_plateau+=1
        rmin,rmed,rmax=min(rand_sstars),sorted(rand_sstars)[len(rand_sstars)//2],max(rand_sstars)
        ss=smooth_sstars[0][1]
        print(f"\n--- n={n} k={k} beta~{beta} primes={primes} budget={budget} ---")
        print(f"    Johnson s_J={sJ:.3f} (delta*_J={1-sJ/n:.3f})")
        print(f"    SMOOTH s* across primes: {smooth_sstars}  q-invariant={q_invariant}")
        print(f"    SMOOTH plateau profile (p={primes[0]}): {smooth_prof}")
        print(f"    RANDOM s* over 21 draws (p={p0}): min={rmin} med={rmed} max={rmax}  dist={sorted(rand_sstars)}")
        print(f"    RANDOM draws with a clean '=n' plateau: {rand_clean_plateau}/21 (subgroup gives plateau by construction)")
        if ss < rmin:
            v="smooth s* BELOW the entire random distribution => mu_n SUPPRESSES LD radius (LIVE thinness lever)"
        elif ss > rmax:
            v="smooth s* ABOVE all random => mu_n HELPS adversary (anti-helpful, like n=8k=2)"
        else:
            v=f"smooth s*={ss} sits INSIDE random [{rmin},{rmax}] => LD radius NOT thinness-separated (mapped wall: plateau quantization is a red herring for s*)"
        print(f"    VERDICT: {v}")

if __name__=="__main__":
    main()
