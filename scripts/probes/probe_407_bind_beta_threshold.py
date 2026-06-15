#!/usr/bin/env python3
"""
#407 lane 0 -- BIND beta-THRESHOLD: the decisive follow-up to the depth-fraction probe.

Established (probe_407_bind_depth_fraction.py, EXACT MITM):
  At the thinness BOUNDARY beta=4.0 (p ~ n^4, p^{1/4}/n ~ 1):
    n=16: r_min = NONE (full depth)   phi = 1.0
    n=32: r_min = 11                  phi = 0.69
    n=64: r_min <= 8 (rand UB)        phi <= 0.25
  And at n=32, going to beta>=4.5 makes r_min = NONE (BIND full depth).
  And THINNESS-ESSENTIAL: thin r_min(11) > random median(6) at n=32 beta=4.0.

THE DECISIVE QUESTION (decides bootstrap gap real vs BIND holds):
  Define beta*(n) = the smallest beta at which BIND holds to FULL depth n/2 (no non-antipodal
  zero-sum at all). The in-tree PROVEN depth-2 result needs p > 4^phi(n) = 2^n, i.e. beta > n/log2(n)
  -- which GROWS with n (beta>4 at n=16, >6.4 at n=32, >10.7 at n=64). The prize regime is beta in
  [4,5] FIXED. So the question: does the EMPIRICAL beta*(n) for FULL depth stay <= 5 (bounded, prize
  reachable => BIND plausibly holds at the prize) or GROW like n/log2 n (=> at fixed prize beta in
  [4,5], BIND fails for large n => gap real)?

This probe measures beta*(n) exactly for n=16,32 (full MITM), and brackets it for n=64 (randomized
UB: if even the UPPER bound on r_min is < n/2 at a given beta, BIND FAILS at that beta -- a SOUND
one-sided conclusion). Comparison vs the proven threshold n/log2(n).

HONESTY: r_min from randomized search is an UPPER bound; "r_min < n/2 found" => BIND FAILS (sound);
"NONE found" at n=64 is NOT a proof BIND holds (search may miss). So at n=64 we only report SOUND
failures (r_min found < n/2). Proper subgroup mu_n, p==1 mod n, never n=q-1, exact integer mod p.
"""
import random
from collections import defaultdict
from math import log2

def is_prime(n):
    if n<2: return False
    if n%2==0: return n==2
    d=3
    while d*d<=n:
        if n%d==0: return False
        d+=2
    return True

def primitive_root(p):
    if p==2: return 1
    phi=p-1; facs=set(); m=phi; d=2
    while d*d<=m:
        while m%d==0: facs.add(d); m//=d
        d+=1
    if m>1: facs.add(m)
    for g in range(2,p):
        if all(pow(g,phi//q,p)!=1 for q in facs): return g
    raise RuntimeError

def zeta_powers(p,n):
    g=primitive_root(p); z=pow(g,(p-1)//n,p)
    assert pow(z,n,p)==1 and pow(z,n//2,p)!=1
    return [pow(z,i,p) for i in range(n)]

def find_prize_prime(n,beta,want_odd=True):
    target=int(n**beta)
    p=target+((n-(target%n))%n)+1
    while p<target*64+10**7:
        if is_prime(p) and p%n==1:
            m=(p-1)//n
            if (want_odd is None) or (m%2==1)==want_odd:
                return p
        p+=n
    return None

def antipodal(Sset,n):
    h=n//2
    return all(((i+h)%n) in Sset for i in Sset)

def smallest_zerosum_exact(vals,n,p):
    h=n//2; A=list(range(h)); B=list(range(h,n))
    Atab=defaultdict(list)
    for mask in range(1<<len(A)):
        s=0; Sset=set(); mm=mask; idx=0
        while mm:
            if mm&1: s+=vals[A[idx]]; Sset.add(A[idx])
            mm>>=1; idx+=1
        Atab[s%p].append((frozenset(Sset),len(Sset)))
    best=None
    for mask in range(1<<len(B)):
        s=0; Sset=set(); mm=mask; idx=0
        while mm:
            if mm&1: s+=vals[B[idx]]; Sset.add(B[idx])
            mm>>=1; idx+=1
        need=(-s)%p
        for (Aset,Asz) in Atab.get(need,()):
            tot=Aset|Sset; tsz=Asz+len(Sset)
            if tsz<2: continue
            if best is not None and tsz>=best[0]: continue
            if antipodal(tot,n): continue
            best=(tsz,tot)
    if best is None: return None,None
    return best[0],sorted(best[1])

def rand_zerosum_ub(vals,n,p,restarts=6):
    """Randomized UB on smallest non-antipodal zero-sum for n=64. SOUND only when it FINDS one."""
    import itertools as it
    h=n//2; best=None; idxs=list(range(n))
    for _ in range(restarts):
        random.shuffle(idxs); A=idxs[:h]; B=idxs[h:]
        Atab=defaultdict(list)
        for sz in range(0,6):
            for comb in it.combinations(A,sz):
                Atab[sum(vals[i] for i in comb)%p].append((frozenset(comb),sz))
        for _ in range(150000):
            sz=random.randint(6,12); comb=frozenset(random.sample(A,sz))
            Atab[sum(vals[i] for i in comb)%p].append((comb,sz))
        for sz in range(0,6):
            for comb in it.combinations(B,sz):
                need=(-sum(vals[i] for i in comb))%p
                for (Aset,Asz) in Atab.get(need,()):
                    tot=Aset|set(comb); tsz=Asz+sz
                    if tsz<2: continue
                    if best is not None and tsz>=best[0]: continue
                    if antipodal(tot,n): continue
                    best=(tsz,tot)
        for _ in range(150000):
            sz=random.randint(6,12); comb=frozenset(random.sample(B,sz))
            need=(-sum(vals[i] for i in comb))%p
            for (Aset,Asz) in Atab.get(need,()):
                tot=Aset|comb; tsz=Asz+sz
                if tsz<2: continue
                if best is not None and tsz>=best[0]: continue
                if antipodal(tot,n): continue
                best=(tsz,tot)
    if best is None: return None,None
    return best[0],sorted(best[1])

def main():
    random.seed(7)
    print("="*92)
    print("BIND beta-THRESHOLD beta*(n): does it stay bounded (prize-reachable) or grow with n?")
    print("="*92)
    print("Proven depth-2 threshold (sidonModNeg_rootsOfUnity): p > 2^n  <=>  beta > n/log2(n).")
    print(f"  n=16: proven-thr beta>{16/4:.2f}   n=32: >{32/5:.2f}   n=64: >{64/6:.2f}   "
          f"(GROWS like n/log2 n)\n")

    # n=16, 32 EXACT: find beta*(full depth) by sweeping beta upward.
    for n in (16,32):
        print(f"--- n={n} EXACT (beta* = smallest beta with r_min=NONE, i.e. full-depth BIND) ---")
        print(f"{'beta':>5} {'p':>14} {'p^.25/n':>9} {'r_min':>6} {'full-depth?':>11}")
        bstar=None
        b=4.0
        while b<=8.01:
            p=find_prize_prime(n,b)
            zp=zeta_powers(p,n)
            r,_=smallest_zerosum_exact(zp,n,p)
            full = (r is None)
            if full and bstar is None: bstar=b
            print(f"{b:>5.2f} {p:>14} {p**0.25/n:>9.2f} {str(r) if r else 'NONE':>6} {str(full):>11}")
            b+=0.5
        print(f"   => empirical beta*({n}) for full-depth BIND = {bstar}   "
              f"(proven-suff threshold n/log2 n = {n/log2(n):.2f})\n")

    # n=64: SOUND failures only. If r_min UB < n/2 found at beta, BIND FAILS at that beta (sound).
    print("--- n=64 (SOUND failures only: a found r_min<n/2 PROVES BIND fails at that beta) ---")
    print(f"{'beta':>5} {'p':>16} {'p^.25/n':>9} {'r_min UB':>9} {'BIND fails? (sound)':>20}")
    n=64
    for b in (4.0,4.5,5.0,5.5,6.0,7.0,8.0):
        p=find_prize_prime(n,b)
        zp=zeta_powers(p,n)
        r,S=rand_zerosum_ub(zp,n,p,restarts=5)
        fails = (r is not None and r < n//2)
        print(f"{b:>5.2f} {p:>16} {p**0.25/n:>9.2f} {str(r) if r else 'none-found':>9} "
              f"{str(fails) if r else 'inconclusive':>20}")
    print("\nVERDICT LOGIC:")
    print(" - If beta*(n) for full-depth BIND stays <= ~5 (bounded) AND n=64 stops failing by beta~5:")
    print("     BIND holds throughout the prize regime beta in [4,5] for large n => bootstrap PLAUSIBLE.")
    print(" - If beta*(n) GROWS with n (tracks n/log2 n) AND n=64 still SOUND-FAILS at beta=4,5:")
    print("     at FIXED prize beta in [4,5], BIND FAILS for large n => bootstrap GAP is REAL.")

if __name__=="__main__":
    main()
