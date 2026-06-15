#!/usr/bin/env python3
"""
#407 lane #0 (BIND / Sidon-bootstrap) -- the DEPTH-FRACTION + THINNESS-ESSENTIALITY crux.

State of the board (existing probe_407_sidon_thin_regime_mitm.py, verified): in the THIN prize
regime (p >= n^4, mu_n = 2-power subgroup), the smallest non-antipodal unsigned zero-sum
sum_{i in S} zeta^i == 0 (mod p) has size:
    n=16, beta=4 prize prime: NONE (BIND holds to full depth n/2=8)
    n=32, beta=4 prize prime: r_min = 10-11  (> log2 n = 5, but < n/2 = 16)
The OPEN crux (decides the B_inf <- B_{log n} Sidon bootstrap): does the depth FRACTION
phi(n) = r_min/(n/2) head to a positive constant < 1 (=> a constant-fraction spurious zero-sum
survives => BIND is FALSE as stated => bootstrap GAP is real) or to 1 (=> BIND plausibly holds)?
And -- the rule-3 gate that KILLED the BHBI lever -- is r_min THINNESS-ESSENTIAL (mu_n's r_min
strictly larger than a random thin-density 32-subset's) or thickness-invariant pigeonhole?

THIS PROBE adds three things the board does not have:
  (A) beta-SWEEP at fixed n=32: is r_min(beta) increasing in thinness (beta), or beta-stable?
  (B) THIN-vs-RANDOM control at n=32 prize prime: rule-3 essentiality gate.
  (C) n=64 thin-regime r_min via randomized MITM (the missing 3rd depth-fraction data point).

HONESTY: antipodal subsets (unions of {i,i+n/2}) excluded as trivial. mu_n = n-th roots of unity,
n=2^a, p == 1 mod n, proper subgroup, NEVER n=q-1. Random control = a random size-n subset of
F_p^* (same density n/p) with NO multiplicative structure. Exact integer arithmetic mod p.
r_min reported is the SMALLEST non-antipodal unsigned zero-sum found by exhaustive (n<=32) or
randomized-restart (n=64) MITM; "NONE" means none up to n/2.
"""
import sys, random
from collections import defaultdict
from math import log2

def is_prime(n):
    if n < 2: return False
    if n % 2 == 0: return n == 2
    d = 3
    while d*d <= n:
        if n % d == 0: return False
        d += 2
    return True

def primitive_root(p):
    if p == 2: return 1
    phi = p-1; facs=set(); m=phi; d=2
    while d*d <= m:
        while m % d == 0: facs.add(d); m//=d
        d += 1
    if m>1: facs.add(m)
    for g in range(2,p):
        if all(pow(g,phi//q,p)!=1 for q in facs): return g
    raise RuntimeError

def zeta_powers(p,n):
    g = primitive_root(p); z = pow(g,(p-1)//n,p)
    # sanity: z has order exactly n (proper subgroup, mu_n not q-1)
    assert pow(z,n,p)==1 and all(pow(z,n//q,p)!=1 for q in [2] if n%q==0), "zeta not order n"
    return [pow(z,i,p) for i in range(n)]

def find_prize_prime(n, beta, skip=0, want_odd=None):
    """Smallest prime p == 1 mod n with p >= n^beta (skip 'skip' of them).
       want_odd: True => m=(p-1)/n odd; False => even; None => any."""
    target = int(n**beta)
    p = target + ((n-(target%n))%n) + 1
    found=0
    while p < target*64 + 10**7:
        if is_prime(p) and p % n == 1:
            m=(p-1)//n
            ok = (want_odd is None) or (m%2==1)==want_odd
            if ok:
                if found==skip: return p
                found+=1
        p += n
    return None

def antipodal(Sset, n):
    h=n//2
    return all(((i+h)%n) in Sset for i in Sset)

def smallest_zerosum_exact(vals, n, p):
    """Exact MITM over an index set 0..n-1 with weight vals[i] in F_p. Smallest non-antipodal
       (in the index sense) unsigned zero-sum subset, |S|>=2. Antipodality defined on indices."""
    h=n//2
    A=list(range(0,h)); B=list(range(h,n))
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

def smallest_zerosum_random(vals, n, p, restarts=40, half_splits=8):
    """Randomized MITM for n=64: split into 4 quarters, build two halves by random quarter pairing,
       and meet in the middle on each pairing. vals indexed 0..n-1, antipodality on indices.
       Returns smallest non-antipodal zero-sum found (UPPER bound on true r_min)."""
    h=n//2
    best=None
    idxs=list(range(n))
    for _ in range(restarts):
        random.shuffle(idxs)
        A=idxs[:h]; B=idxs[h:]
        # cap A-table size: if h>20, subsample A masks (Monte-Carlo). h=32 -> 2^32 too big.
        # Instead: random sparse masks on A up to weight wcap, hash, then random B masks.
        Atab=defaultdict(list)
        # enumerate low-weight A subsets up to weight wa
        wa = min(h, 12)
        import itertools as it
        # sample: all subsets of A of size <= 6 (C(32,6)~9e5) is borderline; use size<=5 + random size 6..wa
        for sz in range(0, 6):
            for comb in it.combinations(A, sz):
                s=sum(vals[i] for i in comb)%p
                Atab[s].append((frozenset(comb),sz))
        # random larger A-subsets
        for _ in range(200000):
            sz=random.randint(6,wa)
            comb=frozenset(random.sample(A,sz))
            s=sum(vals[i] for i in comb)%p
            Atab[s].append((comb,sz))
        # B side: sizes 0..5 exhaustive-ish + random
        for sz in range(0,6):
            for comb in it.combinations(B,sz):
                s=sum(vals[i] for i in comb)%p
                need=(-s)%p
                for (Aset,Asz) in Atab.get(need,()):
                    tot=Aset|set(comb); tsz=Asz+sz
                    if tsz<2: continue
                    if best is not None and tsz>=best[0]: continue
                    if antipodal(tot,n): continue
                    best=(tsz,tot)
        for _ in range(200000):
            sz=random.randint(6,12)
            comb=frozenset(random.sample(B,sz))
            s=sum(vals[i] for i in comb)%p
            need=(-s)%p
            for (Aset,Asz) in Atab.get(need,()):
                tot=Aset|comb; tsz=Asz+sz
                if tsz<2: continue
                if best is not None and tsz>=best[0]: continue
                if antipodal(tot,n): continue
                best=(tsz,tot)
    if best is None: return None,None
    return best[0],sorted(best[1])

def main():
    random.seed(40)
    print("="*90)
    print("BIND depth-fraction + thinness-essentiality crux (#407 lane 0)")
    print("="*90)

    # ---------- (A) beta-sweep at fixed n=32 ----------
    print("\n(A) beta-SWEEP at n=32 (does r_min depend on thinness beta, or is it beta-stable?)")
    print(f"{'beta':>5} {'p':>16} {'p^.25/n':>9} {'r_min':>6} {'r_min/(n/2)':>12}")
    n=32
    for beta in (4.0, 4.5, 5.0, 5.5, 6.0):
        p=find_prize_prime(n,beta,want_odd=True)
        if p is None: continue
        zp=zeta_powers(p,n)
        r,S=smallest_zerosum_exact(zp,n,p)
        frac = (r/(n/2)) if r else None
        rs = str(r) if r else "NONE"
        fs = f"{frac:.3f}" if frac else "  -"
        print(f"{beta:>5.1f} {p:>16} {p**0.25/n:>9.2f} {rs:>6} {fs:>12}")

    # ---------- (B) THIN vs RANDOM control at n=32 prize prime (rule-3 gate) ----------
    print("\n(B) THIN mu_32 vs RANDOM thin-density 32-subset at the SAME prize prime (rule-3 gate)")
    print("    If r_min(thin) >> r_min(random): thinness-essential. If ~equal: pigeonhole (lever dead).")
    print(f"{'beta':>5} {'p':>16} {'r_min thin':>11} {'r_min random (median/5)':>24}")
    n=32
    for beta in (4.0, 5.0):
        p=find_prize_prime(n,beta,want_odd=True)
        zp=zeta_powers(p,n)
        rt,_=smallest_zerosum_exact(zp,n,p)
        # random control: 32 distinct nonzero residues, no mult structure, antipodality on a
        # FORMAL index pairing i<->i+16 (random sets have no real antipodes, so this is the
        # honest analogue: exclude formally-antipodal index subsets exactly as for mu_n).
        rr=[]
        for seed in range(5):
            random.seed(1000+seed)
            vals=random.sample(range(1,p),n)
            r,_=smallest_zerosum_exact(vals,n,p)
            rr.append(r if r else n//2+1)
        rr.sort()
        med=rr[len(rr)//2]
        print(f"{beta:>5.1f} {p:>16} {str(rt) if rt else 'NONE':>11} "
              f"{str(rr).replace(' ',''):>24}  (median {med})")

    # ---------- (C) n=64 thin-regime r_min (randomized MITM upper bound) ----------
    print("\n(C) n=64 thin-regime r_min (randomized MITM => UPPER bound on true r_min)")
    print("    Depth-fraction trend: n=16 -> NONE(phi=1.0), n=32 -> ~10/16=0.63, n=64 -> ?")
    print(f"{'n':>4} {'beta':>5} {'p':>18} {'r_min (UB)':>11} {'phi=r/(n/2)':>12}")
    n=64
    p=find_prize_prime(n,4.0,want_odd=True)
    zp=zeta_powers(p,n)
    r,S=smallest_zerosum_random(zp,n,p,restarts=4)
    frac=(r/(n/2)) if r else None
    print(f"{n:>4} {4.0:>5.1f} {p:>18} {str(r) if r else 'NONE(UB)':>11} "
          f"{f'{frac:.3f}' if frac else '  -':>12}")
    if S: print(f"     witness S (|S|={len(S)}) = {S}")

    print("\nINTERPRETATION:")
    print(" (A) r_min rising with beta => the obstruction-free depth is THINNESS-driven (good for BIND).")
    print("     r_min beta-flat => depth set by something beta-independent.")
    print(" (B) thin r_min >> random => thinness-essential (rule-3 PASS, unlike BHBI). thin~random => dead.")
    print(" (C) phi(64) vs phi(32)=0.63, phi(16)=1.0: if phi DECREASING toward a const<1 => bootstrap GAP")
    print("     real (BIND false at const fraction). If phi staying high/->1 => BIND plausibly holds.")

if __name__=="__main__":
    main()
