#!/usr/bin/env python3
"""
#407 LANE B -- the CLEAN Q2 finding: the orbit-COMPRESSION ratio |bad|/N is the S-fold for SPARSE
pencils and ~1 (NO compression) for DENSE lines, p-INDEPENDENTLY.

The bad-COUNT |bad| at t=k+1 is ~#subsets for any line (union artifact) and is NOT the right metric.
The PRIZE quantity is the bad-ORBIT count N (BridgeLoop43: eps_mca = N*S/q^2).  The Action-Orbit
O(1)/|F| bound rests on the COMPRESSION  N = |bad|/S  (S = n/gcd(b-a,n) the orbit size), which holds
for the two-monomial pencil (badSet_orbit_closed) and is what makes N small.  Q2 asks whether the
general (dense) input also compresses.  This probe measures the compression ratio  r = |bad|/N
directly, across multiple primes, for SPARSE pencils vs DENSE lines:

  SPARSE pencil (a,b):  expect r = S = n/gcd(b-a,n)  (full orbit compression), p-INDEPENDENT.
  DENSE line:           if Q2's mechanism extended, r would be ~S too; if NOT, r ~ 1 (N ~ |bad|).

Reports r_sparse (per far pencil) and r_dense (random + superposition), and whether dense bad sets
are orbit-CLOSED under the generic action (the precondition for any compression).  Multi-prime,
proper subgroup mu_n < F_p*, far directions.  Uses the exact linear-in-alpha t=k+1 bad set.

FINDING (machine-checked, n=16, p in {40961,65537,786433}, interior delta):
  SPARSE: r = S EXACTLY (16,8,4...), orbit-closed=True, orbit count N p-INDEPENDENT (~250 @ k=4).
  DENSE : orbit-closed 0/40 ALWAYS; r -> 1 as p grows (1.98->1.57->1.04 @ k=4) = NO compression,
          N ~ |bad| grows with q. => the Action-Orbit O(1)/|F| compression is SPARSITY-EXCLUSIVE;
          Q2 is not a corollary of the action-orbit mechanism (it needs a genuine dense-count bound).
"""
import itertools, random, sys
from math import sqrt, gcd
from collections import Counter

def is_prime(m):
    if m<2: return False
    if m%2==0: return m==2
    i=3
    while i*i<=m:
        if m%i==0: return False
        i+=2
    return True

def find_gen(p,n):
    for g0 in range(2,p):
        w=pow(g0,(p-1)//n,p)
        if pow(w,n,p)==1 and all(pow(w,n//q,p)!=1 for q in (2,3,5,7) if n%q==0): return w
    raise RuntimeError

def domain(w,n,p): return [pow(w,i,p) for i in range(n)]

def precompute_divdiff(D,p,k):
    out=[];N=len(D)
    for sub in itertools.combinations(range(N),k+1):
        xs=[D[i] for i in sub]; W=[]
        for j in range(k+1):
            den=1
            for l in range(k+1):
                if l!=j: den=den*((xs[j]-xs[l])%p)%p
            W.append(pow(den,p-2,p))
        out.append((sub,W))
    return out

def bad_set(u,v,p,dd):
    BAD=set()
    for sub,W in dd:
        A=0;B=0
        for idx,j in enumerate(sub):
            A=(A+W[idx]*u[j])%p; B=(B+W[idx]*v[j])%p
        if B!=0: BAD.add((-A*pow(B,p-2,p))%p)
        elif A%p==0: return None
    return BAD

def closed_and_orbits(BAD,p,mult):
    BADset=BAD
    closed=all((a*mult%p) in BADset for a in BAD)
    seen=set();N=0
    for a in BAD:
        if a in seen: continue
        N+=1;cur=a
        while cur not in seen:
            seen.add(cur);cur=cur*mult%p
    return closed,N

def main():
    print("="*100)
    print("#407 LANE B -- orbit COMPRESSION ratio r=|bad|/N : SPARSE (=S) vs DENSE (~1), p-independent")
    print("="*100)
    print("r=S => Action-Orbit O(1)/|F| compression works; r~1 => NO compression (N~|bad|).\n")
    configs=[(16,4,40961),(16,4,65537),(16,4,786433),(16,8,40961),(16,8,65537)]
    rng=random.Random(20260614)
    for (n,k,p) in configs:
        if not is_prime(p) or (p-1)%n!=0: print(f"skip {n},{p}");continue
        w=find_gen(p,n);D=domain(w,n,p);rho=k/n
        dd=precompute_divdiff(D,p,k)
        far=[e for e in range(k,n) if (e%n) not in (0,n//2)]
        pencils=[(a,b) for a in far for b in far if a!=b and (b-a)%n not in (0,n//2)]
        print(f"--- n={n} k={k} rho={rho:.3f} p={p}  (t=k+1, delta={1-(k+1)/n:.3f}) ---")
        sample=pencils[:5]
        for (a,b) in sample:
            u=[pow(x,a,p) for x in D];v=[pow(x,b,p) for x in D]
            mult=pow(w,(b-a)%n,p)
            S=n//gcd((b-a)%n,n)
            BAD=bad_set(u,v,p,dd)
            if BAD is None:
                print(f"   sparse ({a},{b}) S={S}: DEGENERATE (full-bad)"); continue
            cl,N=closed_and_orbits(BAD,p,mult)
            r=len(BAD)/N if N else 0
            print(f"   sparse ({a},{b}) S={S:2d}: |bad|={len(BAD):5d} N={N:5d} r=|bad|/N={r:5.2f} closed={cl}")
        def mk_rand(): return [rng.randrange(p) for _ in range(n)],[rng.randrange(p) for _ in range(n)]
        def mk_super():
            J=max(2,n//4)
            def word():
                ws=[0]*n
                for _ in range(J):
                    a=rng.choice(far);c=rng.randrange(1,p)
                    for i in range(n): ws[i]=(ws[i]+c*pow(D[i],a,p))%p
                return ws
            return word(),word()
        for fam,maker in (("rand",mk_rand),("super",mk_super)):
            rs=[];ns=[];closes=0;tot=0
            for _ in range(40):
                u,v=maker();BAD=bad_set(u,v,p,dd)
                if BAD is None: continue
                cl,N=closed_and_orbits(BAD,p,w)
                tot+=1; closes+= (1 if cl else 0)
                rs.append(len(BAD)/N if N else 0); ns.append(N)
            if tot:
                print(f"   DENSE {fam:5s}: mean |bad|/N r={sum(rs)/len(rs):5.2f} (S would be up to {n}), "
                      f"mean N={sum(ns)/len(ns):7.1f}, orbit-closed {closes}/{tot}")
        print(); sys.stdout.flush()

if __name__=="__main__":
    main()
