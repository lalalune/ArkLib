#!/usr/bin/env python3
"""
#407 LANE D -- GENUINE-RS orbit count K(delta) growth n=8 -> n=16, the DECISIVE escape/collapse.

The OPEN ITEM: does Action-Orbit give a genuine O(1)/|F| on PLAIN RS over mu_n in the WINDOW
INTERIOR, or collapse to BGK?  Mechanism (ActionOrbitFRI.badSet_orbit_closed, axiom-clean):
the bad-alpha set of h_alpha(z)=z^a+alpha z^b on mu_n is a union of <w^{b-a}>-orbits, each of
size S = n/gcd(b-a,n).  So  K(delta) = L(delta)/S  where L = #bad scalars at radius delta.
Escape <=> K = O(1) as n grows at FIXED window depth.  Collapse <=> K grows with n.

The K-growth-LAW probe answered this for the |Sigma_r| value-spectrum PROXY (K exploded,
x19.5 per doubling).  But |Sigma_r| over-counts: most distinct r-fold sums are NOT realizable
as a deg<k codeword agreement (the realizability gate).  So we must measure the GENUINE-RS K.

Here we compute L, S, K on ACTUAL Reed-Solomon agreement (exact deg<k via Lagrange, full
alpha-sweep over F_p) for n=8 AND n=16 at the SAME window depth (the first interior threshold
t = ceil(sqrt(rho)*n)+1, i.e. one step past Johnson), to see whether genuine-RS K is bounded
or grows.  We use the SMALLEST p=1 mod n that keeps mu_n a proper subgroup, to bound the sweep.

To make n=16 feasible (alpha-sweep is O(p * C(n,k) * n)) we use moderate p and k=2 (rate small)
so best_agreement enumerates only C(16,2)=120 subsets per alpha.  We report K at the deepest
interior threshold reachable, for BOTH n, and the n=8->16 growth ratio.
"""
import itertools
from math import gcd, sqrt, ceil
from collections import Counter

def is_prime(m):
    if m<2: return False
    if m%2==0: return m==2
    i=3
    while i*i<=m:
        if m%i==0: return False
        i+=2
    return True

def primes_1_mod_n(n, lo, cap):
    out=[]; p=lo|1
    while len(out)<cap:
        if (p-1)%n==0 and is_prime(p): out.append(p)
        p+=2
    return out

def find_gen(p,n):
    for g0 in range(2,p):
        w=pow(g0,(p-1)//n,p)
        if pow(w,n,p)==1 and all(pow(w,n//q,p)!=1 for q in (2,3,5,7) if n%q==0):
            return w
    raise RuntimeError

def best_agreement(H, vals, p, k):
    n=len(H); best=0
    for sub in itertools.combinations(range(n),k):
        bx=[H[i] for i in sub]; by=[vals[i] for i in sub]
        def interp(x):
            tot=0
            for j in range(k):
                num=by[j]%p; den=1
                for l in range(k):
                    if l!=j:
                        num=num*((x-bx[l])%p)%p; den=den*((bx[j]-bx[l])%p)%p
                tot=(tot+num*pow(den,p-2,p))%p
            return tot
        cnt=sum(1 for i in range(n) if interp(H[i])==vals[i]%p)
        if cnt>best: best=cnt
        if best==n: break
    return best

def orbit_K(p,n,k,a,b,t):
    w=find_gen(p,n); H=[pow(w,i,p) for i in range(n)]
    Ha=[pow(x,a,p) for x in H]; Hb=[pow(x,b,p) for x in H]
    d=(b-a)%n; mult=pow(w,d,p); S=n//gcd(d if d else n,n)
    BAD=set()
    for alpha in range(1,p):
        vals=[(Ha[i]+alpha*Hb[i])%p for i in range(n)]
        if best_agreement(H,vals,p,k)>=t: BAD.add(alpha)
    closed=all((alpha*mult)%p in BAD for alpha in BAD)
    seen=set(); K=0
    for alpha in BAD:
        if alpha in seen: continue
        K+=1; cur=alpha
        while cur not in seen:
            seen.add(cur); cur=(cur*mult)%p
    return len(BAD), S, K, closed

def main():
    print("="*84)
    print("#407 LANE D -- GENUINE-RS orbit count K growth, n=8 vs n=16, fixed window depth")
    print("="*84)
    print("Escape <=> K=O(1) across n at fixed depth.  Collapse <=> K grows.\n")
    # rho = k/n = 2/n. far pencil a,b>=k, gcd(b-a,n) gives S.
    results={}
    for (n,p) in [(8,409),(16,193)]:
        k=2; rho=k/n; dJ=1-sqrt(rho)
        # Johnson agreement ~ sqrt(rho)*n; first interior threshold t = floor(sqrt(rho)*n)+1
        tJ=int(sqrt(rho)*n)
        # pick far pencil avoiding x^{n/2}
        a=b=None
        for aa in range(k,n):
            for bb in range(k,n):
                if aa==bb: continue
                dd=(bb-aa)%n
                if dd==0 or dd==n//2: continue
                a,b=aa,bb; break
            if a is not None: break
        print(f"--- n={n} k={k} rho={rho:.3f} p={p} pencil(z^{a}+a*z^{b}) Johnson_agr~{sqrt(rho)*n:.1f} dJ={dJ:.3f} ---")
        print(f"  {'t(agr)':>7} {'delta':>7} {'L=|bad|':>8} {'S':>3} {'K':>4} {'closed':>7} {'region':>9}")
        Kfirst=None
        for t in range(tJ+1, n+1):
            delta=1-t/n
            L,S,K,cl=orbit_K(p,n,k,a,b,t)
            reg="INTERIOR" if delta>dJ+1e-9 else "Johnson"
            if L==0 and Kfirst is not None:
                print(f"  {t:>7} {delta:7.3f} {L:>8} {S:>3} {K:>4} {str(cl):>7} {reg:>9}")
                continue
            print(f"  {t:>7} {delta:7.3f} {L:>8} {S:>3} {K:>4} {str(cl):>7} {reg:>9}")
            if Kfirst is None and L>0 and reg=="INTERIOR":
                Kfirst=(t,delta,L,S,K)
        results[n]=Kfirst
        print()

    print("="*84)
    print("VERDICT: genuine-RS orbit count K at the FIRST interior threshold, n=8 vs n=16:")
    for n in [8,16]:
        r=results.get(n)
        if r: print(f"  n={n}: first-interior t={r[0]} delta={r[1]:.3f}  L={r[2]} S={r[3]} K={r[4]}")
        else: print(f"  n={n}: no interior bad set found at this p")
    if results.get(8) and results.get(16):
        K8=results[8][4]; K16=results[16][4]
        print(f"\n  K(n=8)={K8}, K(n=16)={K16}, growth ratio = {K16/K8 if K8 else float('inf'):.2f}")
        print(f"  => {'K BOUNDED (escape candidate)' if K16<=2*K8 else 'K GROWS with n (collapse to BGK)'}")

if __name__=="__main__":
    main()
