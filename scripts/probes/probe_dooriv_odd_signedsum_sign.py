#!/usr/bin/env python3
"""
Door-(iv) Lane 1 — the SIGN profile of the odd signed deep sum A_r = Sum_{b!=0} eta_b^r in the THIN regime.

The open wall is A_r = q*W_r - n^r small at r~log q. The odd-profile entry (DISPROOF 1790) established
A_r = -n^r RIGID below d_odd (W_r=0). UNMAPPED: BEYOND d_odd (W_r>0), does A_r stay NEGATIVE (sign-rigid,
the rigidity just relaxing in magnitude) or does it FLIP SIGN / OSCILLATE in the thin regime? A sign
oscillation across odd r would be a genuine alternating-series structure an odd-r cancellation argument
could grip (distinct from magnitude); pure sign-definiteness would say the cancellation is monotone
magnitude-relaxation only. Either way it sharpens what an odd-r lever can assume.

PROBE: THIN mu_n only (beta>=4, p>>n^3), PROPER mu_n, NEVER n=q-1, multiple structured primes, exact real
arithmetic. Report sign(A_r) and |A_r|/n^r (=1 at rigidity floor, <1 when cancellation kicks in) across
ODD r up to ~2 log2 n + 5 (well past d_odd).
"""
import math

def is_prime(m):
    if m<2: return False
    for q in (2,3,5,7,11,13,17,19,23,29,31,37):
        if m%q==0: return m==q
    d=m-1; r=0
    while d%2==0: d//=2; r+=1
    for a in (2,3,5,7,11,13,17,19,23,29,31,37):
        x=pow(a,d,m)
        if x in (1,m-1): continue
        for _ in range(r-1):
            x=x*x%m
            if x==m-1: break
        else: return False
    return True

def factor_small(m):
    f={}; d=2
    while d*d<=m:
        while m%d==0: f[d]=f.get(d,0)+1; m//=d
        d+=1
    if m>1: f[m]=f.get(m,0)+1
    return f

def primitive_root(p):
    fac=list(factor_small(p-1).keys())
    for g in range(2,p):
        if all(pow(g,(p-1)//q,p)!=1 for q in fac): return g

def find_primes(t,mod,count):
    k0=max(1,round(t/mod)); found=[]
    for d in range(0,2000000):
        for s in (1,-1):
            kk=k0+s*d
            if kk<1: continue
            p=kk*mod+1
            if p>3 and is_prime(p) and p not in found:
                found.append(p)
                if len(found)>=count: return found
    return found

def subgroup(n,p):
    g=primitive_root(p); h=pow(g,(p-1)//n,p); e=[];x=1
    for _ in range(n): e.append(x); x=(x*h)%p
    return e

def periods(e,p):
    w=2*math.pi/p; cos=[math.cos(w*t) for t in range(p)]; out=[0.0]*p
    for b in range(p):
        s=0.0
        for x in e: s+=cos[(b*x)%p]
        out[b]=s
    return out

def run():
    print("Door-(iv) ODD signed-sum SIGN profile, THIN regime. A_r=Sum_{b!=0} eta_b^r.")
    print("report sign(A_r) and |A_r|/n^r (1=rigidity floor -n^r; <1 cancellation kicks in). ODD r.\n")
    for n in [16,32,64]:
        beta = 4.0 if n<64 else 3.7
        npr = 2 if n<64 else 1
        for p in find_primes(int(round(n**beta)),n,npr):
            ab=math.log(p)/math.log(n)
            e=subgroup(n,p); eta=periods(e,p)
            rmax=2*int(math.log2(n))+5
            cells=[]
            for r in range(3,rmax+1,2):
                A=sum(eta[b]**r for b in range(1,p))
                sgn='-' if A<0 else ('+' if A>0 else '0')
                cells.append(f"r{r}:{sgn}{abs(A)/n**r:.3f}")
            print(f"  n={n:3d} THIN beta={ab:.2f} p={p:>9d}: "+" ".join(cells))
        print()
    print("READING: if sign stays '-' at all odd r => sign-rigid (cancellation = monotone magnitude")
    print(" relaxation of -n^r, no alternation). if sign FLIPS => genuine odd-r oscillation (alternating")
    print(" structure an odd-r cancellation lever could exploit). |A_r|/n^r dropping below 1 = cancellation")
    print(" onset past d_odd. Maps the odd-r object's sign structure; no CORE/cancellation/capacity claim.")

if __name__=="__main__":
    run()
