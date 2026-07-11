#!/usr/bin/env python3
"""probe_cliff_coset_stability.py (#389, Fable): the worst-monomial coset-spectrum N_a is
q-INDEPENDENT (structural) for q above a band-dependent polynomial threshold -- dissolving
the 'Bourgain' framing for LOW-DEGREE bands, and localizing the wall to the HIGH-DEGREE cliff.

Monomial bad-set coset-CLOSURE is proven (#371 equivariance, any q). The coset COUNT #cosets:
- a=4 (m=1, degree 4): #cosets=6 FLAT for q>=193 (~n^1.5).  [structural, low threshold]
- a=3 (m=0, degree 3, capacity-adjacent cliff): #cosets=12,26,29,29,29 at q=193..12289 --
  STABILIZES at 29 for q>=~3089 (~n^3).  [structural, HIGHER threshold]
So the stability threshold grows with band degree d=k+m+1. For PRODUCTION RATE (k=rho*n), the
delta*-binding cliff band has degree d~rho*n, threshold ~n^{Theta(d)}=exp(Theta(n)) >> q=n^beta
=> Weil/structural-stability FAILS there: the genuine wall is the HIGH-DEGREE cliff census.
For fixed/low k (degree ~beta), the census is structural & coset-recursive => delta* EXACT.
RATE DICHOTOMY: low-rate (degree<=beta) delta* coset-recursive exact (Bourgain-free);
high-rate (degree~rho*n) cliff = the wall (threshold exp(n) > q)."""
def rou(p,n):
    for g in range(2,p):
        h=pow(g,(p-1)//n,p)
        if all(pow(h,d,p)!=1 for d in range(1,n)): return [pow(h,i,p) for i in range(n)]
def badcosets(D,u0,u1,p,a):
    n=len(D); bad=set()
    for g in range(p):
        w=[(u0[i]+g*u1[i])%p for i in range(n)]
        seen=set(); ok=False
        for i in range(n):
            for j in range(i+1,n):
                dx=(D[i]-D[j])%p
                if dx==0: continue
                al=((w[i]-w[j])*pow(dx,p-2,p))%p; be=(w[i]-al*D[i])%p
                if (al,be) in seen: continue
                seen.add((al,be))
                if sum(1 for t in range(n) if (al*D[t]+be)%p==w[t])>=a: ok=True;break
            if ok:break
        if ok: bad.add(g)
    Bnz=bad-{0};sn=set();k=0
    for b in sorted(Bnz):
        if b in sn:continue
        sn|={(b*h)%p for h in D};k+=1
    return k
if __name__=="__main__":
    n=16
    for a in (3,4,5):
        row=[]
        for p in (193,769,3089,6481,12289):
            if (p-1)%n: continue
            D=rou(p,n);u1=[pow(x,2,p) for x in D]
            row.append((p,max(badcosets(D,[pow(x,e,p) for x in D],u1,p,a) for e in range(3,n))))
        print(f"a={a} (deg {a}): #cosets vs q: "+"  ".join(f"{p}:{c}" for p,c in row))
