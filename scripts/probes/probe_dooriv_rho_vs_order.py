#!/usr/bin/env python3
"""
Door-IV Lane 1 PROBE — does the worst-b coherence rho(b) depend on the multiplicative ORDER of b?

Deconfliction: prior worst-b structure probes tested the coset INDEX (additive: a2ad4130b;
multiplicative QR: 4444b7fe0) and refinement geometry (e5c3d8652 + g55 sign-mass). NONE tested
whether rho(b) (the index-2 coset-half coherence, the brief's localized object) correlates with the
MULTIPLICATIVE ORDER of b in F_p* — a different axis. If small-order b (e.g. b in a small subgroup,
roots of unity) systematically gives LOWER rho (more cancellation/slack), an anti-concentration
method could target them; if rho is order-blind, that axis is dead.

Object: rho(b) = |A+B|/(|A|+|B|) where A,B are the two index-2 coset-half period sums of
S(b)=sum_{x in mu_n} e_p(b x). We bucket b by ord(b) | (p-1) and report mean rho per order bucket,
PLUS the rho AT the worst-b (argmax|S|) tagged with its order. Question: is rho@worst lower for
special orders, or is the worst-b order generic?

EXACT trig; PROPER mu_n; p>>n^3; structured primes; never n=q-1.
"""
import math
from collections import defaultdict

def is_prime(p):
    if p<2: return False
    for q in (2,3,5,7,11,13,17,19,23,29,31,37,41,43):
        if p%q==0: return p==q
    d=p-1;r=0
    while d%2==0: d//=2;r+=1
    for a in (2,3,5,7,11,13,17,19,23,29,31,37):
        if a%p==0: continue
        x=pow(a,d,p)
        if x==1 or x==p-1: continue
        ok=False
        for _ in range(r-1):
            x=x*x%p
            if x==p-1: ok=True;break
        if not ok: return False
    return True

def find_primes(n,count,beta=4):
    out=[];k=(n**beta)//n+1
    while len(out)<count:
        p=k*n+1
        if is_prime(p): out.append(p)
        k+=1
    return out

def primitive_root(p):
    phi=p-1;factors=set();m=phi;f=2
    while f*f<=m:
        if m%f==0:
            factors.add(f)
            while m%f==0: m//=f
        f+=1
    if m>1: factors.add(m)
    for g in range(2,p):
        if all(pow(g,phi//q,p)!=1 for q in factors): return g
    raise RuntimeError

def mult_order(b,p,phi,phi_factors):
    # order divides phi; reduce by prime factors
    o=phi
    for q in phi_factors:
        while o%q==0 and pow(b,o//q,p)==1:
            o//=q
    return o

def analyze(n,p,full_scan):
    g0=primitive_root(p)
    g=pow(g0,(p-1)//n,p)
    elems=[1]
    for _ in range(n-1): elems.append(elems[-1]*g%p)
    # index-2 coset halves: H0 = <g^2> = even powers, H1 = odd powers (g * H0).
    half0=[elems[2*i] for i in range(n//2)]
    half1=[elems[2*i+1] for i in range(n//2)]
    tp=2*math.pi/p
    cos=math.cos; sin=math.sin
    def csum(half,b):
        re=0.0;im=0.0
        for x in half:
            a=tp*((b*x)%p); re+=cos(a); im+=sin(a)
        return complex(re,im)
    phi=p-1
    # phi prime factors
    pf=set(); m=phi; f=2
    while f*f<=m:
        if m%f==0:
            pf.add(f)
            while m%f==0: m//=f
        f+=1
    if m>1: pf.add(m)
    k=(p-1)//n
    # codex P2 fix: rho is constant on mu_n-cosets while order varies WITHIN a coset, so bucketing
    # coset-REPS by the rep's order is representative-dependent. To make the rho-vs-order measurement
    # rep-INDEPENDENT we scan EVERY b in F_p* (full_scan) and bucket each b by its TRUE element order.
    # This way every order class is fully represented (each coset contributes its rho to ALL the
    # order buckets its n members fall into). NB: the resulting flatness is the EXPECTED CONSEQUENCE
    # of coset-invariance (which the Lean brick _DoorIVCoherenceOrderBlind proves); the probe's
    # independent content is (i) confirming rho really is coset-invariant for THIS statistic and
    # (ii) the worst-b (rho=1) order being generic. For large p we cap the full scan and flag it.
    buckets=defaultdict(lambda:[0.0,0])  # order_class -> [sum_rho, count]
    best_absS=-1.0; rho_at_best=None; ord_at_best=None
    scanN = (p-1) if full_scan else min(k,4000)
    b=1
    for t in range(scanN):
        b = t+1 if full_scan else b   # full: b=1..p-1 ; sampled: b=g0^t coset reps
        A=csum(half0,b); B=csum(half1,b)
        S=A+B; absS=abs(S)
        den=abs(A)+abs(B)
        rho=absS/den if den>0 else 1.0
        o=mult_order(b,p,phi,pf)
        frac=o/phi
        if frac<=0.05: cls="tiny(<=.05phi)"
        elif frac<=0.5: cls="small(<=.5phi)"
        else: cls="large(>.5phi)"
        buckets[cls][0]+=rho; buckets[cls][1]+=1
        if absS>best_absS:
            best_absS=absS; rho_at_best=rho; ord_at_best=o
        if not full_scan: b=b*g0%p
    return buckets,best_absS,rho_at_best,ord_at_best,phi,scanN,k,full_scan

def main():
    print("# Door-IV index-2 coset-half coherence rho(b) vs multiplicative ORDER of b")
    print("# rep-INDEPENDENT: FULL scan over ALL b in F_p* (small n), each b bucketed by its TRUE order.")
    print("# flatness across order buckets = EXPECTED consequence of coset-invariance (Lean-proven);")
    print("# independent content = coset-invariance holds for this rho + worst-b (rho=1) order generic.")
    print()
    # n=16 small enough for a FULL F_p* scan (p~65k). Larger n: sampled coset-rep scan (flagged).
    for n,full in ((16,True),(32,False),(64,False)):
        for p in find_primes(n,2,beta=4):
            buckets,absS,rho_b,ord_b,phi,scanN,k,fs=analyze(n,p,full_scan=full)
            note=" FULL F_p* scan (rep-independent)" if fs else " SAMPLED coset-rep prefix (rep-dependent order tag)"
            print(f"n={n} p={p} phi=p-1={phi} scanned {scanN} b{note}")
            for cls in ("tiny(<=.05phi)","small(<=.5phi)","large(>.5phi)"):
                if cls in buckets and buckets[cls][1]>0:
                    s,c=buckets[cls]
                    print(f"    {cls:18s}: mean rho={s/c:.4f} over {c} b")
            tag="" if fs else " (rep-dependent — see note)"
            print(f"    rho@worst-b (argmax|S|) = {rho_b:.4f}  ord(b*)={ord_b}  ord/phi={ord_b/phi:.4f}{tag}")
            print()

if __name__=="__main__":
    main()
