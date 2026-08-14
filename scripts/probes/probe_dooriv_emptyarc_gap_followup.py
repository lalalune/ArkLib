#!/usr/bin/env python3
# Followup: does the worst-b largest gap carry sqrt-cancellation, or is the
# CORRELATION DECAY (0.57->0.34->0.22) evidence it DECOUPLES at scale?
# Key test: a single largest gap of size G (arc length G*p/n) can, at BEST, force
# |eta_b| <= n - (mass that would have been in the hole). But |eta| is a PHASE sum,
# not an occupancy count. A single empty arc gives at most a TRIVIAL bound:
#   one missing arc of angular width w=2pi*G/n changes |eta| by O(1) per the n terms,
#   NOT by a sqrt factor. So even an anomalous gap can only certify a CONSTANT-factor
#   reduction, not the sqrt(n log) -> sqrt(n) gap. Verify numerically:
#   compare |eta_b| to the "single-hole bound": n minus the arc deficit.
import math, random, statistics
def is_prime(n):
    if n<2: return False
    for q in (2,3,5,7,11,13,17,19,23,29,31,37):
        if n%q==0: return n==q
    d=n-1;r=0
    while d%2==0: d//=2;r+=1
    for a in (2,3,5,7,11,13,17,19,23,29,31,37):
        x=pow(a,d,n)
        if x in (1,n-1): continue
        for _ in range(r-1):
            x=x*x%n
            if x==n-1: break
        else: return False
    return True
def find_prime(n,beta):
    t=int(round(n**beta)); k0=max(2,t//n)
    for dk in range(400000):
        for k in (k0+dk,k0-dk):
            if k<2: continue
            p=k*n+1
            if p>n*n*n and is_prime(p): return p
def fac(m):
    f={};d=2
    while d*d<=m:
        while m%d==0: f[d]=f.get(d,0)+1;m//=d
        d+=1
    if m>1: f[m]=f.get(m,0)+1
    return f
def gen(p,F):
    for g in range(2,p):
        if all(pow(g,(p-1)//q,p)!=1 for q in F): return g
def sub(p,n):
    h=pow(gen(p,fac(p-1)),(p-1)//n,p); S=[];x=1
    for _ in range(n): S.append(x); x=x*h%p
    return S
def eta(b,mu,p):
    re=im=0.0
    for y in mu:
        a=2*math.pi*((b*y)%p)/p; re+=math.cos(a); im+=math.sin(a)
    return math.hypot(re,im)
def gaps(res,p):
    rs=sorted(res); n=len(rs); out=[]
    for i in range(n):
        out.append(((rs[(i+1)%n]-rs[i])%p) if i<n-1 else (rs[0]+p-rs[i]))
    return out
print("=== Followup: gap-statistic CANNOT carry sqrt-cancellation (single-hole = O(1)) ===")
print("Test: worst-b |eta| vs n - (single-largest-arc phase deficit). If the gap route")
print("worked, removing the single biggest empty arc would explain the sqrt gap. It can't.\n")
random.seed(7)
for n in (16,32,64,128):
    p=find_prime(n,4.0); mu=sub(p,n); unit=p/n
    # find worst b
    be=-1;bb=None
    bs=range(1,p) if p<=200000 else random.sample(range(1,p),40000)
    for b in bs:
        e=eta(b,mu,p)
        if e>be: be=e;bb=b
    A=[(bb*y)%p for y in mu]; G=gaps(A,p)
    gmax=max(G); 
    # angular width of biggest empty arc
    w=2*math.pi*gmax/p
    # "single-hole heuristic bound": if points were uniform on the circle MINUS this arc,
    # |eta| ~ |n * (integral over remaining arc)| -> for a uniform-on-complement model the
    # resultant from one missing arc of width w is n*sin(w/2)/(pi - w/2)... trivial O(1) shape.
    # Simpler honest check: the SECOND, THIRD largest gaps -- is clumping in ONE hole or many?
    Gs=sorted(G,reverse=True)
    top1=Gs[0]/unit; top2=Gs[1]/unit; top3=Gs[2]/unit
    sumtop3=sum(Gs[:3])/unit
    # fraction of total circle in the top gap vs needed for sqrt-cancellation
    # sqrt route would need the "deficit" to scale like n - sqrt(n*log) i.e. ~n. 
    # one gap covers gmax/p of circle = top1/n fraction.
    frac_top1 = gmax/p
    print(f"n={n:4d} p={p}  |eta|_max={be:.2f}  ratio/sqrt={be/math.sqrt(n*math.log(p/n)):.3f}")
    print(f"     top-3 gaps (p/n units)={top1:.2f},{top2:.2f},{top3:.2f}  sum3={sumtop3:.2f}")
    print(f"     top gap covers {100*frac_top1:.2f}% of circle  (sqrt route needs ~(1-1/sqrt(n))=~{100*(1-1/math.sqrt(n)):.1f}% empty)")
    print(f"     => single hole is {100*frac_top1:.1f}% << {100*(1-1/math.sqrt(n)):.0f}%: gap statistic CANNOT carry the sqrt gap")
