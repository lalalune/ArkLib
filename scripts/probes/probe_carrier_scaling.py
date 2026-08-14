#!/usr/bin/env python3
"""
Carrier-size scaling probe (floor lane, hBadCount).

For a small RS code over F_p (eval domain = all of F_p^* or a subset), pick a random
stack (u0,u1) and measure, at MCA radius delta':
  - badCount = #{ gamma in F_p : line point u0+gamma*u1 is delta'-close to RS }
  - carrier |T| = #distinct codewords appearing as a close witness across bad gamma
  - L = Johnson list size proxy = max over centers of |RS cap Ball(center, e)| (the
        actual per-point list size encountered)
Compare |T| to L and L^2. Also test the reduction: c - c0 in RS close to ray {t*u1}.
GCXK25 claims |T| <= L^2; if empirically |T| ~ L (linear), the L^2 is pessimistic.
"""
import itertools, random
random.seed(1)

def rs_codewords(p, k, dom):
    # degree < k polynomials evaluated on dom (list of field elements)
    cws=[]
    for coeffs in itertools.product(range(p), repeat=k):
        cw=tuple(sum(coeffs[j]*pow(x,j,p) for j in range(k))%p for x in dom)
        cws.append((cw,coeffs))
    return cws

def hd(a,b): return sum(1 for x,y in zip(a,b) if x!=y)

def run(p,k,domsize,delta_frac,trials=40):
    dom=list(range(1,domsize+1))      # domsize distinct nonzero points
    n=len(dom)
    cws=[c for c,_ in rs_codewords(p,k,dom)]
    cwset=set(cws)
    e=int(delta_frac*n)               # absolute radius
    johnson_e = 1 - (k/n)**0.5        # relative Johnson radius
    results=[]
    for _ in range(trials):
        u0=tuple(random.randrange(p) for _ in range(n))
        u1=tuple(random.randrange(p) for _ in range(n))
        if all(v==0 for v in u1): continue
        bad=[]; carrier=set(); percenter=[]
        for g in range(p):
            line=tuple((u0[i]+g*u1[i])%p for i in range(n))
            close=[c for c in cws if hd(c,line)<=e]
            if close:
                bad.append(g); carrier.update(close); percenter.append(len(close))
        if not bad: continue
        L=max(percenter)              # max per-point list size actually seen
        results.append((len(bad),len(carrier),L))
    if not results: return None
    import statistics
    mb=max(r[0] for r in results); mc=max(r[1] for r in results); mL=max(r[2] for r in results)
    return n,e,johnson_e,mb,mc,mL

print("n  e  Jrad | maxBad  maxCarrier(|T|)  maxL   |  |T|/L   |T|/L^2  (L^2)")
for (p,k,ds,df) in [(11,2,8,0.45),(13,2,10,0.45),(13,3,10,0.40),(17,2,12,0.45),(11,3,8,0.40)]:
    r=run(p,k,ds,df)
    if r is None: print(f"p={p} k={k}: no bad"); continue
    n,e,J,mb,mc,mL=r
    l2=mL*mL
    print(f"{n:2d} {e:2d} {J:.2f} | {mb:5d}   {mc:6d}        {mL:4d}  | {mc/max(mL,1):5.2f}   {mc/max(l2,1):.3f}   ({l2})  [p={p},k={k}]")
