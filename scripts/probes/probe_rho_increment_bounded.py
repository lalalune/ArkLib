#!/usr/bin/env python3
"""
PROBE: is the per-level ratio rho(2^i) = M(2^{i+1})/M(2^i) BOUNDED per level in the prize regime?
If rho(2^i) in [c,C] uniformly, then log rho is a BOUNDED-increment sequence: Azuma-Freedman on
Sum log rho(2^i) is the formalizable object (prize <=> Sum log rho <= 1/2 log L + log C).
The eta-increment martingale (probe_407_cumulant_martingale_deep) is UNbounded -- but the LOG-RATIO
of consecutive sup-norms is a different, possibly bounded, object. Test it.

M(2^a) = max_{b != 0} | sum_{x in mu_{2^a}} e_p(b x) |, mu_{2^a} = order-2^a subgroup of F_p^*.
PRIZE REGIME: proper thin subgroups, p >> n^3, p = 1 mod 2^a_max, NEVER n=q-1.
"""
import cmath, math
import numpy as np

def is_prime(m):
    if m<2: return False
    for q in (2,3,5,7,11,13,17,19,23,29,31,37,41,43,47):
        if m%q==0: return m==q
    d=m-1;r=0
    while d%2==0:d//=2;r+=1
    for a in (2,3,5,7,11,13,17,19,23,29,31,37):
        if a>=m: continue
        x=pow(a,d,m); 
        if x==1 or x==m-1: continue
        ok=False
        for _ in range(r-1):
            x=x*x%m
            if x==m-1: ok=True;break
        if not ok: return False
    return True

def find_prime(amax, beta, near_min=True):
    n=2**amax
    target=int(n**beta)
    # p = 1 mod 2^amax (so mu_{2^amax} exists), p prime, p near target
    mod=2**amax
    start=(target//mod)*mod+1
    for k in range(0, 200000):
        for cand in (start+k*mod, start-k*mod):
            if cand>n and is_prime(cand):
                return cand
    return None

def primitive_root(p):
    # find generator of F_p^*
    fac=[]
    pm=p-1; d=2
    while d*d<=pm:
        if pm%d==0:
            fac.append(d)
            while pm%d==0: pm//=d
        d+=1
    if pm>1: fac.append(pm)
    for g in range(2,p):
        if all(pow(g,(p-1)//q,p)!=1 for q in fac):
            return g
    return None

def subgroup(p, g, n):
    # order-n subgroup: <g^((p-1)/n)>
    h=pow(g,(p-1)//n,p)
    S=[]; cur=1
    for _ in range(n):
        S.append(cur); cur=cur*h%p
    return S

def Mval(p, S):
    # max over b != 0 of |sum_{x in S} e_p(b x)|
    best=0.0
    w=2j*math.pi/p
    # b ranges over F_p^* but by dilation symmetry over cosets; brute small p
    for b in range(1,p):
        s=sum(cmath.exp(w*(b*x % p)) for x in S)
        a=abs(s)
        if a>best: best=a
    return best

results=[]
for beta in (3.2, 4.0, 4.5):
    for amax in (4,5,6):
        p=find_prime(amax,beta)
        if p is None or p>200003: 
            continue
        g=primitive_root(p)
        Ms=[]
        for a in range(1,amax+1):
            n=2**a
            S=subgroup(p,g,n)
            Ms.append(Mval(p,S))
        rhos=[Ms[i+1]/Ms[i] for i in range(len(Ms)-1)]
        logrhos=[math.log(r) for r in rhos]
        results.append((amax,beta,p,Ms,rhos,logrhos))
        print(f"amax={amax} beta={beta} p={p} n={2**amax}")
        print(f"  M = {[round(m,3) for m in Ms]}")
        print(f"  rho(2^i)={[round(r,4) for r in rhos]}  (sqrt2={math.sqrt(2):.4f})")
        print(f"  log rho ={[round(l,4) for l in logrhos]}")
        print(f"  rho range: [{min(rhos):.4f}, {max(rhos):.4f}]  Prod rho={np.prod(rhos):.4f}")
        print()

# Verdict: are rho's bounded in [c, C] with c>0, C<inf uniformly?
allrho=[r for (_,_,_,_,rhos,_) in results for r in rhos]
if allrho:
    print(f"=== VERDICT: rho_min={min(allrho):.4f}  rho_max={max(allrho):.4f} over {len(allrho)} levels ===")
    print(f"    log rho range: [{math.log(min(allrho)):.4f}, {math.log(max(allrho)):.4f}]")
    print(f"    BOUNDED-INCREMENT? rho in [{min(allrho):.3f},{max(allrho):.3f}] => |log rho| <= {max(abs(math.log(min(allrho))),abs(math.log(max(allrho)))):.4f}")
