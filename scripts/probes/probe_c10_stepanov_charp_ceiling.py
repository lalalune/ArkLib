#!/usr/bin/env python3
"""
probe_c10_stepanov_charp_ceiling.py  (#444/#389, angle C10-stepanov-charp-ceiling)

ANGLE C10: a NEW Stepanov tailored to the char-p CEILING at depth -- build an auxiliary whose
vanishing controls the mod-p WRAP COUNT A_r (the anomaly), exploiting the 2-adic tower. Motivating
hope: the soft ceiling R_r=A_r/Wick<=1 needs only A_r<=slack, a COUNT; Stepanov-style auxiliaries
CAN bound counts even when the SUP cannot (sup stalls at n^{2/3} / HBK n^{9/8}, both REFUTED in-tree).

OBJECT (proper mu_n: p PRIME, n=2^mu, n|p-1, p>>n^3, NEVER n=p-1):
  A_r = E_r^{Fp,nonzero} - E_r^{char0,nonzero} counts 2r-tuples (x_1..x_r,y_1..y_r) in mu_n^{2r}
  with sum x_i == sum y_i mod p but the cyclotomic integers sum_eps zeta^{a_i} != 0 over C
  (the mod-p WRAP). This is distinct from C1's norm/height route (which gives ONSET only, T~n^r).

FOUR EXACT MEASUREMENTS (all integer-exact; pure Python => axiom-clean trivially):

(M1) WRAP-FIBER MULTIPLICITY. For Stepanov to beat the trivial count it needs multiplicity M>1 at
     the counted points. Fix (y-tuple, x_1..x_{r-1}); the free x_r solves x_r == T mod p. Since
     mu_n INJECTS into F_p, this fiber has AT MOST ONE solution. MEASURED max #sol/fiber = 1.
     => every counted wrap point is the UNIQUE mu_n solution of its fiber: multiplicity 1, FORCED
     by separability of X^n-1 (the in-tree stepanov_collapses_to_degree wall). No concentration.

(M2) WRAP SPREAD vs CONCENTRATION. When alive (small p / deep r), the wrap is SPREAD across many
     residue classes, each carrying ~2 colliding cyclotomic values -- NOT concentrated into few
     high-multiplicity fibers. (n=8 r=4 p=1201: 8 wrap-residues x 2 vals; n=16 r=3 p=7873: 64 x 2.)
     A Stepanov hook would require the OPPOSITE (few fibers, high mult). The 2-adic tower SPREADS
     (same mechanism as the I008 dyadic-tower NO-GAIN: telescopes in ROOTS, not multiplicity).

(M3) SLACK ARITHMETIC. Best per-fiber Stepanov certifies A_r <= n^{2r-1} (trivial total count).
     The consumer needs A_r <= Wick = (2r-1)!! n^r. But (2r-1)!! n^r << n^{2r-1} for all n,r>=2
     (ratio -> 0). So even the BEST Stepanov-on-fiber bound is ORDERS ABOVE the needed slack:
     Stepanov certifies a WORSE bound than the true A_r already satisfies. NO GAIN.

(M4) MULTIVARIATE / WEIL-BOMBIERI version. The curve/variety Stepanov-Weil error term is sqrt(q)*deg
     = n^{beta/2}*deg, VACUOUS vs the n-scale count whenever beta>2 (always in the prize beta 4-5).
     Exactly the in-tree C36 / probe_stepanov_weil_qvacuity vacuity. The COUNT inherits it.

VERDICT: NO-GAIN / reduces-to-bgk. C10 is the SAME wall as the entire Stepanov family on mu_n
(C36 HBK REFUTED, I008 dyadic-tower NO-GAIN, stepanov_collapses_to_degree): X^n-1 separable =>
mu_n manufactures NO multiplicity => Stepanov is blind below the true count. Reframing the target
from the SUP to the COUNT A_r does NOT escape, because (a) the wrap fiber is a single injective
point (M=1), (b) the wrap SPREADS not concentrates, (c) the trivial per-fiber count n^{2r-1} is
already ABOVE the needed Wick slack, and (d) the multivariate Weil error sqrt(q) is vacuous on the
thin mu_n. No push past the 0.011 effective exponent; no soft ceiling proof. The soft ceiling
R_r<=1 survives EMPIRICALLY (it is the open BGK/DSAR input), not via Stepanov.
"""
import math, itertools
from collections import defaultdict

def is_prime(m):
    if m<2: return False
    if m%2==0: return m==2
    d=3
    while d*d<=m:
        if m%d==0: return False
        d+=2
    return True
def prime_factors(m):
    f=set();d=2
    while d*d<=m:
        while m%d==0:f.add(d);m//=d
        d+=1
    if m>1:f.add(m)
    return f
def primroot(p):
    fs=prime_factors(p-1);g=2
    while any(pow(g,(p-1)//q,p)==1 for q in fs):g+=1
    return g
def roots_modp(n,p):
    g=primroot(p);w=pow(g,(p-1)//n,p)
    return [pow(w,i,p) for i in range(n)]
def reduced_single(a,n):
    d=n//2;coord=a%d;sgn=-1 if (a//d)%2 else 1
    return coord,sgn
def rfold(n,p,mu_roots,r):
    d=n//2
    ri=[(a,mu_roots[a]%p)+reduced_single(a,n) for a in range(n)]
    cur={(0,tuple([0]*d)):1}
    for _ in range(r):
        nxt=defaultdict(int)
        for (res,vec),c in cur.items():
            lv=list(vec)
            for a,mv,co,sg in ri:
                nv=lv.copy();nv[co]+=sg
                nxt[((res+mv)%p,tuple(nv))]+=c
        cur=nxt
    return cur
def wick(r,n):
    x=1;m=2*r-1
    while m>0:x*=m;m-=2
    return x*n**r
def first_prime_ge(lo,n):
    m=max(2,lo//n)
    while True:
        c=m*n+1
        if c>=lo and is_prime(c): return c
        m+=1

print("="*100); print("C10 STEPANOV-CHARP-CEILING -- four exact measurements"); print("="*100)

print("\n[M1] WRAP-FIBER MULTIPLICITY (max #x_r in mu_n per fiber). Must be >1 for Stepanov to bite.")
for (n,r,blo) in [(8,4,3.4),(16,3,3.2)]:
    p=first_prime_ge(int(n**blo),n); mu=roots_modp(n,p)
    maxsol=0; sample=0
    for ytup in itertools.product(mu,repeat=r):
        Sy=sum(ytup)%p
        for xpre in itertools.product(mu,repeat=r-1):
            need=(Sy-sum(xpre))%p
            maxsol=max(maxsol,sum(1 for x in mu if x==need)); sample+=1
            if sample>=150000: break
        if sample>=150000: break
    print(f"   n={n} r={r} p={p} beta={math.log(p)/math.log(n):.2f}: max #sol/fiber={maxsol} (=1 => M=1 forced, Stepanov vacuous)")

print("\n[M2] WRAP SPREAD vs CONCENTRATION (when alive).")
for (n,r,blo,bhi) in [(8,4,3.0,4.2),(16,3,3.0,4.0)]:
    d=n//2;lo=int(n**blo);hi=int(n**bhi);m=max(2,lo//n);live=[]
    while m*n+1<=hi and len(live)<6:
        p=m*n+1;m+=1
        if not (p>=lo and is_prime(p)): continue
        cur=rfold(n,p,roots_modp(n,p),r)
        byres=defaultdict(list)
        for (res,vec),c in cur.items(): byres[res].append((vec,c))
        Anom=sum((sum(c for _,c in l))**2-sum(c*c for _,c in l) for l in byres.values())
        if Anom>0: live.append((p,byres,Anom))
    if not live:
        print(f"   n={n} r={r}: no live wrap in window (onset above window)"); continue
    p,byres,Anom=max(live,key=lambda t:t[0])
    wr=[(res,l) for res,l in byres.items() if (sum(c for _,c in l))**2-sum(c*c for _,c in l)>0]
    sizes=[len(l) for _,l in wr]
    print(f"   n={n} r={r} p={p} beta={math.log(p)/math.log(n):.2f} Anom={Anom}: wrap on {len(wr)} residues, "
          f"distinct-vals/residue min={min(sizes)} max={max(sizes)} (SPREAD, not concentrated)")

print("\n[M3] SLACK ARITHMETIC: best per-fiber Stepanov = n^{2r-1} (trivial) vs needed Wick=(2r-1)!!n^r.")
for n in [8,16,2**10,2**30]:
    for r in [2, max(2,int(round(math.log(n**4))))]:
        W=wick(r,n); T=n**(2*r-1)
        lgW=math.log2(W); lgT=math.log2(T)
        print(f"   n={n} r={r}: log2(Wick)={lgW:.1f}  log2(trivial)={lgT:.1f}  Wick<<trivial: {W<T}  gap=2^{lgT-lgW:.1f}")

print("\n[M4] MULTIVARIATE WEIL-BOMBIERI: error sqrt(q)=n^(beta/2) vacuous vs n-count for beta>2.")
for beta in [4,5]:
    print(f"   beta={beta}: sqrt(q)=n^{beta/2:.1f} >> n (count scale) -> Weil/Bombieri VACUOUS on thin mu_n (C36)")

print("\n"+"="*100)
print("VERDICT: NO-GAIN (reduces-to-bgk). Reframing SUP->COUNT does not escape the separability/")
print("M=1 multiplicity wall: wrap fiber single+injective, wrap SPREADS, trivial fiber count already")
print("> Wick slack, Weil error sqrt(q) vacuous. Soft ceiling R_r<=1 stays the open BGK/DSAR input.")
print("="*100)
