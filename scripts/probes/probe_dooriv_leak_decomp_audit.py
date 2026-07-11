#!/usr/bin/env python3
"""
RULE-6 ADVERSARIAL RE-AUDIT of my own f_r=1-|A_r|/Sum|eta|^r leak result (commit 630e2198f).

WORRY: f_r high in thin could be DRIVEN BY the known thin ABSOLUTE-MOMENT INFLATION (the denominator
Sum_b|eta_b|^r being larger in thin -- companion to 6feb11b53 even-energy inflation + the odd-profile
entry 1790 which found |A_r| PINNED HIGH in thin by Sidon rigidity, i.e. signed cancellation WORSE). If
my Δf_r>0 is just the denominator inflating (not the numerator |A_r| genuinely shrinking relative to the
mass), then "thin discards more" is a RESTATEMENT of moment inflation, not a new cancellation advantage,
and my receipt would be MISLEADING. Decompose honestly.

For ODD r: A_r = Sum_{b!=0} eta_b^r (signed, real). Define:
  amom_r = Sum_{b!=0} |eta_b|^r        (absolute moment, denominator)
  absA_r = |A_r|                        (signed sum magnitude, numerator)
  f_r    = 1 - absA_r/amom_r
Report thin/thick ratios of amom_r and absA_r SEPARATELY, and the per-b NORMALIZED signed sum
  g_r = |Sum_b (eta_b/M)^r| / (#b)      and   amom_norm = Sum_b (|eta_b|/M)^r / (#b)
so M-scale and count cancel. If thin f_r-advantage comes from absA_r/amom_r being smaller in thin for a
reason NOT explained by amom inflation alone, it survives; if absA_r/amom_r tracks the same in both once
you account for the mass, it's a restatement.
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

def find_prime(t,mod):
    k0=max(1,round(t/mod))
    for d in range(0,2000000):
        for s in (1,-1):
            kk=k0+s*d
            if kk<1: continue
            p=kk*mod+1
            if p>3 and is_prime(p): return p

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

def stats(n,p):
    e=subgroup(n,p); eta=periods(e,p)
    M=max(abs(eta[b]) for b in range(1,p))
    nb=p-1
    rows={}
    rmax=2*int(math.log2(n))+1
    for r in range(3,rmax+1,2):
        absA=abs(sum(eta[b]**r for b in range(1,p)))
        amom=sum(abs(eta[b])**r for b in range(1,p))
        # M-normalized, count-normalized (scale + size free):
        gA=absA/(nb*M**r)          # normalized signed sum (my C_r at odd r, essentially)
        gmom=amom/(nb*M**r)        # normalized absolute moment
        f=1-absA/amom if amom>0 else 0.0
        rows[r]=(absA,amom,gA,gmom,f,M)
    return rows

def run():
    print("RULE-6 re-audit: decompose f_r=1-|A_r|/amom_r into numerator |A_r| vs denominator amom_r")
    print("gA=|A_r|/((p-1)M^r) (norm signed), gmom=amom/((p-1)M^r) (norm abs moment). ODD r.\n")
    # one thin + one thick per n; compare the M-normalized numerator and denominator directly.
    for n in [16,32]:
        pthick=find_prime(int(n**2.5),n); pthin=find_prime(int(n**4.0),n)
        st=stats(n,pthick); sh=stats(n,pthin)
        print(f"== n={n}  THICK p={pthick} (b=2.5)  vs  THIN p={pthin} (b=4.0) ==")
        print(f"  {'r':>3} | {'gA_thick':>9} {'gA_thin':>9} {'gA thin/thick':>13} | {'gmom_thk':>9} {'gmom_thn':>9} {'gmom t/t':>9} | {'f_thick':>7} {'f_thin':>7}")
        for r in sorted(st):
            aT=st[r][2]; aN=sh[r][2]; mT=st[r][3]; mN=sh[r][3]; fT=st[r][4]; fN=sh[r][4]
            ratA = aN/aT if aT>0 else float('inf')
            ratM = mN/mT if mT>0 else float('inf')
            print(f"  {r:>3} | {aT:9.4f} {aN:9.4f} {ratA:13.3f} | {mT:9.4f} {mN:9.4f} {ratM:9.3f} | {fT:7.4f} {fN:7.4f}")
        print()
    print("READING:")
    print(" - If gA (norm SIGNED sum) is SMALLER in thin (gA thin/thick < 1) => the NUMERATOR genuinely")
    print("   cancels more in thin: real signed-cancellation advantage, f_r advantage is NOT just denom inflation.")
    print(" - If gA thin/thick ~ 1 or >1 but gmom thin/thick >> 1 => f_r advantage is DRIVEN BY denominator")
    print("   (absolute-moment inflation, 6feb11b53/odd-profile-1790 known effect) => my 'discards more'")
    print("   framing is a RESTATEMENT of moment inflation, NOT a new cancellation lever. (would need a")
    print("   correction note on commit 630e2198f.)")

if __name__=="__main__":
    run()
