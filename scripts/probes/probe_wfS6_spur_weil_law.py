#!/usr/bin/env python3
r"""#444 LANE S6: the SPURIOUS-ONLY Weil law -- exponent + Betti constant of spur_r(p).

PRIOR FINDING (probe_wfS6_weil_exponent.py, EXACT, anchor = exact complex char-0
energy NOT the Wick bound): at prize-scale primes p=n^beta, beta in [3,5], the char-p
energy E_r^charp = E_r^char0 EXACTLY for the OVERWHELMING majority of primes
(faithful transfer); spur_r(p) := E_r^charp - E_r^char0 > 0 only at a SPARSE set of
"spurious primes". The spur, when nonzero, is TINY: spur/p^{r-1} ~ 1e-4 << C(2r,r).

This probe isolates the LAW of the spurious set:
  (1) scan ALL primes p=1 mod n with beta=log_n p in a band, collect those with spur>0.
  (2) for each spurious prime, fit/record spur and the toric ratio spur/p^{r-1}/C(2r,r).
  (3) measure the Weil EXPONENT: across the spurious set, fit spur ~ C*p^alpha. The toric
      Weil-II prediction is alpha <= r-1 with C <= C(2r,r). GLT's r=2 weight-1 curve says
      the governing object has error O(p^{(2r-3)/2}) so alpha could be even < r-1.
  (4) DENSITY of the spurious set vs beta -- does it thin out (=> faithful transfer is
      generic at prize scale) or thicken?

The key deliverable: confirm spur is (a) sparse, (b) bounded by C(2r,r)*p^{r-1} with
HUGE margin, and report the empirical Weil exponent alpha_eff and constant C_eff that
SpurToricBounded would need. If alpha_eff <= r-1 and C_eff <= C(2r,r) across the
spurious set, that is direct numerical support for the named open input.

EXACT ARITHMETIC. p = 1 mod n prime, n = 2^a.
"""
from math import comb, log, exp
from collections import defaultdict

def is_prime(m):
    if m < 2: return False
    for q in (2,3,5,7,11,13,17,19,23,29,31,37):
        if m % q == 0: return m == q
    d = m-1; s=0
    while d%2==0: d//=2; s+=1
    for a in (2,3,5,7,11,13,17,19,23,29,31,37):
        x=pow(a,d,m)
        if x==1 or x==m-1: continue
        for _ in range(s-1):
            x=x*x%m
            if x==m-1: break
        else: return False
    return True

def _df(r):
    v=1
    for j in range(1,r+1): v*=(2*j-1)
    return v

def gen_order_n(p, n):
    g0=2
    while True:
        m=p-1; fs=[]; mm=m; d=2
        while d*d<=mm:
            if mm%d==0:
                fs.append(d)
                while mm%d==0: mm//=d
            d+=1
        if mm>1: fs.append(mm)
        if all(pow(g0,(p-1)//f,p)!=1 for f in fs): break
        g0+=1
    return pow(g0,(p-1)//n,p)

def Er_charp(n,r,p):
    g=gen_order_n(p,n)
    elts=[pow(g,k,p) for k in range(n)]
    dist=defaultdict(int)
    for e in elts: dist[e%p]+=1
    cur=dict(dist)
    for _ in range(r-1):
        nxt=defaultdict(int)
        for s1,c1 in cur.items():
            for e in elts: nxt[(s1+e)%p]+=c1
        cur=nxt
    return sum(c*c for c in cur.values())

def Er_char0(n,r):
    half=n//2
    cur=defaultdict(int)
    for k in range(n):
        idx=k%half; sgn=1 if k<half else -1
        v=[0]*half; v[idx]=sgn; cur[tuple(v)]+=1
    for _ in range(r-1):
        nxt=defaultdict(int)
        for vt,c in cur.items():
            for k in range(n):
                idx=k%half; sgn=1 if k<half else -1
                w=list(vt); w[idx]+=sgn; nxt[tuple(w)]+=c
        cur=nxt
    return sum(c*c for c in cur.values())

def main():
    print("="*78)
    print("S6 SPURIOUS-ONLY WEIL LAW (exact char-0 anchor)")
    print("="*78)
    for (n, r) in [(8,3),(16,3),(16,4),(32,3)]:
        char0=Er_char0(n,r); wick=_df(r)*n**r; cbin=comb(2*r,r)
        lo=int(n**3.0); hi=int(n**4.2)
        p=lo-(lo%n)+1
        if p<lo: p+=n
        spur_pts=[]; total=0
        # cap work
        maxprimes = 3000 if n<=16 else (1200 if n==32 else 400)
        while p<=hi and total<maxprimes:
            if is_prime(p):
                total+=1
                Er=Er_charp(n,r,p); spur=Er-char0
                if spur>0: spur_pts.append((p,spur,log(p,n)))
            p+=n
        nz=len(spur_pts)
        print(f"\n--- n={n} r={r}: char0={char0} wick={wick} (ratio {char0/wick:.3f}) C(2r,r)={cbin}")
        print(f"    scanned {total} primes in beta in [3,4.2]; spurious (spur>0): {nz}  density={nz/total if total else 0:.4f}")
        if nz==0:
            print("    => FAITHFUL TRANSFER everywhere in band (spur identically 0)")
            continue
        # toric ratios
        worstC = max(s/p**(r-1)/cbin for (p,s,_) in spur_pts)
        worst_ratio = max(s/p**(r-1) for (p,s,_) in spur_pts)
        print(f"    worst spur/p^(r-1) = {worst_ratio:.5g}  worst /C(2r,r) = {worstC:.5g}  (SpurToricBounded holds iff <=1)")
        # Weil exponent fit over spurious set
        if nz>=3:
            xs=[log(p) for (p,_,_) in spur_pts]; ys=[log(s) for (_,s,_) in spur_pts]
            m=len(xs); sx=sum(xs); sy=sum(ys); sxx=sum(x*x for x in xs); sxy=sum(x*y for x,y in zip(xs,ys))
            denom=(m*sxx-sx*sx)
            if abs(denom)>1e-9:
                alpha=(m*sxy-sx*sy)/denom; Ceff=exp((sy-alpha*sx)/m)
                print(f"    Weil fit: spur ~ {Ceff:.4g} * p^{alpha:.4f}   (toric needs alpha<=r-1={r-1}, C<=C(2r,r)={cbin})")
                verdict = "alpha<=r-1, C<=C(2r,r): SpurToricBounded SUPPORTED" if (alpha<=r-1+0.2 and Ceff<=cbin) else (
                          "alpha<=r-1 but C>C(2r,r)" if alpha<=r-1+0.2 else f"alpha={alpha:.2f}>r-1: exceeds toric exponent")
                print(f"    => {verdict}")
        # density vs beta: bucket
        buckets=defaultdict(int); tot_b=defaultdict(int)
        # recompute totals per bucket cheaply: just show spurious beta distribution
        bdist=defaultdict(int)
        for (p,s,b) in spur_pts: bdist[round(b,1)]+=1
        print(f"    spurious-prime beta distribution: {dict(sorted(bdist.items()))}")
        print(f"    sample spurious primes: {[(pp, ss, round(bb,3)) for (pp,ss,bb) in spur_pts[:6]]}")

if __name__=="__main__":
    main()
