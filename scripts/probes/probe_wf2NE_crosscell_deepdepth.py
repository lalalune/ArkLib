"""
probe_wf2NE_crosscell_deepdepth.py  (#407 lane wf-NE, part 2)

Part 1 found: at fixed SMALL r, crossCell is p-INDEPENDENT (char-0 fixed integer), the major arc
(random main term ~(n/2)^r 2^r/p) VANISHES as p grows, so |minor|/major BLOWS UP — minor IS the
whole crossCell. NO concentration on the random main term in the thin regime at small r.

BUT the |minor|/major ratio DROPS as r grows (toward the deep-moment band r~β log n). The decisive
prize question: at the deep depth r* = ceil(β·log_2 n) = ln q / ln 2 (the genuinely-open band
[β log n, 1.36n]), does the minor arc become SUBDOMINANT to the major arc (=> crossCell concentrates
on its random main term => floor) or does it stay >~ major (=> no cancellation => pinned)?

The deep-moment validity target (DM): E_r <= (2r-1)!! n^{r-1}, equivalently crossCell stays at the
"random" Wick level. crossCell = N0(G,2r')-2N0(H,2r') with r' the energy index; here we use the
raw r-fold relation count N0(.,r) so the depth variable is r directly (r ~ ln q).

We measure at r* and r*+/-2:
  - cc_observed / cc_random  where cc_random = major*  (the t=0 main term)
  - |minor|/major at depth r*
  - whether minor/major SHRINKS as p grows at FIXED r=r* (the uniform-in-q cancellation test)
Exact DFT power-sum, multiple primes per n.
"""
import math, sys
import numpy as np

def pr(*a):
    print(*a); sys.stdout.flush()

def isprime(m):
    if m<2: return False
    for q in (2,3,5,7,11,13,17,19,23,29,31,37):
        if m%q==0: return m==q
    d=m-1; s=0
    while d%2==0: d//=2; s+=1
    for a in (2,3,5,7,11,13,17,19,23,29,31,37):
        x=pow(a,d,m)
        if x in (1,m-1): continue
        for _ in range(s-1):
            x=x*x%m
            if x==m-1: break
        else: return False
    return True

def prime_factors(m):
    s=set(); d=2
    while d*d<=m:
        while m%d==0: s.add(d); m//=d
        d+=1
    if m>1: s.add(m)
    return s

def subgroup(p,n):
    e=(p-1)//n; pf=prime_factors(n)
    for c in range(2,p):
        h=pow(c,e,p)
        if pow(h,n,p)!=1: continue
        if any(pow(h,n//q,p)==1 for q in pf): continue
        S=set(); x=1
        for _ in range(n): x=x*h%p; S.add(x)
        if len(S)==n: return sorted(S)
    raise RuntimeError("no subgroup")

def coset_split(S,p,n):
    H=sorted({(x*x)%p for x in S}); Hset=set(H)
    zetaH=[x for x in S if x not in Hset]
    return H, zetaH, zetaH[0]

def SH_table(H,p):
    ind=np.zeros(p)
    for x in H: ind[x]=1.0
    return np.fft.fft(ind).conj()

def crosscell_circle(H,zeta,r,p,SH):
    idx=(zeta*np.arange(p))%p
    SHz=SH[idx]
    contrib=np.zeros(p,dtype=complex)
    for a in range(1,r):
        contrib += math.comb(r,a)*(SH**(r-a))*(SHz**a)
    total=contrib.sum().real/p
    major=contrib[0].real/p
    minor=(contrib.sum()-contrib[0]).real/p
    return total,major,minor

def run():
    pr("="*104)
    pr("wf-NE part2: minor vs major at the DEEP depth r* = ceil(beta log_2 n) ~ ln q (the open band)")
    pr("="*104)
    pr("DECISIVE: at r=r*, does |minor|/major SHRINK as p grows (uniform cancellation => floor)")
    pr("          or stay >~ O(1) (no cancellation => pinned)?\n")
    PMAX=180_000
    for n in [8,16,32]:
        nh=n//2; logn=math.log2(n)
        pr(f"\n{'='*94}\n--- n={n} (|H|={nh}, log2 n={logn:.1f}) ---")
        pr(f"{'p':>9} {'beta':>5} {'r*':>4} {'crossCell':>16} {'major(rand)':>16} "
           f"{'|minor|/major':>13} {'cc/major':>10}")
        rows_at_rstar=[]
        # primes spanning beta 2..5 at this n
        idxs=[16,128,1024,8192,32768]
        for idx in idxs:
            p=None; m=idx
            while m<idx*3+300 and n*m+1<=PMAX:
                cand=n*m+1
                if isprime(cand): p=cand; break
                m+=1
            if p is None: continue
            try:
                S=subgroup(p,n); H,zetaH,zeta=coset_split(S,p,n)
            except Exception as ex:
                pr(f"  skip p={p}: {ex}"); continue
            beta=math.log(p)/math.log(n)
            rstar=max(2, math.ceil(beta*logn))   # ln q / ln 2 = beta log_2 n
            SH=SH_table(H,p)
            for r in [rstar]:
                if r>22: r=22
                total,major,minor=crosscell_circle(H,zeta,r,p,SH)
                rm=abs(minor)/abs(major) if abs(major)>1e-12 else float('inf')
                cm=total/major if abs(major)>1e-12 else float('inf')
                pr(f"{p:>9} {beta:>5.2f} {r:>4} {total:>16.1f} {major:>16.1f} {rm:>13.4f} {cm:>10.4f}")
                rows_at_rstar.append((p,beta,r,rm,cm))
        pr(f"  -- trend of |minor|/major at r=r* as p (beta) grows, n={n} --")
        for (p,beta,r,rm,cm) in rows_at_rstar:
            pr(f"     beta={beta:.2f} r*={r}: |minor|/major={rm:.4f}  cc/major={cm:.4f}")
    pr("\n"+"="*104)
    pr("If |minor|/major at r* DECREASES with beta -> minor cancels at the relevant depth -> FLOOR side.")
    pr("If it STAYS O(1) or grows -> no cancellation at the open band -> PINNED.")
    pr("="*104)

if __name__=="__main__":
    run()
