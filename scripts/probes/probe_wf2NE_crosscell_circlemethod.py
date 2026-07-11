"""
probe_wf2NE_crosscell_circlemethod.py  (#407 lane wf-NE)

NEW LENS: the CIRCLE METHOD applied directly to crossCell (NOT to the bad-scalar count a,
which CircleMethodFreeSetSupport already did; and NOT the TOTAL crossCell value, which wf-LF/A02
already measured = random expectation). The new object is the MAJOR/MINOR ARC DECOMPOSITION of
crossCell, exploiting the dyadic 2-power split G = H ⊔ ζH.

THE EXACT FOURIER IDENTITY (the circle method on the relation count).
For G ⊆ F_p, the r-fold relation count is
    N0(G, r) = (1/p) Σ_{t∈F_p} S_G(t)^r ,     S_G(t) = Σ_{x∈G} e_p(t·x).
The t=0 ("major arc") term is |G|^r / p — the RANDOM main term (uniform measure).
The t≠0 ("minor arc") terms carry ALL the arithmetic: N0 - |G|^r/p = (1/p) Σ_{t≠0} S_G(t)^r.

For crossCell, with the dyadic split G=H⊔ζH so S_G(t)=S_H(t)+S_H(ζt):
    crossCell(r) = N0(G,r) - 2 N0(H,r)
                 = (1/p) Σ_t [ (S_H(t)+S_H(ζt))^r - 2 S_H(t)^r ].
Expanding the binomial and using the (t↦ζ^{-1}t) reindex on S_H(ζt) terms:
    crossCell(r) = (1/p) Σ_t Σ_{a=1}^{r-1} C(r,a) S_H(t)^{r-a} S_H(ζt)^a .   (the genuinely cross part)

MAJOR ARC of crossCell  (t=0):  S_H(0)=|H|=n/2, so the t=0 term is
    (1/p) Σ_{a=1}^{r-1} C(r,a) (n/2)^r = (1/p) (n/2)^r (2^r - 2).
This is the RANDOM main term of crossCell (= "BCHKS expectation", matches wf-LF's cc/(N0H/n)~2^r).
MINOR ARC of crossCell  (t≠0):  the rest. THE QUESTION (my lane): is the minor arc SMALLER than
the major arc uniformly in p? If yes, crossCell concentrates on its random main term and the floor
follows from the random value; if the minor arc DOMINATES (no cancellation), pin it.

KEY DYADIC TEST: S_H(ζt) vs S_H(t). Because ζ is a NON-SQUARE in μ_n and H=squares, the pair
(S_H(t), S_H(ζt)) probes whether the 2-power coset structure forces minor-arc cancellation in the
PRODUCT S_H(t)^{r-a} S_H(ζt)^a beyond what a generic set gives.

We compute EVERYTHING exactly (integer/float exp, err ~1e-12), multiple primes, n=8,16,32.
"""
import math, sys, cmath
import numpy as np

def pr(*a):
    print(*a); sys.stdout.flush()

def isprime(m):
    if m < 2: return False
    for q in (2,3,5,7,11,13,17,19,23,29,31,37):
        if m % q == 0: return m == q
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

def subgroup(p, n):
    assert (p-1)%n==0
    e=(p-1)//n; pf=prime_factors(n)
    for c in range(2,p):
        h=pow(c,e,p)
        if pow(h,n,p)!=1: continue
        if any(pow(h,n//q,p)==1 for q in pf): continue
        S=set(); x=1
        for _ in range(n): x=x*h%p; S.add(x)
        if len(S)==n: return sorted(S)
    raise RuntimeError("no subgroup")

def coset_split(S, p, n):
    H=sorted({ (x*x)%p for x in S })
    assert len(H)==n//2, f"H size {len(H)} != {n//2}"
    Hset=set(H)
    zetaH=[x for x in S if x not in Hset]
    zeta=zetaH[0]
    return H, zetaH, zeta

def SH_table(H, p):
    """S_H(t) for all t in F_p, exact complex via DFT of indicator. length-p."""
    ind=np.zeros(p)
    for x in H: ind[x]=1.0
    # S_H(t) = sum_x e_p(t x) = DFT at frequency -t (numpy convention). We want S_H(t)=sum_x e^{2pi i t x/p}.
    # np.fft.fft(ind)[k] = sum_x ind[x] e^{-2pi i k x/p}. So S_H(t)=conj(fft[t]) = fft[-t].
    F=np.fft.fft(ind)
    return F.conj()   # SH[t] = sum_x e^{+2pi i t x/p}

def crosscell_circle(H, zeta, r, p, SH):
    """Exact major/minor arc decomposition of crossCell(r) via the Fourier identity.
       crossCell(r) = (1/p) Σ_t Σ_{a=1}^{r-1} C(r,a) S_H(t)^{r-a} S_H(ζt)^a.
       Returns (crossCell_total, major_arc(t=0), minor_arc(t!=0))."""
    n = 2*len(H)
    # S_H(ζt): reindex. SHz[t] = SH[(zeta*t)%p]
    idx = (zeta*np.arange(p)) % p
    SHz = SH[idx]
    binom = [math.comb(r,a) for a in range(r+1)]
    # per-t contribution: sum_{a=1}^{r-1} C(r,a) SH^{r-a} SHz^a
    contrib = np.zeros(p, dtype=complex)
    for a in range(1, r):
        contrib += binom[a] * (SH**(r-a)) * (SHz**a)
    total = contrib.sum().real / p
    major = contrib[0].real / p     # t=0
    minor = (contrib.sum() - contrib[0]).real / p
    return total, major, minor

def N0_direct(elts, r, p):
    """exact char-p relation count via DFT-power sum: N0=(1/p)Σ_t S(t)^r."""
    ind=np.zeros(p)
    for x in elts: ind[x]=1.0
    S=np.fft.fft(ind).conj()
    return (S**r).sum().real / p

def run():
    pr("="*108)
    pr("wf-NE: CIRCLE METHOD on crossCell — MAJOR (t=0, random main term) vs MINOR (t!=0) arc decomposition")
    pr("="*108)
    pr("crossCell(r) = (1/p) Σ_t Σ_{a=1}^{r-1} C(r,a) S_H(t)^{r-a} S_H(ζt)^a   [exact Fourier identity]")
    pr("major = t=0 term = (n/2)^r (2^r-2)/p  (RANDOM main term).  minor = Σ_{t!=0}.")
    pr("QUESTION: |minor| << major uniformly in p?  => crossCell concentrates, floor follows.")
    pr("          |minor| >~ major (grows with r)?  => no cancellation, PINNED.\n")

    PMAX = 200_000
    configs = [
        (8,  [16, 64, 256, 1024, 4096, 16384]),
        (16, [16, 64, 256, 1024, 4096]),
        (32, [16, 64, 256, 1024]),
    ]
    for (n, indices) in configs:
        nh=n//2
        pr(f"\n{'='*100}\n--- n={n}  (H=mu_{nh}, |H|={nh}) ---")
        pr(f"{'p':>9} {'beta':>5} {'r':>3} {'crossCell':>14} {'major(t=0)':>14} {'minor(t!=0)':>14} "
           f"{'|minor|/major':>13} {'minor/cc':>10}")
        ratio_by_r={}
        for idx in indices:
            p=None; m=idx
            while m<idx*3+200 and n*m+1<=PMAX:
                cand=n*m+1
                if isprime(cand): p=cand; break
                m+=1
            if p is None: continue
            try:
                S=subgroup(p,n); H,zetaH,zeta=coset_split(S,p,n)
            except Exception as ex:
                pr(f"  skip p={p}: {ex}"); continue
            beta=math.log(p)/math.log(n)
            SH=SH_table(H,p)
            rmax = 10 if p<50000 else 8
            for r in range(2, rmax):
                total,major,minor = crosscell_circle(H,zeta,r,p,SH)
                # sanity: cross-check against direct N0(G,r)-2N0(H,r)
                rmratio = abs(minor)/abs(major) if major else float('inf')
                mfrac = minor/total if abs(total)>1e-9 else float('inf')
                pr(f"{p:>9} {beta:>5.2f} {r:>3} {total:>14.2f} {major:>14.2f} {minor:>14.2f} "
                   f"{rmratio:>13.4f} {mfrac:>10.4f}")
                ratio_by_r.setdefault(r,[]).append((p,beta,rmratio))
            # one direct cross-check
            G=H+zetaH
            cc_direct = N0_direct(G,4,p) - 2*N0_direct(H,4,p)
            cc_circle,_,_ = crosscell_circle(H,zeta,4,p,SH)
            pr(f"       [check r=4] direct N0-form={cc_direct:.2f}  circle-form={cc_circle:.2f}  "
               f"err={abs(cc_direct-cc_circle):.2e}")
        pr(f"  -- |minor|/major across primes (uniformity in q), n={n} --")
        for r in sorted(ratio_by_r):
            vals=[v for (_,_,v) in ratio_by_r[r]]
            if len(vals)>=2:
                pr(f"     r={r}: |minor|/major range [{min(vals):.4f},{max(vals):.4f}] "
                   f"spread={max(vals)-min(vals):.4f}")
    pr("\n"+"="*108)
    pr("VERDICT KEY:")
    pr("- |minor|/major -> 0 as p grows (at fixed r): minor arc cancels, crossCell = random main term => floor")
    pr("- |minor|/major bounded < 1 uniformly: crossCell concentrated on major => sub-trivial => PRIZE candidate")
    pr("- |minor|/major grows with r or ~O(1) and NOT shrinking in p: NO cancellation => PINNED")
    pr("="*108)

if __name__=="__main__":
    run()
