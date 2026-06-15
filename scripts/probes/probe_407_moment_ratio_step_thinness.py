#!/usr/bin/env python3
"""
#407 — the SINGLE-STEP monotonicity inequality, made explicit and clean.

f(r)=A_r/Wick_r monotone-decreasing  <=>  A_{r+1}/Wick_{r+1} <= A_r/Wick_r
  <=>  A_{r+1}/A_r <= Wick_{r+1}/Wick_r = (2r+1)!! n^{r+1} / ((2r-1)!! n^r) = (2r+1) * n.

So the monotonicity step IS exactly the clean consecutive-moment ratio bound:
        A_{r+1} / A_r  <=  (2r+1) * n.            (STEP)
A_r = (1/p) sum_{b!=0} |eta_b|^{2r}. By Cauchy-Schwarz / power-mean, A_{r+1}/A_r is a weighted average of
|eta_b|^2 (weights |eta_b|^{2r}/sum), so A_{r+1}/A_r <= max_b |eta_b|^2 = M^2. Thus (STEP) <= (M^2 <= (2r+1)n)
which AT r~log q is EXACTLY the prize (M^2 <= ~2n log q). So (STEP) at deep r ⟺ prize — confirms BGK-hard.
BUT: the question is the SLACK and whether (STEP) is provable at the OPTIMIZER r* via the WEIGHTED average
being << M^2 (the heavy weight |eta_b|^{2r} concentrates on large |eta_b|, so A_{r+1}/A_r -> M^2 as r->inf,
but how fast, and is it < (2r+1)n at r* in THIN?).

DECISIVE: measure g(r) = (A_{r+1}/A_r) / ((2r+1)n)  [STEP holds iff g<=1], in THIN vs THICK, and the
relation A_{r+1}/A_r vs M^2 (how close the weighted-avg is to the sup at r*). Exact FFT spectrum.
HONEST: small n, accessible p; maps the step + its slack, does not prove asymptotic.

RESULT (exact FFT spectrum):
- THIN (prize β 4.0-4.5, n=16,32): g(r)=(A_{r+1}/A_r)/((2r+1)n) <= 1 at EVERY r [STEP holds], AND g(r) is
  itself DECREASING in r (n=32 β=4.5: 0.97,0.94,0.91,0.88,0.85,0.82,0.80) -> the step gets EASIER at deeper
  r in thin (growing margin). (A_{r+1}/A_r)/M^2 stays 0.15-0.8 << 1 -> the consecutive-moment ratio is far
  below the sup at accessible r (heavy tail not yet dominating).
- THICK (maximally-structured n=32/F_4129, β=2.40): g(r)=1.145,1.225,1.167,1.050,... > 1 at low r
  [STEP FAILS], exactly the rungs where A_r > Wick.
=> the single-step monotonicity IS the clean inequality A_{r+1}/A_r <= (2r+1)n; it holds thin with growing
   margin, fails thick. Reframes the open core to this ONE consecutive-moment-ratio bound at r~log q (still
   BGK at deep r since A_{r+1}/A_r -> M^2, but a cleaner provability target with measured growing thin margin).
"""
import numpy as np, math

def is_prime(m):
    if m<2: return False
    if m%2==0: return m==2
    d=3
    while d*d<=m:
        if m%d==0: return False
        d+=2
    return True

def primroot(p):
    def pf(mm):
        f=set(); d=2; m=mm
        while d*d<=m:
            while m%d==0: f.add(d); m//=d
            d+=1
        if m>1: f.add(m)
        return f
    fs=pf(p-1); g=2
    while any(pow(g,(p-1)//q,p)==1 for q in fs): g+=1
    return g

def roots(n,p):
    g=primroot(p); w=pow(g,(p-1)//n,p)
    return [pow(w,i,p) for i in range(n)]

def spec_sq(n,p):
    ind=np.zeros(p)
    for x in roots(n,p): ind[x%p]=1.0
    F=np.fft.fft(ind)
    return (F*np.conj(F)).real

def find_prime(n,beta):
    target=int(n**beta); m=max(1,target//n); best=None
    while True:
        p=m*n+1
        if p>target*1.7: break
        if p>=target*0.6 and is_prime(p):
            if best is None or abs(p-target)<abs(best-target): best=p
        m+=1
    return best

print("="*80)
print("STEP: A_{r+1}/A_r <= (2r+1)n  (= monotonicity of A_r/Wick). g(r)=(A_{r+1}/A_r)/((2r+1)n)<=1?")
print("Also: A_{r+1}/A_r vs M^2 (sup) -- how close the weighted-avg is to the sup.")
print("="*80)
for n in [16,32]:
    rmax=8 if n==16 else 7
    print(f"\n### n={n}")
    for label,betas in [("THIN",[4.0,4.5]),("THICK",[2.4,2.9])]:
        for beta in betas:
            p=find_prime(n,beta)
            if not p: continue
            sq=spec_sq(n,p); nz=sq.copy(); nz[0]=0.0
            M2=float(nz.max())
            be=math.log(p)/math.log(n)
            A=[float(np.sum(nz.astype(object)**r))/p for r in range(1,rmax+2)]
            gs=[]; ratios=[]
            for r in range(1,rmax+1):
                ratio=A[r]/A[r-1]  # A[r] is A_{r+1} index off-by-one: A[0]=A_1,... A[r]=A_{r+1}
                g=ratio/((2*r+1)*n)
                gs.append(g); ratios.append(ratio/M2)
            print(f"  {label} beta={be:.2f} p={p} M^2={M2:.1f} (n^2={n*n}):")
            print(f"     g(r)=(A_r+1/A_r)/((2r+1)n): "+" ".join(f"{v:.3f}" for v in gs)
                  +f"  STEP-holds={'Y' if all(v<=1+1e-9 for v in gs) else 'N'}")
            print(f"     (A_r+1/A_r)/M^2:           "+" ".join(f"{v:.3f}" for v in ratios))
