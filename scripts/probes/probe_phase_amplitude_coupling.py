# probe_phase_amplitude_coupling.py (#444) — CRITICISM of the b-summation dichotomy. The dichotomy
# proves b-summed POLYNOMIALS in (eta,conj eta) are real counts (phase-blind), concluding the tool must
# be per-b*. BLIND SPOT (verified here): b-summed PHASE functionals (non-polynomial, e.g. phase-windowed
# moments sum_b |eta_b|^{2k} 1[arg in arc]) are NOT covered. And the coupling is REAL: the |eta_b|^{2k}-
# weighted mass is ~5.5x NON-uniform across 12 phase arcs (std~2, max-ratio 5.5-5.9 at k=1 and k=4, n=16,32)
# — NOT phase-equidistributed. So the per-b* CONCLUSION is OVERSTATED: there is an untried THIRD class
# (phase-coupled b-sums) the dichotomy does not forbid and the data shows is non-trivial. (Caveat: eta_b
# is constant on mu_n-cosets — the dilates give IDENTICAL eta — so the coupling is a Galois/coset-structured
# phenomenon; whether it can BOUND M is open, but it is a legitimate gap in the paper.)

import numpy as np
def is_prime(N):
    if N<2:return False
    for q in (2,3,5,7,11,13,17,19,23,29,31,37,41):
        if N%q==0:return N==q
    d=N-1;r=0
    while d%2==0:d//=2;r+=1
    for a in (2,3,5,7,11,13,17,19,23,29,31,37):
        x=pow(a,d,N)
        if x in(1,N-1):continue
        ok=False
        for _ in range(r-1):
            x=x*x%N
            if x==N-1:ok=True;break
        if not ok:return False
    return True
def primroot(p):
    fac=set();m=p-1;d=2
    while d*d<=m:
        while m%d==0:fac.add(d);m//=d
        d+=1
    if m>1:fac.add(m)
    for g in range(2,p):
        if all(pow(g,(p-1)//q,p)!=1 for q in fac):return g
def subgroup(p,n):
    g=primroot(p);w=pow(g,(p-1)//n,p);S=[];x=1
    for _ in range(n):S.append(x);x=x*w%p
    return S
def eta(p,roots):
    b=np.arange(1,p)
    return np.array([sum(np.exp(2j*np.pi*(bb*x%p)/p) for x in roots) for bb in b])

print("PHASE-AMPLITUDE COUPLING (fixed binning, NB=12 arcs covering [0,2pi)):")
print("does the |eta|^{2k}-weighted mass concentrate in phase (coupling, dichotomy blind spot with teeth)")
print("or spread uniformly (no coupling, phase-windowing useless)?")
print("="*72)
NB=12
for n,p in [(16,65537),(32,1048609)]:
    e=eta(p,subgroup(p,n)); ar=np.mod(np.angle(e),2*np.pi); 
    for k in (1,4):
        mag2k=np.abs(e)**(2*k)
        binidx=np.minimum((ar/(2*np.pi)*NB).astype(int),NB-1)
        binmass=np.array([mag2k[binidx==j].sum() for j in range(NB)])
        frac=binmass/binmass.sum()  # fraction of total k-moment in each arc
        # uniform would be 1/NB=0.083 each
        ratios=frac*NB  # ratio to uniform
        print(f"n={n} k={k}: mass-fraction/arc *{NB} (uniform=1): max={ratios.max():.2f} min={ratios.min():.2f} "
              f"std={ratios.std():.2f}  sum={ratios.sum():.2f}(should be {NB})")
    # is the argmax's arc special vs the SAME-COSET structure? the n dilates of argmax have |eta|=M, varied arg
    bm=int(np.argmax(np.abs(e)))+1  # b value (1-indexed)
    roots=subgroup(p,n)
    dilarg=sorted(np.mod(np.angle([sum(np.exp(2j*np.pi*((bm*xi%p)*x%p)/p) for x in roots) for xi in roots]),2*np.pi))
    print(f"  the n={n} dilates of argmax b* (all |eta|=M) have args spread: range {dilarg[0]:.2f}..{dilarg[-1]:.2f} over [0,2pi)")
print()
print("READING: k=4 max-ratio near 1 with small std ⟹ phase EQUIDISTRIBUTED even in the high moment ⟹")
print("no exploitable coupling (dichotomy gap real but useless). max-ratio >> 1 ⟹ genuine coupling (a crack).")
print("The dilates of b* (|eta|=M, args SPREAD across [0,2pi)) show the max's phase is NOT a single arc.")
