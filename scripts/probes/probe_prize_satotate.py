#!/usr/bin/env python3
"""
Sato-Tate moment test of the subgroup Gauss sums (the exact open question,
cheap via coset symmetry).

eta_b constant on (p-1)/n cosets of mu_n. Normalized moment
M_r(p) = (1/#cosets) Sum_C |eta_C|^{2r} / n^r. Gaussian/chi^2 baseline: M_r ->
(2r-1)!! (complex Gaussian: actually E|Z|^{2r}=r! n^r for CN(0,n); for these
real-structured sums the baseline is the Bessel (2r-1)!! per the energy). Test
which r the moments track (2r-1)!! [or r!], and where they diverge, vs p ~ n^beta.
If M_r ~ (2r-1)!! up to r~log p (and >= no blow-up), supports the conjecture
(clean to r~log p => closes). If diverges early, locates r_max(p).
Cheap: only (p-1)/n coset reps.
"""
import cmath, math

def find_prime(n, lo):
    c=(lo//n+1)*n+1
    while True:
        if c>2 and all(c%d for d in range(2,int(c**0.5)+1)): return c
        c+=n
def subgroup(p,n):
    for g in range(2,p):
        h=pow(g,(p-1)//n,p)
        if pow(h,n,p)==1 and all(pow(h,j,p)!=1 for j in range(1,n)):
            return [pow(h,t,p) for t in range(n)], g
    raise RuntimeError
def df(r):
    v=1
    for k in range(1,r+1): v*=(2*k-1)
    return v

def coset_moments(p, n, Rmax):
    H,g=subgroup(p,n)
    # coset reps: g0=1..(p-1)/n via powers of a generator of F_p* mod mu_n
    # simplest: b ranges over all F_p*, eta_b constant on cosets; sample one b per coset
    # mu_n = H; cosets = {b*H}. iterate b, track seen cosets.
    seen=set(); reps=[]
    for b in range(1,p):
        key=min((b*x)%p for x in H)  # canonical coset rep
        if key not in seen:
            seen.add(key); reps.append(b)
    mom=[0.0]*(Rmax+1)
    for b in reps:
        e=abs(sum(cmath.exp(2j*math.pi*((b*x)%p)/p) for x in H))**2
        for r in range(1,Rmax+1): mom[r]+= e**r
    nc=len(reps)
    return [mom[r]/nc/n**r for r in range(1,Rmax+1)], nc

print("Sato-Tate moments M_r = avg|eta_C|^{2r}/n^r  vs Gaussian (2r-1)!!  [ratio M_r/(2r-1)!!]")
for (n,beta) in [(8,3),(8,4),(16,3),(16,4)]:
    p=find_prime(n, max(60, int(n**beta)))
    if p>500000: print(f"n={n} beta={beta} p={p} too big"); continue
    Rmax=min(8, int(2*math.log2(p)))
    M,nc=coset_moments(p,n,Rmax)
    ratios=[f"r{r}:{M[r-1]/df(r):.2f}" for r in range(1,Rmax+1)]
    # r_max = largest r with ratio in [0.7,1.5]
    rmax=0
    for r in range(1,Rmax+1):
        if 0.6 <= M[r-1]/df(r) <= 1.6: rmax=r
        else: break
    print(f"n={n} p={p}(~n^{beta}) #cosets={nc} log2p={math.log2(p):.1f}: "
          f"r_max~{rmax} | {' '.join(ratios)}")
