#!/usr/bin/env python3
# ZP follow-up: is the orbit count N a DEGREE parameter (poly-in-n via effective ZP) or a DIMENSION
# parameter (doubly-exp)? Reframe: the bad-gamma set for direction (a,b) at agreement w lives in the
# 1-PARAMETER line pencil {x^a + gamma x^b}. Via Vieta gamma=-h_{a-k}(S)/h_{b-k}(S), the bad gammas at
# band w are the VALUES of a fixed RATIONAL FUNCTION on the consistency variety. N = # distinct
# dilation-orbits = # distinct gamma values up to the dilation action gamma->gamma*zeta^{b-a}.
# KEY TEST: does N(n) (the binding orbit count, GPU) grow like a DEGREE (poly in n) or worse?
# GPU data ρ=1/4: at the binding band s*, N collapses to ~1; but track N just ABOVE binding (s*-1)
# where the gap to budget lives. Measure N(n) at fixed over-det depth c across n -> poly or exp?
import cmath, math, itertools
def musub(n,p,g):
    h=pow(g,(p-1)//n,p); return [pow(h,j,p) for j in range(n)]
import sympy
def orbitcount_at(n,k,a,b,w,p):
    g=sympy.primitive_root(p); G=musub(n,p,g); zb=pow(G[1],(b-a)%n,p) if (b-a)%n<n else 1
    # bad gammas: x^a+gamma x^b agrees with deg<k poly on a w-subset -> gamma = -residual ratio
    import numpy as np
    roots=[cmath.exp(2j*math.pi*j/n) for j in range(n)]
    gammas=set()
    cnt=0
    for S in itertools.combinations(range(n),w):
        xs=[roots[s] for s in S]
        V=np.array([[x**c for c in range(k)] for x in xs],dtype=complex)
        va=np.array([x**a for x in xs]); vb=np.array([x**b for x in xs])
        Vp=np.linalg.pinv(V); ra=va-V@(Vp@va); rb=vb-V@(Vp@vb)
        na=np.linalg.norm(ra); nb=np.linalg.norm(rb)
        if nb<1e-9: continue
        if na<1e-9: gammas.add(0j); continue
        lam=np.vdot(rb,ra)/np.vdot(rb,rb)
        if np.linalg.norm(ra-lam*rb)<1e-6*na: gammas.add(round((-lam).real,4)+1j*round((-lam).imag,4))
        cnt+=1
        if cnt>3_000_000: return None
    # collapse by dilation orbit gamma->gamma*zeta_n^{b-a}
    zr=cmath.exp(2j*math.pi*((b-a)%n)/n)
    seen=set(); orbits=0
    gl=[g_ for g_ in gammas if abs(g_)>1e-9]
    pool=set((round(g_.real,3),round(g_.imag,3)) for g_ in gl)
    while pool:
        g0=pool.pop(); z=complex(*g0); orbits+=1
        for _ in range(n):
            z=z*zr; pool.discard((round(z.real,3),round(z.imag,3)))
    return orbits, len(gammas)
print("N(n) = binding-band dilation-orbit count, worst dir (n/4,5n/8), at over-det depth c=2 (just above Johnson):")
print(f"{'n':>5}{'k':>4}{'dir':>10}{'w':>4}{'#orbits N':>10}{'#gammas':>9}{'N vs n':>10}")
for n in [8,16,24]:
    k=n//4; a=n//4; b=5*n//8; w=k+2
    if not(k<=a<b<n): continue
    p=sympy.nextprime(n**4); 
    while (p-1)%n: p=sympy.nextprime(p)
    r=orbitcount_at(n,k,a,b,w,p)
    if r is None: print(f"{n:>5}{k:>4}{'(%d,%d)'%(a,b):>10}{w:>4}{'>cap':>10}"); continue
    orb,ng=r
    print(f"{n:>5}{k:>4}{'(%d,%d)'%(a,b):>10}{w:>4}{orb:>10}{ng:>9}{'%.2f'%(orb/n) if orb else 0:>10}")
print()
print("READ: if N grows POLY in n (e.g. ~n, ~n^2) => effective-ZP-on-pencil could give N<=poly(n) (NEW handle).")
print("      if N exp / erratic => stays orbit-count-open. (degree param = poly; dimension param = exp.)")
