import itertools, cmath, math
import numpy as np
TAU=2*math.pi
def incidence_band(n,k,a,b,w):
    gammas=set()
    for S in itertools.combinations(range(n),w):
        xs=[cmath.exp(1j*TAU*s/n) for s in S]
        V=np.array([[x**c for c in range(k)] for x in xs],dtype=complex)
        va=np.array([x**a for x in xs],dtype=complex); vb=np.array([x**b for x in xs],dtype=complex)
        Vp=np.linalg.pinv(V)
        ra=va-V@(Vp@va); rb=vb-V@(Vp@vb)
        na=np.linalg.norm(ra); nb=np.linalg.norm(rb)
        if nb<1e-9: continue
        if na<1e-9: gammas.add(0j); continue
        lam=np.vdot(rb,ra)/np.vdot(rb,rb)
        if np.linalg.norm(ra-lam*rb)<1e-6*na:
            g=-lam; gammas.add(round(g.real,3)+1j*round(g.imag,3))
    return len(gammas)
def deltastar(n,k):
    budget=n; best_ds=1.0  # worst (smallest) delta* over directions
    fars=list(range(k,n))
    for a,b in itertools.combinations(fars,2):
        ds=None
        for w in range(k+1,n):
            if incidence_band(n,k,a,b,w)<=budget: ds=1-w/n; break
        if ds is not None and ds<best_ds: best_ds=ds; wa=(a,b)
    return best_ds,wa
print("Residual 2 across rates: delta* and c=(1-rho-delta*)*log2 n  [formula delta*=(1-rho)(1-1/log2 n) => c=1-rho]:")
for (n,k) in [(8,2),(16,4),(8,4),(16,8)]:
    rho=k/n; ds,wa=deltastar(n,k); gap=(1-rho)-ds; c=gap*math.log2(n)
    pred=(1-rho)*(1-1/math.log2(n))
    print(f"  n={n} k={k} rho={rho}: delta*={ds:.4f} (worst dir {wa}); c=(1-rho-d*)log2 n={c:.3f}; 1-rho={1-rho:.3f}; formula pred={pred:.4f} {'MATCH' if abs(ds-pred)<0.02 else 'differ'}")

# RESULT (2026-06-14) -- residual 2 (exact char-0 delta* formula):
# WORST-direction char-0 over-det delta* (incidence crosses budget n), q-independent:
#   rho=1/4: n=8 delta*=0.375 (dir 4,7), n=16 delta*=0.5625 (dir 4,6)
#   rho=1/2: n=8 delta*=0.250 (dir 4,5), n=16 delta*=0.3125 (dir 8,10)
# c=(1-rho-delta*)*log2 n: rho=1/4 -> 1.125, 0.75 (NOT constant); rho=1/2 -> 0.75, 0.75.
# => the clean candidate delta*=(1-rho)(1-1/log2 n) [c=1-rho] is REFUTED by the WORST direction
#    (it held only for a NON-worst single direction). Exact asymptotic delta* NOT pinnable from
#    n=8,16; this is the genuine OPEN combinatorial residual (R4 feasibility ~5, #400/#389 orbit
#    count). NOTE: this is the CHAR-0 (decidable-per-n, decoupled) count, NOT the BGK char-sum.
