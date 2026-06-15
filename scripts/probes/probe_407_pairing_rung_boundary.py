import numpy as np
import sympy

# Sharpen the pairing-residual refutation: for fixed prize (n, q), at WHICH r does the raw
# E_r <= Wick (=> H, the antipodal pairing) FIRST FAIL? i.e. which rungs of the K1/pairing route
# are vacuous at prize and which survive. The DC term n^{2r}/q crosses Wick=(2r-1)!!*n^r at some r*(n,q).
# Lower rungs r < r* keep E_r <= Wick (pairing route OK); rungs r >= r* are prize-DEAD (H false).
# Verify EXACTLY via FFT: E_r = (1/q) sum_all |eta_b|^{2r}, compare to Wick.

def dfac(r):
    p = 1.0; k = 2*r-1
    while k >= 1:
        p *= k; k -= 2
    return p

def prime_sub(n, beta):
    p = sympy.nextprime(int(n**beta))
    while (p-1) % n != 0:
        p = sympy.nextprime(p)
    return p

def period_sq(n, p):
    g = sympy.primitive_root(p); h = pow(g,(p-1)//n,p)
    G=set(); x=1
    for _ in range(n):
        G.add(x); x=(x*h)%p
    ind=np.zeros(p)
    for x in G: ind[x]=1.0
    return np.abs(np.fft.fft(ind))**2

for (n, beta) in [(32,4.5),(64,4.0),(128,3.4),(256,3.0)]:
    p = prime_sub(n, beta); a = period_sq(n, p); q = float(p)
    rstar_dc = None       # first r where DC term n^{2r}/q > Wick (predicts raw E_r>Wick)
    rstar_exact = None    # first r where EXACT E_r > Wick
    lnq = int(round(np.log(q)))
    print(f"n={n} beta={beta} p={p} round(ln q)={lnq}")
    for r in range(1, lnq+4):
        Er = (a**r).sum() / q              # exact full moment E_r
        wick = dfac(r) * (n**r)
        dc = (n**(2*r)) / q                # DC term lower bound on E_r
        if rstar_dc is None and dc > wick: rstar_dc = r
        if rstar_exact is None and Er > wick: rstar_exact = r
    print(f"   raw E_r <= Wick first FAILS (exact) at r*={rstar_exact}   (DC-predicted r*={rstar_dc})   [pairing route H vacuous for r >= r*]")
    # show a few rungs around the boundary
    lo = max(1,(rstar_exact or lnq)-2); hi = (rstar_exact or lnq)+2
    for r in range(lo, hi+1):
        Er=(a**r).sum()/q; wick=dfac(r)*(n**r)
        print(f"      r={r}: E_r/Wick={Er/wick:.3f}  {'E_r<=Wick (H ok)' if Er<=wick else 'E_r>Wick (H FALSE)'}")
