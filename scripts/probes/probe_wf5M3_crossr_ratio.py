#!/usr/bin/env python3
"""
wf-M3 pre-screen: the ADDITIVE-DEPTH recursion E_{r+1}(mu_n) = n*E_r + cross_r.
cross_r = sum_{s,t in G, s!=t} C_r(s-t),  C_r(d) = sum_e f_r(e) f_r(e+d), f_r = r-fold sumset freq.
E_r = C_r(0) = sum_d f_r(d)^2.

TARGET: E_r <= (2r-1)!! n^r  (char-0 Lam-Leung ceiling, depth r ~ ln q).
Per-step sufficient lemma to PRESERVE the target inductively:
  if E_r <= (2r-1)!! n^r then need E_{r+1} <= (2r+1)!! n^{r+1}.
  E_{r+1} = n E_r + cross_r <= (2r+1)!! n^{r+1}  <=>  cross_r <= [(2r+1)!! - (2r-1)!!] n^{r+1}... 
  but careful: E_r may be < target. Cleanest RATIO test: define rho_r := cross_r / E_r.
  Then E_{r+1} = (n + rho_r) E_r. Target ratio E_{r+1}/E_r should be ~ (2r+1) n.
  So SUFFICIENT LEMMA (M3):  cross_r <= 2r * n * E_r   <=>   rho_r := cross_r/E_r <= 2r*n.
  (Because (2r+1)!! n^{r+1} / [(2r-1)!! n^r] = (2r+1) n = n + 2r*n.)
We measure rho_r = cross_r/E_r and compare to 2r*n across n,r. We work CHAR-0 (over Z): 
mu_n char-0 = the n-th roots of unity; f_r(d) counts r-subsets of roots summing to d. 
For char-0 we use the integer-exponent surrogate: G = Z/n under ADDITION is NOT the subgroup;
the real object is multiplicative mu_n embedded in C (or F_p). Char-0 E_r = additive energy of 
the n-th roots of unity in C. We compute it via the polynomial-coefficient model: 
roots zeta^0..zeta^{n-1}; sum of r of them (with repetition, ordered) = a Gaussian integer in Z[zeta].
f_r(d) for d in Z[zeta]. Exact but Z[zeta] is big. 
INSTEAD: compute char-p E_r exactly for moderate p,n (the TRUE prize object) and the ratio.
"""
import numpy as np
from math import comb

def double_fact(k):
    # (2r-1)!! for k=2r-1
    p=1
    while k>0:
        p*=k; k-=2
    return p

def Er_charp(p, n, r):
    """Exact E_r(mu_n) over F_p via freq array f_r over F_p (length p). 
    mu_n = n-th roots of unity in F_p (n | p-1). f_1 = indicator of mu_n.
    f_{r+1}(d) = sum_{s in G} f_r(d-s) : convolve with indicator of G (cyclic over F_p additive group)."""
    # find a generator of mu_n
    g = None
    for cand in range(2,p):
        # order of cand
        x=cand; o=1
        while x!=1:
            x=(x*cand)%p; o+=1
            if o>p: break
        if o==(p-1):
            g=cand; break
    h=pow(g,(p-1)//n,p)  # primitive n-th root
    G=set()
    x=1
    for _ in range(n):
        G.add(x); x=(x*h)%p
    G=sorted(G)
    ind=np.zeros(p,dtype=object)
    for s in G: ind[s]=1
    f=ind.copy()
    for _ in range(r-1):
        # circular convolution over Z/p additive: f_new[d] = sum_{s in G} f[(d-s)%p]
        fnew=np.zeros(p,dtype=object)
        farr=f
        for s in G:
            fnew += np.roll(farr, s)  # roll by s: fnew[d]+=f[d-s]
        f=fnew
    Er=int((f.astype(object)**2).sum())
    return Er, G, f, ind

def crossr(p,n,r):
    Er, G, f, ind = Er_charp(p,n,r)
    # cross_r = sum_{s,t in G, s!=t} C_r(s-t), C_r(d)=sum_e f(e) f(e+d)
    # = sum over offsets delta of (#pairs s,t in G with s-t=delta) * C_r(delta), minus diag (delta=0 incl s=t)
    # easier: total = sum_{s,t in G} C_r(s-t); diag s=t gives |G|*C_r(0)=n*Er; cross = total - n*Er
    # autocorr C_r(delta) = sum_e f[e]*f[(e+delta)%p]  -> full autocorrelation = correlate
    fi = f.astype(np.float64)  # use float for fft-free direct; n small
    # C_r as array indexed by delta in F_p:
    C = np.zeros(p, dtype=object)
    for delta in range(p):
        C[delta] = int((f * np.roll(f, -delta)).sum())  # sum_e f[e] f[e+delta]
    total = 0
    for s in G:
        for t in G:
            total += C[(s-t)%p]
    cross = total - n*Er
    return Er, cross

print(f"{'p':>6} {'n':>4} {'r':>3} {'E_r':>18} {'cross_r':>20} {'cross/E':>12} {'2r*n':>8} {'ok?':>4}")
for (p,n) in [(257,16),(257,32),(193,16),(241,16),(241,24),(769,16),(769,32),(673,32),(577,8),(577,16)]:
    if (p-1)%n: continue
    for r in range(1,7):
        try:
            Er, cross = crossr(p,n,r)
        except Exception as e:
            print(f"{p:>6} {n:>4} {r:>3}  ERR {e}"); continue
        if Er==0: 
            print(f"{p:>6} {n:>4} {r:>3} {Er:>18} {cross:>20}  E=0"); continue
        ratio = cross/Er
        tgt = 2*r*n
        ok = "Y" if ratio<=tgt+1e-9 else "N"
        print(f"{p:>6} {n:>4} {r:>3} {Er:>18} {cross:>20} {ratio:>12.3f} {tgt:>8} {ok:>4}")
