#!/usr/bin/env python3
"""
LANE A1: Phase-aware dyadic-transfer spectral radius probe.

Setup. Fix prime p, n=2^mu | p-1. The Gauss-period vector at level n is
  S^{(n)}_b = sum_{x in mu_n} e_p(b x),   b ranging over F_p^* (coset-constant in b mod mu_n).
Doubling identity (EXACT):  S^{(2n)}_b = S^{(n)}_b + S^{(n)}_{zeta b},  zeta of order 2n, zeta^2 in mu_n.

The MAGNITUDE recursion M(2n)^2 <= 2 M(n)^2 is FALSE (phase alignment).
Lane A1 question: the *operator* viewpoint. Consider the linear map on C^{F_p^*} (or on the
quotient by mu_n) that the doubling induces. Its operator norm controls growth.

We measure several candidate "spectral radii" of the relative-phase transfer:

(A) Naive magnitude ratio rho_mag = M(2n)/M(n) -- known to exceed sqrt2 (refuted).
(B) L2-operator ratio: ||S^{(2n)}||_2 / ||S^{(n)}||_2 over the coset transversal.
    By Parseval this is EXACTLY sqrt2 (domain doubles) -- the second-moment wall. Confirm.
(C) The PHASE-AWARE pointwise transfer T: at each b define the 2x2 (or scalar-complex)
    map carrying (S^{(n)}_b, S^{(n)}_{zeta b}) -> S^{(2n)}_b. The relevant "spectral radius
    in the RS-restricted sector" = sup over b of the GROWTH FACTOR of |S^{(2n)}_b| relative
    to the LOCAL pair-rms sqrt((|S^{(n)}_b|^2+|S^{(n)}_{zeta b}|^2)/?) ... we measure the
    pointwise amplification a(b) = |S^{(n)}_b + S^{(n)}_{zeta b}| / max(|S^{(n)}_b|,|S^{(n)}_{zeta b}|).
    This is the honest "did the worst child grow" factor. a(b) in [0,2]; a<=sqrt2 would save us.

We report, at the WORST parent b* (the maximizer of |S^{(2n)}|):
  - ratio M(2n)/M(n)
  - the relative phase theta between the two children at b*
  - amplification vs the LARGER child |S^{(2n)}_{b*}| / max(child)
  - amplification vs the parent-level max |S^{(2n)}_{b*}| / M(n)   (==ratio, the key quantity)
And the GLOBAL sup of these over all b, which is the true spectral radius of T.
"""
import numpy as np, math

def is_prime(x):
    if x<2: return False
    i=2
    while i*i<=x:
        if x%i==0: return False
        i+=1
    return True

def find_prime(n, lo):
    # p = 1 mod 2n (so both mu_n and mu_{2n} exist), near lo
    p = lo + ((1 - lo) % (2*n))
    if p < 3: p += 2*n
    while not is_prime(p): p += 2*n
    return p

def primitive_root(p):
    m=p-1; fs=[]; d=2; mm=m
    while d*d<=mm:
        if mm%d==0:
            fs.append(d)
            while mm%d==0: mm//=d
        d+=1
    if mm>1: fs.append(mm)
    g=2
    while True:
        if all(pow(g,(p-1)//f,p)!=1 for f in fs): return g
        g+=1

def gauss_vec(p, sub, b_list):
    # returns S_b for each b in b_list (vectorized over x in sub)
    sub=np.array(sub, dtype=np.int64)
    out=np.empty(len(b_list), dtype=np.complex128)
    for i,b in enumerate(b_list):
        t = (b*sub) % p
        ang = 2*math.pi*t/p
        out[i] = np.cos(ang).sum() + 1j*np.sin(ang).sum()
    return out

print("n     p        M(2n)/M(n)  theta@b*  amp_vs_child@b*  GLOBAL_sup_ratio  GLOBAL_sup_amp  L2ratio")
for mu in [4,5,6,7]:
    n=2**mu; twon=2*n
    p=find_prime(n, max(50021, n**4))   # beta~4 prize-ish
    g=primitive_root(p)
    # mu_{2n}: zeta=g^{(p-1)/2n}, order 2n. mu_n = squares of mu_{2n}.
    zeta=pow(g,(p-1)//twon,p)
    mu2n=[pow(zeta,i,p) for i in range(twon)]
    mun =[pow(zeta,2*i,p) for i in range(n)]   # = mu_n
    # transversal of mu_{2n} in F_p^*: b = g^j, j=0..m2-1, m2=(p-1)/2n cosets
    m2=(p-1)//twon
    gn2=pow(g,twon,p)
    bs=[]; b=1
    for _ in range(m2): bs.append(b); b=(b*gn2)%p
    bs=np.array(bs,dtype=np.int64)
    # S^{(2n)}_b and children S^{(n)}_b, S^{(n)}_{zeta b}
    S2 = gauss_vec(p, mu2n, bs)
    Sa = gauss_vec(p, mun,  bs)
    Sb = gauss_vec(p, mun,  (zeta*bs)%p)
    # check identity S2 = Sa + Sb
    err=np.max(np.abs(S2-(Sa+Sb)))
    assert err<1e-6, f"identity broken err={err}"
    # M(2n)=max|S2|, M(n)=max over the FULL F_p^* of |S^{(n)}|. Since mu_n is index-2 coarser,
    # S^{(n)} over the transversal {bs, zeta*bs} covers all cosets of mu_n. So:
    childmags = np.concatenate([np.abs(Sa), np.abs(Sb)])
    Mn = childmags.max()
    M2n = np.abs(S2).max()
    ratio = M2n/Mn
    # at b* (argmax of |S2|):
    istar=np.argmax(np.abs(S2))
    a,b_=Sa[istar],Sb[istar]
    theta=abs(np.angle(a/b_)) if abs(b_)>1e-12 and abs(a)>1e-12 else 0.0
    amp_child_star = np.abs(S2[istar])/max(abs(a),abs(b_))
    # GLOBAL sup amplification a(b)=|Sa+Sb|/max(|Sa|,|Sb|)
    denom=np.maximum(np.abs(Sa),np.abs(Sb))
    amp = np.abs(S2)/np.maximum(denom,1e-15)
    sup_amp=amp.max()
    # L2 ratio
    l2ratio = math.sqrt((np.abs(S2)**2).sum() / (np.abs(Sa)**2).sum())  # vs ONE child-coset family
    print(f"{twon:<5} {p:<8} {ratio:10.4f}  {theta:7.4f}  {amp_child_star:14.4f}   {ratio:14.4f}   {sup_amp:12.4f}  {l2ratio:.4f}   sqrt2={math.sqrt(2):.4f}")
