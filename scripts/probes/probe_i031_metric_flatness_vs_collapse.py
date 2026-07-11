#!/usr/bin/env python3
"""I031 STEP (b)-i: reconcile the two competing claims about the QUOTIENT chaining metric.

CLAIM A (I031 handle): orbit-invariance collapses entropy log p -> log m, recovering exponent 1/2.
CLAIM B (Salem-Zygmund self-refutation, kb 2026-06-13): the chaining metric is FLAT
   d(c,c') ~ sqrt(2n) for ALL distinct quotient pairs => gamma_2 = union bound, no chaining gain.

These are consistent ONLY if the gain is purely the index-count reduction (m points not p),
NOT multi-scale geometry. This probe MEASURES the metric directly to settle it:

  d(b,b')^2 = E|eta_b - eta_{b'}|^2  (covariance-induced L2 metric of the MATCHED Gaussian process)
            = Cov(b,b)+Cov(b',b')-2Re Cov(b,b'),  Cov(b,b') = E_g [ G_b conj(G_{b'}) ]
For G_b = sum_x g_x e_p(b x), g_x iid std complex normal:
  Cov(b,b') = sum_x e_p((b-b')x) = eta_{b-b'}... NO: = sum_{x in mu_n} e_p((b-b')x) = eta at freq (b-b')
  -- i.e. the covariance of the matched Gaussian process IS the deterministic period at the difference
     frequency. Cov(b,b) = n. So d(b,b')^2 = 2n - 2 Re eta_{b-b'}.
This is the EXACT covariance structure the task asks for (step i). Measure its spread over the quotient.

PROPER REGIME: p prime, n=2^mu, n|p-1, p>>n^3, NEVER n=p-1.
"""
import cmath, math, numpy as np

def isprime(m):
    if m < 2: return False
    if m % 2 == 0: return m == 2
    d=m-1;s=0
    while d%2==0: d//=2;s+=1
    for a in [2,3,5,7,11,13,17,19,23,29,31,37]:
        if a%m==0: continue
        x=pow(a,d,m)
        if x==1 or x==m-1: continue
        ok=False
        for _ in range(s-1):
            x=x*x%m
            if x==m-1: ok=True;break
        if not ok: return False
    return True
def find_prime(mu,beta):
    n=1<<mu; lo=int(n**beta); t=((lo//n)+1)*n+1
    while True:
        if isprime(t): return n,t
        t+=n
def subgroup(p,n):
    fac=[];x=p-1;d=2
    while d*d<=x:
        if x%d==0:
            fac.append(d)
            while x%d==0: x//=d
        d+=1
    if x>1: fac.append(x)
    g=None
    for c in range(2,p):
        if all(pow(c,(p-1)//q,p)!=1 for q in fac): g=c;break
    h=pow(g,(p-1)//n,p)
    H=[pow(h,i,p) for i in range(n)]
    assert len(set(H))==n and pow(h,n//2,p)!=1
    return g,h,H

print("I031 STEP(b)-i: the matched-Gaussian covariance is Cov(b,b')=eta_{b-b'}; d(b,b')^2=2n-2Re eta_{b-b'}.")
print("Test: is the QUOTIENT metric FLAT (~sqrt 2n) or does it have multi-scale structure?")
print(f"{'n':>4}{'beta':>5}{'p':>9}{'m':>8}  {'sqrt2n':>7}  {'d_min':>7}{'d_med':>7}{'d_max':>7}  {'frac<.5diam':>11}{'frac<.25diam':>12}")
for mu,beta in [(2,4.0),(3,4.0),(4,4.0),(5,4.0),(6,3.6)]:
    n,p=find_prime(mu,beta)
    g,h,H=subgroup(p,n)
    w=2*math.pi/p; m=(p-1)//n
    Hn=np.array(H,dtype=np.int64)
    # quotient coset reps: g^0,...,g^{m-1}. eta at a difference freq c: sum_x e_p(c x).
    # We measure d(b,b') for b,b' coset reps. Differences (b-b') range over F_p; eta_{c} computed.
    reps=np.array([pow(g,c,p) for c in range(m)],dtype=np.int64)
    if m>2000:
        idx=np.linspace(0,m-1,2000).astype(np.int64); reps=reps[idx]
    R=len(reps)
    # sample pairs
    rng=np.random.default_rng(7)
    npair=min(R*(R-1)//2, 4000)
    ii=rng.integers(0,R,npair); jj=rng.integers(0,R,npair)
    mask=ii!=jj; ii=ii[mask]; jj=jj[mask]
    c=(reps[ii]-reps[jj])%p   # difference frequencies
    # eta_c = sum_{x in mu_n} e_p(c x)
    prod=(c[:,None]*Hn[None,:])%p
    eta_c=np.exp(1j*w*prod).sum(axis=1)
    d2=2*n-2*eta_c.real
    d2=np.maximum(d2,0.0)
    d=np.sqrt(d2)
    diam=d.max()
    sqrt2n=math.sqrt(2*n)
    f_half=float(np.mean(d<0.5*diam))
    f_quart=float(np.mean(d<0.25*diam))
    print(f"{n:>4}{beta:>5.1f}{p:>9}{m:>8}  {sqrt2n:>7.2f}  {d.min():>7.2f}{np.median(d):>7.2f}{d.max():>7.2f}  {f_half:>11.3f}{f_quart:>12.3f}")
print()
print("If d_med ~ d_max ~ sqrt(2n) and frac<.5diam tiny => FLAT (Salem-Zygmund refutation holds):")
print("  the I031 gain is ONLY the index reduction p->m (union bound over m), NOT multi-scale chaining.")
print("If frac<.5diam, frac<.25diam substantial => genuine multi-scale geometry, chaining buys more.")
