#!/usr/bin/env python3
"""
probe_wf5A3_salem_zygmund.py  (#444 lane A3 — deterministic Salem-Zygmund / incompressibility)

GOAL: PROVE  M(n) = max_{b!=0} |S_b|,  S_b = sum_{x in mu_n} e_p(b x),  <= C sqrt(n log(p/n)).

mu_n = <h>, n=2^mu, h^{n/2} = -1.  So S_b is REAL:  S_b = 2 sum_{j=0}^{n/2-1} cos(2 pi b h^j / p).

============================================================================
THE A3 SUFFICIENT LEMMA  (deterministic Salem-Zygmund, moment form)
============================================================================
Classical Salem-Zygmund: for a LACUNARY trig polynomial T(t)=sum a_k cos(2pi n_k t + phi_k)
with Hadamard gaps n_{k+1}/n_k >= q>1, one has  ||T||_inf <= C(q) sqrt( (sum a_k^2) log(deg) ).
The mechanism is a deterministic sub-Gaussian moment bound:
   (1/P) sum_t exp(lambda T(t)) <= exp( C lambda^2 sum a_k^2 )   for all real lambda,   (*)
i.e. T is sub-Gaussian with variance proxy  sigma^2 = C * sum a_k^2.
Then a union/Chernov bound over the P=p sample points gives ||T||_inf <= sqrt(2 sigma^2 log p).

For us:  the "signal" is  f(b) = S_b  as b ranges over the m = (p-1)/n COSET reps.
Equivalently fix the worst b and view  S_b = sum_{x in mu_n} cos(theta_x), theta_x = 2 pi b x / p.
The DETERMINISTIC SUB-GAUSSIAN CLAIM we must verify:

   (SG)   for the family { S_b : b in transversal },  E_b[ exp(lambda S_b / sqrt(n)) ] <= exp( C lambda^2 / 2 )
          for all lambda,  with C ABSOLUTE.

(SG) => the max over m points satisfies  M <= sqrt(n) * sqrt(2 C log m) = sqrt(2C) sqrt(n log m),
and log m = log(p/n) (up to O(1)). That is EXACTLY the prize bound.

So the prize bound REDUCES to:  the empirical MGF of S_b/sqrt(n) over the coset family is
sub-Gaussian with an ABSOLUTE variance proxy C (independent of n,p).  This is the
deterministic Salem-Zygmund statement: the 2-power lacunary subgroup makes S_b sub-Gaussian.

PRE-SCREEN: measure  K(lambda) = (1/m) sum_b exp(lambda S_b/sqrt(n))  and check
   sup_lambda [ log K(lambda) - lambda^2 C / 2 ] <= 0  for some absolute C.
Report the smallest such C (the empirical variance proxy) and whether it is n-stable.
Also report the moments: E[S_b]=0?, Var(S_b/sqrt(n)) -> ?, E[(S_b/sqrt n)^4]/Var^2 (kurtosis -> 3 if Gaussian).
"""
import math, sys
import numpy as np

def isp(x):
    if x < 2: return False
    if x % 2 == 0: return x == 2
    d = 3
    while d*d <= x:
        if x % d == 0: return False
        d += 2
    return True

def find_p(n, beta):
    target = int(round(n**beta))
    lo = max(target, 50)
    p = lo + ((1 + n - lo % n) % n)
    if p <= 2: p += n
    while True:
        if p % n == 1 and isp(p):
            return p
        p += n

def primitive_root(p):
    m = p-1
    fs=[]; d=2; mm=m
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

def all_periods(n, p):
    """Return array S_b for b over a transversal of mu_n in F_p^* (m = (p-1)/n reps)."""
    g = primitive_root(p)
    h = pow(g, (p-1)//n, p)
    mu = np.array([pow(h, j, p) for j in range(n)], dtype=np.int64)
    m = (p-1)//n
    gn = pow(g, n, p)
    # b = gn^t for t=0..m-1 hits each coset once
    bs = np.empty(m, dtype=np.int64)
    b = 1
    for t in range(m):
        bs[t] = b
        b = (b * gn) % p
    # S_b = sum_x cos(2 pi b x / p). Vectorize: outer product b*x mod p.
    # m can be large; do in chunks.
    S = np.empty(m, dtype=np.float64)
    chunk = max(1, 2_000_000 // n)
    twopi_over_p = 2.0*math.pi/p
    use_obj = p >= (1<<31)  # b*x may overflow int64 once p~2^31
    for s in range(0, m, chunk):
        e = min(m, s+chunk)
        bb = bs[s:e]
        if use_obj:
            prodm = (bb[:,None].astype(object) * mu[None,:].astype(object)) % p
            prodm = prodm.astype(np.float64)
        else:
            prodm = ((bb[:,None] * mu[None,:]) % p).astype(np.float64)
        S[s:e] = np.cos(twopi_over_p*prodm).sum(axis=1)
    return S, m

def analyze(n, beta):
    p = find_p(n, beta)
    S, m = all_periods(n, p)
    Z = S/math.sqrt(n)            # normalized
    mean = Z.mean(); var = Z.var();
    M = np.abs(S).max()
    logm = math.log(m)
    Cbound = M/math.sqrt(n*logm)  # the prize constant
    # kurtosis
    z2 = ((Z-mean)**2).mean(); z4=((Z-mean)**4).mean()
    kurt = z4/(z2*z2) if z2>0 else float('nan')
    # empirical MGF sub-Gaussian variance proxy:
    # find smallest C with  log mean(exp(lam Z)) <= C lam^2/2  for lam in a grid
    lams = np.linspace(0.1, 4.0, 40)
    worstC = 0.0
    for lam in lams:
        K = np.mean(np.exp(lam*Z))
        if K <= 0 or not np.isfinite(K): continue
        Creq = 2.0*math.log(K)/(lam*lam)
        worstC = max(worstC, Creq)
    # the union bound prediction for M using empirical variance proxy
    M_pred = math.sqrt(n)*math.sqrt(2.0*worstC*logm)
    return dict(n=n,p=p,m=m,M=M,Cbound=Cbound,var=var,kurt=kurt,
                subgC=worstC, M_pred=M_pred, ratio=M/M_pred)

if __name__ == "__main__":
    ns = [int(x) for x in sys.argv[1:]] or [16,32,64,128,256,512,1024]
    beta = 4.0
    print(f"# beta={beta}  prize bound M <= C sqrt(n log(p/n));  SG variance proxy must be ABSOLUTE")
    print(f"{'n':>6} {'p':>12} {'m':>9} {'M':>8} {'C=M/sqrt(nlogm)':>15} {'Var(Z)':>8} {'kurt':>6} {'subG_C':>7} {'M_pred':>8} {'M/Mpred':>8}")
    for n in ns:
        r = analyze(n, beta)
        print(f"{r['n']:>6} {r['p']:>12} {r['m']:>9} {r['M']:>8.3f} {r['Cbound']:>15.4f} {r['var']:>8.4f} {r['kurt']:>6.3f} {r['subgC']:>7.4f} {r['M_pred']:>8.3f} {r['ratio']:>8.4f}")
