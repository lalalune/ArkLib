#!/usr/bin/env python3
"""
#407 cumulant-deep-nonbetti  --  routes (B) hypercontractivity and (C) tower martingale.

KEY MEASURED FACT (from _cumulant_nonbetti_lab): kappa_r DECREASING in r, kurtosis<3 -> the period
measure is sub-Gaussian with BOUNDED support [-n,n].  We test the two non-Betti mechanisms that
could PROVE sub-Gaussianity to depth ln m without Betti:

(C) TOWER MARTINGALE.  mu_{2n} = mu_n cup (zeta * mu_n) where zeta = primitive 2n-th root, zeta^2=g0
    a generator of mu_n's... no: mu_n subset mu_{2n}, [mu_{2n}:mu_n]=2, mu_{2n}=mu_n cup w*mu_n,
    w^2 in mu_n.  Then eta^{(2n)}_b = sum_{x in mu_{2n}} e_p(bx) = eta^{(n)}_b + eta^{(n)}_{b w}.
    So the order-2n period is the SUM OF TWO order-n periods (b and bw, DIFFERENT cosets).
    Increment view: build mu_n = mu_2 < mu_4 < ... < mu_{2^a} as a depth-a tower; at each level
    eta doubles via eta_{level k+1, b} = eta_{level k, b} + eta_{level k, b w_k}.
    Martingale question: are the two summands eta_{k,b}, eta_{k, b w_k} approximately INDEPENDENT
    (decorrelated)?  If so, the period at level a is a sum of ~"2-independent" increments and
    sub-Gaussianity follows by a martingale/Azuma-type bound -> NON-BETTI deep cumulant control.
    Measure: corr(eta_{k,b}, eta_{k,b w_k}) over b; and the conditional-variance flatness.

(B) HYPERCONTRACTIVITY.  Is eta_b a LOW-DEGREE function on a product space?  The natural product:
    index the m cosets by the quotient group Q = F_p*/mu_n ~ Z/m.  Walsh/Fourier-on-Z/m expansion
    of the period sequence (eta_i)_{i in Z/m}.  Its DFT is exactly chi-bar(b) tau(chi) (Gauss sums),
    which are UNIMODULAR (|.|=sqrt p / something).  A flat spectrum = white noise = NOT low-degree.
    Hypercontractivity (degree-d -> (q-1)^{d/2} 2-to-2r norm) needs LOW degree. We MEASURE the
    spectral concentration of (eta_i): fraction of L2 mass in top-K frequencies. Flat => hyperc dead.

We also test the DUAL: the deepest provable cumulant via the EXACT Newton/cumulant recursion using
ONLY the proven low moments mu_2=1, mu_4=3-3/n (kurtosis), mu_6 (E_3 in-tree).  Markov-Krein says
that's frozen; but the cumulant SIGN structure (c_4<0, alternating) is a stronger constraint than
Markov-Krein uses (which only uses mu_2,mu_4 magnitudes). Test if c_4<0 (sub-Gaussian) + boundedness
gives a Bennett/Bernstein tail beating Markov-Krein.
"""
import cmath, math
import numpy as np

def is_prime(m):
    if m<2: return False
    for q in (2,3,5,7,11,13,17,19,23,29,31,37):
        if m%q==0: return m==q
    d=m-1;r=0
    while d%2==0:d//=2;r+=1
    for a in (2,3,5,7,11,13,17,19,23,29,31,37):
        x=pow(a,d,m)
        if x in (1,m-1):continue
        for _ in range(r-1):
            x=x*x%m
            if x==m-1:break
        else:return False
    return True

def factorize(m):
    s=set();d=2
    while d*d<=m:
        while m%d==0:s.add(d);m//=d
        d+=1
    if m>1:s.add(m)
    return s

def order_n_gen(p,n):
    F=factorize(p-1)
    for h in range(2,p):
        if all(pow(h,(p-1)//q,p)!=1 for q in F): return pow(h,(p-1)//n,p)
    return None

def gen_Fp_star(p):
    F=factorize(p-1)
    for h in range(2,p):
        if all(pow(h,(p-1)//q,p)!=1 for q in F): return h
    return None

def find_prime(n, beta):
    lo=int(n**beta); p=lo+(1-lo)%n
    while p<int(n**(beta+0.6)):
        if is_prime(p): return p
        p+=n
    return None

def eta_of(p, b, mu_list):
    s=0j
    for x in mu_list:
        s+=cmath.exp(2j*cmath.pi*(b*x%p)/p)
    return s.real

print("="*100)
print("ROUTE (C) TOWER MARTINGALE  +  ROUTE (B) HYPERCONTRACTIVITY  spectral concentration")
print("="*100)

for n in (16,32,64):
    p=find_prime(n,4.0)
    g0=gen_Fp_star(p)         # generator of F_p*
    # mu_n = <g0^m>, m=(p-1)/n
    m=(p-1)//n
    gen_mu_n = pow(g0, m, p)
    mu_n=[pow(gen_mu_n,i,p) for i in range(n)]
    # mu_{2n} = <g0^{m/2}> needs 2n | p-1.  p=1 mod n; need 2n|p-1 for tower step.
    has2n = ((p-1) % (2*n)==0)
    print(f"\n--- n={n} p={p} m={m} (2n|p-1: {has2n}) ---")

    # ROUTE C: eta^{(2n)} = eta^{(n)}_b + eta^{(n)}_{b w}, w in mu_{2n}\mu_n
    if has2n:
        gen_mu_2n = pow(g0, (p-1)//(2*n), p)
        w = gen_mu_2n      # w^2 = gen_mu_n's ... w has order 2n; w*mu_n is the other coset
        # sample cosets b: reps of F_p*/mu_{2n}? use reps of F_p*/mu_n and look at b, b*w
        Eb=[]; Ebw=[]
        # take a representative set of b (one per mu_n coset) up to a cap for speed
        seen=set(); reps=[]; b=1
        cap=min(m, 6000)
        while len(reps)<cap and b<p:
            if b not in seen:
                reps.append(b)
                for x in mu_n: seen.add(b*x%p)
            b+=1
        for b in reps:
            Eb.append(eta_of(p,b,mu_n))
            Ebw.append(eta_of(p,(b*w)%p,mu_n))
        Eb=np.array(Eb); Ebw=np.array(Ebw)
        corr=np.corrcoef(Eb,Ebw)[0,1]
        # the order-2n period = Eb+Ebw ; its variance vs 2*var(eta_n) (2n if independent)
        E2n=Eb+Ebw
        print(f" ROUTE C: corr(eta_b, eta_bw) = {corr:+.4f}  (independent->0)")
        print(f"   var(eta_n)={np.var(Eb):.3f} (~n={n})  var(eta_2n)={np.var(E2n):.3f} (~2n={2*n} if indep, ~? if not)")
        print(f"   E[eta_2n^4]/(3 var^2) = kappa2(2n) = {np.mean(E2n**4)/(3*np.var(E2n)**2):.4f}")
        print(f"   E[eta_n^4]/(3 var^2)  = kappa2(n)  = {np.mean(Eb**4)/(3*np.var(Eb)**2):.4f}")

    # ROUTE B: spectral concentration of the period sequence on Z/m
    # full period vector (real) indexed by coset rep order; compute |DFT| and concentration
    seen=set(); reps=[]; b=1
    while len(reps)<m and b<p:
        if b not in seen:
            reps.append(b)
            for x in mu_n: seen.add(b*x%p)
        b+=1
    etas=np.array([eta_of(p,b,mu_n) for b in reps])
    # DFT over the cyclic quotient: order reps by discrete log base g0 mod m's structure.
    # quotient F_p*/mu_n is cyclic of order m generated by image of g0. coset index of b = dlog_g0(b) mod m
    # build dlog of generator images: g0^j for j=0..m-1 are coset reps (distinct mod mu_n)
    cosrep_eta=np.zeros(m)
    cur=1
    for j in range(m):
        cosrep_eta[j]=eta_of(p,cur,mu_n)
        cur=(cur*g0)%p
    F=np.fft.fft(cosrep_eta)
    power=np.abs(F)**2
    power_sorted=np.sort(power)[::-1]
    tot=power.sum()
    for frac_k in (0.001,0.01,0.05):
        K=max(1,int(frac_k*m))
        print(f" ROUTE B: top {frac_k*100:.1f}% freqs hold {power_sorted[:K].sum()/tot*100:5.1f}% of L2 power", end="")
    print()
    print(f"   |DFT| stats: min={np.sqrt(power.min()):.2f} mean={np.sqrt(power.mean()):.2f} max={np.sqrt(power.max()):.2f}  (flat=white=hyperc DEAD)")
