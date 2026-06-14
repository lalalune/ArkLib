#!/usr/bin/env python3
"""
#407 cumulant-deep-nonbetti  --  ROUTE (C) tower martingale, DEEP structural test.

Established: eta^{(2n)}_b = eta^{(n)}_b + eta^{(n)}_{bw},  corr=0,  var adds.
For a martingale/Azuma sub-Gaussian bound we need MORE than 2nd-order decorrelation.

We test the EXACT algebraic claim and the higher-order martingale structure:

1. IS corr=0 an IDENTITY?  E_b[eta^{(n)}_b * eta^{(n)}_{bw}]  where b ranges over a FULL
   transversal of F_p*/mu_{2n} (so (b, bw) ranges over pairs in the two mu_n-cosets inside one
   mu_{2n}-coset). Compute the exact sum sum_b eta_b eta_{bw}. If it's exactly 0 (or -something
   tiny) it's an identity = Parseval orthogonality of distinct Gauss periods.

2. MIXED 4th moments:  for the martingale to give sub-Gaussian we want the cross terms in
   E[(A+B)^{2r}] to be SMALL relative to the diagonal (2r-1)!! n^r.  Measure
   E[A^2 B^2]/(E[A^2]E[B^2])  (=1 if independent in 2nd order),
   E[A^3 B]/..., E[A^4]/E[A^2]^2, and the full E[(A+B)^4] vs 2*E[A^4]+6 E[A^2]E[B^2].

3. The CRUX for a clean martingale bound: is the conditional distribution of B given A's coset
   sub-Gaussian with variance ~n UNIFORMLY?  i.e. is max_b |eta^{(n)}_{bw}| (the increment) bounded
   conditional on b?  No -- B itself is a full order-n period, its own max is ~sqrt(n log m).
   So the tower is NOT a bounded-increment martingale; each increment can be as big as the whole.
   THIS is the obstruction: telescoping doesn't shrink the increment.  We QUANTIFY:
   distribution of the per-level increment |eta_{level k+1} - eta_{level k}| vs sqrt(level).

4. NESTED tower from the bottom: mu_2={1,-1} -> eta=2cos.  Build the full a-level telescope for a
   single worst-case b and watch the partial sums S_k = eta^{(2^k)}_b.  Is (S_k) a martingale-like
   walk with increment variance ~2^k (so S_a ~ sqrt(sum 2^k)=sqrt(2^a)=sqrt n) -- the RIGHT scale?
   Or do increments correlate to build the max coherently?
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

def gen_Fp_star(p):
    F=factorize(p-1)
    for h in range(2,p):
        if all(pow(h,(p-1)//q,p)!=1 for q in F): return h
    return None

def find_prime_tower(a, beta):
    """prime p with 2^a | p-1 (full tower available) and p ~ n^beta, n=2^a."""
    n=2**a
    lo=int(n**beta);
    # need 2^a | p-1; step by 2^a, but also want generator tower; use modulus 2^a
    step=2**a
    p = lo - (lo % step) + 1
    if p<=lo: p+=step
    while p<int(n**(beta+1.0)):
        if is_prime(p): return p
        p+=step
    return None

def eta_of(p, b, mu_list):
    s=0j
    for x in mu_list:
        s+=cmath.exp(2j*cmath.pi*(b*x%p)/p)
    return s.real

print("="*100)
print("ROUTE (C) TOWER MARTINGALE -- deep structural test")
print("="*100)

for a in (4,5,6):
    n=2**a
    p=find_prime_tower(a,4.0)
    if p is None:
        print(f"\nn={n}: no full-tower prime found"); continue
    g0=gen_Fp_star(p)
    m=(p-1)//n
    print(f"\n--- n={n}=2^{a} p={p} m={m} (2^{a}|p-1 full tower) ---")
    # mu_{2^k} = <g0^{(p-1)/2^k}> for k=1..a
    def mu(k):
        gen=pow(g0,(p-1)//(2**k),p)
        return [pow(gen,i,p) for i in range(2**k)]
    mun=mu(a)
    w=pow(g0,(p-1)//(2*n),p)   # order 2n, mu_{2n}=mu_n cup w mu_n

    # (1) exact orthogonality: sum over full transversal of F_p*/mu_{2n}
    # reps of F_p*/mu_{2n}: g0^j, j=0..(p-1)/(2n)-1
    mtop=(p-1)//(2*n)
    cur=1; prod=0.0; sA2=0.0; sB2=0.0; sA4=0.0; sA2B2=0.0; sA3B=0.0; sAB3=0.0
    Avals=[]; Bvals=[]
    for j in range(mtop):
        A=eta_of(p,cur,mun)
        B=eta_of(p,(cur*w)%p,mun)
        prod+=A*B; sA2+=A*A; sB2+=B*B; sA4+=A**4; sA2B2+=A*A*B*B; sA3B+=A**3*B; sAB3+=A*B**3
        Avals.append(A); Bvals.append(B)
        cur=(cur*g0)%p
    Av=np.array(Avals); Bv=np.array(Bvals)
    print(f" (1) <A,B> over F*/mu_2n  = {prod:.4e}   (Parseval-orthogonal => ~0; here /N = {prod/mtop:.4e})")
    print(f"     E[A^2]={sA2/mtop:.3f} E[B^2]={sB2/mtop:.3f}  (both ~ n={n})")
    print(f" (2) mixed: E[A^2 B^2]/(E A^2 E B^2) = {(sA2B2/mtop)/((sA2/mtop)*(sB2/mtop)):.4f}  (indep=1)")
    print(f"     E[A^3 B]={sA3B/mtop:.3e}  E[A B^3]={sAB3/mtop:.3e}  (indep&meanzero => 0)")
    EApB4=np.mean((Av+Bv)**4); diag=2*(sA4/mtop)+6*(sA2/mtop)*(sB2/mtop)
    print(f"     E[(A+B)^4]={EApB4:.1f}  vs  2E[A^4]+6E[A^2]E[B^2]={diag:.1f}  ratio={EApB4/diag:.4f}")

    # (3)(4) per-level increment scale for the WORST-CASE b (max top period)
    # find worst b
    seen=set(); reps=[]; b=1
    cap=min(m,8000)
    while len(reps)<cap and b<p:
        if b not in seen:
            reps.append(b)
            for x in mun: seen.add(b*x%p)
        b+=1
    eat=[(eta_of(p,b,mun),b) for b in reps]
    Mval,bworst=max(eat,key=lambda t:abs(t[0]))
    print(f" (3/4) worst b={bworst}: top period eta={Mval:.3f}  (sqrt(2n ln m)={math.sqrt(2*n*math.log(m)):.3f})")
    # telescope partial sums for bworst:  S_k = eta^{(2^k)}_{bworst}
    Ss=[]
    for k in range(1,a+1):
        Ss.append(eta_of(p,bworst,mu(k)))
    incs=[Ss[0]]+[Ss[k]-Ss[k-1] for k in range(1,len(Ss))]
    print("     level k:  S_k=eta^(2^k)        increment        sqrt(2^k)")
    for k in range(len(Ss)):
        print(f"       {k+1:2d}     {Ss[k]:10.3f}        {incs[k]:10.3f}      {math.sqrt(2**(k+1)):8.3f}")
    # do the increments add coherently (same sign building the max) or random-walk?
    signs=[1 if x>0 else -1 for x in incs]
    print(f"     increment signs: {signs}  (all-same => coherent build; mixed => cancelling walk)")
    print(f"     sum|inc| = {sum(abs(x) for x in incs):.2f}   |S_a| = {abs(Ss[-1]):.2f}   ratio={abs(Ss[-1])/sum(abs(x) for x in incs):.3f}")
