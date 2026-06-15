#!/usr/bin/env python3
"""
wf407 / T232-03-bgk : LARGE-prime behaviour + frequency scaling of M>0.

The big-M cases are small-prime/high-density degeneracies (mu_16=F_17* etc.). The PRIZE regime is
p ~ n*2^128, density n/(p-1) -> 0. We need the behaviour there.

We cannot enumerate primes near 2^128, but we CAN:
  (1) sweep n fixed over a LONG window of primes (n|p-1) and record: how OFTEN is M>0, what values,
      does the max settle, does frequency ~ c/p (probabilistic-heuristic) ?
  (2) test the probabilistic-heuristic prediction:  Pr[M>0] ~ E[M] = n * Pr[(1+u) in mu_n]
      = n * (n/(p-1))  (each of n elements 1+u lands in mu_n with prob ~ n/p)  -> E[M] ~ n^2/p.
      So expected number of primes in [P,2P] (n|p-1, ~ P/(n ln P) of them) with M>0 is
          ~ (P/(n ln P)) * (n^2/P) = n/ln P  -> i.e. roughly constant-in-P count, M tiny.
  (3) directly evaluate M at a handful of LARGE primes p ~ n*2^k (k up to ~40, fits in Python int)
      with n|p-1, to confirm M stays 0 / tiny at genuinely large density-gap.
"""
from sympy import primerange, isprime, nextprime
from collections import defaultdict, Counter

def primroot(p):
    order=p-1; qs=[]; mm=order; d=2
    while d*d<=mm:
        if mm%d==0:
            qs.append(d)
            while mm%d==0: mm//=d
        d+=1
    if mm>1: qs.append(mm)
    g=2
    while any(pow(g,order//q,p)==1 for q in qs): g+=1
    return g

def mu_n(n,p):
    g=primroot(p); h=pow(g,(p-1)//n,p)
    s=set(); cur=1
    for _ in range(n):
        s.add(cur); cur=cur*h%p
    return s

def bgk_M(n,p):
    G=mu_n(n,p)
    return sum(1 for u in G if (1+u)%p in G)

def main():
    print("="*94)
    print("(1) Frequency of M>0 in successive prime windows (n fixed). Expect E[M]~n^2/p -> decays.")
    print("="*94)
    for n in [16,32,64,128]:
        windows=[(1_000,10_000),(10_000,100_000),(100_000,1_000_000),(1_000_000,3_000_000)]
        print(f"\nn={n}:")
        for lo,hi in windows:
            cnt=0; posM=Counter(); total_M=0
            for p in primerange(lo,hi):
                if (p-1)%n: continue
                cnt+=1
                M=bgk_M(n,p)
                if M>0: posM[M]+=1
                total_M+=M
            nprimes=cnt
            frac = sum(posM.values())/nprimes if nprimes else 0
            meanM = total_M/nprimes if nprimes else 0
            # heuristic E[M] ~ n^2 / p_mid
            pmid=(lo+hi)//2
            print(f"   p in [{lo:>9},{hi:>9}): {nprimes:>5} primes, "
                  f"#M>0={sum(posM.values()):>3} (frac={frac:.2e}), meanM={meanM:.3e}, "
                  f"heur n^2/pmid={n*n/pmid:.2e}, M-values={dict(posM)}")

    print("\n"+"="*94)
    print("(2) DIRECT M at genuinely LARGE primes p ~ n*2^k (density n/(p-1) ~ 2^-k -> 0).")
    print("="*94)
    for n in [16,32,64,128,256]:
        print(f"\nn={n}:")
        for k in [20,30,40,60,80,100,128]:
            # find prime p = n*2^k * t + 1 ... we need n | p-1, i.e. p = 1 + n*m. Search near n*2^k.
            base = n*(1<<k)
            # we want p prime with (p-1)%n==0 and p ~ base. take m near 2^k, p=1+n*m.
            m = (base)//n  # = 2^k
            found=None
            for dm in range(0, 200000):
                for mm in (m+dm, m-dm):
                    if mm<=0: continue
                    p=1+n*mm
                    if isprime(p):
                        found=p; break
                if found: break
            if not found:
                print(f"   k={k}: no prime found"); continue
            M=bgk_M(n,found)
            dens = n/(found-1)
            print(f"   k={k:>3}: p={found}  (~n*2^{k}, density={dens:.3e})  M={M}")

if __name__=="__main__":
    main()
