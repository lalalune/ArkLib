#!/usr/bin/env python3
"""
wf407 / T232-03-bgk : p-DEPENDENCE and large-prime behaviour of the BGK magnitude.

Q: the big M values sit at TINY primes (17,97,193,257). Prize regime is p ~ n*2^128 (HUGE).
   Does M -> 0 as p grows?  What primes p give M>0, and how big can M be at a fixed n?

Also: dissect the E_2 (additive energy) anomaly.  Standard identity for a set G with -G=G:
   E_2(G) = #{(a,b,c,d) in G^4 : a+b=c+d}.
   Diagonal-type solutions: a+b=c+d always has the 'trivial' families
       (a,b,c,d)=(a,b,a,b), (a,b,b,a)  -> 2|G|^2 - (a=b) overcount = 2n^2 - n.
   Plus a+b=c+d with {a,b}!={c,d}: these are the genuine additive quadruples = 'extra'.
   The 3-fold zero-sum (BGK) is a DIFFERENT moment: #{(x,y,z):x+y+z=0}=n*M. They are related
   but not identical. We separate them cleanly here.

We also test the SHARP question: max over ALL primes (any size) at fixed n of M -- is it bounded
by an n-only quantity?  Connect to KSV / Mersenne wall: M_odd happens exactly at p|2^n-1.
"""
from sympy import primerange
from collections import Counter, defaultdict

def primroot(p):
    order=p-1
    qs=[]; mm=order; d=2
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
    return sum(1 for u in G if (1+u)%p in G), G

def E2(G,p):
    r=Counter()
    Gl=list(G)
    for a in Gl:
        for b in Gl:
            r[(a+b)%p]+=1
    return sum(v*v for v in r.values())

def main():
    print("="*94)
    print("(A) Which primes p give M>0, and how does M depend on p (n fixed)?")
    print("="*94)
    for n in [8,16,32,64]:
        cap = 3_000_000 if n<=16 else (2_000_000 if n==32 else 1_500_000)
        pos=[]  # (p, M)
        for p in primerange(3,cap):
            if (p-1)%n: continue
            M,_=bgk_M(n,p)
            if M>0: pos.append((p,M))
        maxM=max((M for _,M in pos), default=0)
        # which p? are they all small? compute p / n (mu_n density = n/(p-1))
        print(f"\nn={n}: cap={cap}, #primes with M>0 = {len(pos)}, maxM={maxM} (maxM/sqrt(n)={maxM/n**0.5:.3f})")
        print("   (p, M, n/(p-1)=density of mu_n):")
        for p,M in sorted(pos, key=lambda t:-t[1])[:14]:
            print(f"      p={p:>9}  M={M:>3}  density={n/(p-1):.2e}  p|2^n-1? {pow(2,n,p)==1}")
        if pos:
            big_p = [p for p,M in pos if p>10000]
            print(f"   #primes>10^4 with M>0: {len(big_p)}; their M values: "
                  f"{sorted(set(M for p,M in pos if p>10000))}")
    print("\n"+"="*94)
    print("(B) E_2 decomposition: E_2 = trivial(2n^2-n) + extra; relation of 'extra' to M")
    print("="*94)
    for n in [8,16,32]:
        cap = 60000
        print(f"\nn={n}: trivial 2n^2-n = {2*n*n-n}; 3n^2-3n = {3*n*n-3*n}")
        rows=[]
        for p in primerange(3,cap):
            if (p-1)%n: continue
            M,G=bgk_M(n,p)
            e=E2(G,p)
            extra=e-(2*n*n-n)
            rows.append((p,M,e,extra))
        # group extra by M
        byM=defaultdict(set)
        for p,M,e,extra in rows: byM[M].add(extra)
        for k in sorted(byM):
            print(f"   M={k:3d}: E_2-(2n^2-n) in {sorted(byM[k])[:8]}")
        # check char-0 prediction: extra should be n^2-3n (=3n^2-3n - (2n^2-n)+? ) when M=0
        print(f"     char-0 'extra' (n^2-... ) candidates: n^2-3n={n*n-3*n}, n^2-n={n*n-n}, "
              f"2n={2*n}")

    print("\n"+"="*94)
    print("(C) SHARP magnitude question: is max_p M(n,p) bounded by a clean n-function?")
    print("="*94)
    print("   collecting global max over ALL enumerated primes per n (incl. structured primes):")
    for n in [8,16,32,64,128]:
        cap = 5_000_000 if n<=64 else 5_000_000
        gM=0; gp=None
        cnt=0
        for p in primerange(3,cap):
            if (p-1)%n: continue
            cnt+=1
            M,_=bgk_M(n,p)
            if M>gM: gM=M; gp=p
        print(f"   n={n:>4}: max M={gM:>3} at p={gp}  (#primes={cnt}); "
              f"M/sqrt(n)={gM/n**0.5:.3f}, M/n^(2/3)={gM/n**(2/3):.3f}, M/log2(n)={gM/(n.bit_length()-1):.3f}")

if __name__=="__main__":
    main()
