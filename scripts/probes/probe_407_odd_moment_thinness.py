#!/usr/bin/env python3
"""
#407 -- ODD-MOMENT thinness discriminator for the deep-Sidon / W_r object.

Found in probe_407_deep_sidon_depth: even-r EXCESS_r = 1 + (1/n^r) sum_{b!=0} eta_b^r
is dominated by the FORCED antipodal zero-sums (scales like p/n) -> thickness-leaky junk.
But the ODD-r values looked DIFFERENT thick vs thin (n=16: thin r5,7,9 ~ 5; thick ~ 1).

This isolates the ODD moments and asks honestly whether
    A_r := sum_{b != 0} eta_b^r        (r ODD, so SIGN-sensitive: no |.|)
carries a THINNESS-ESSENTIAL signal -- i.e. is genuinely different in the THIN (beta>=4)
vs THICK (beta~2.3-3.2, where CORE is FALSE) windows, BEYOND a trivial p/n rescale.

We normalize three honest ways and compare across MANY primes per (n,beta) to kill prime-
specific noise. eta_b are REAL (mu_n closed under negation), so eta_b^r is real; A_r real.

NORMALIZATIONS (each a candidate "is it thinness-essential" lens):
  (a) A_r / p                  (DC-free count density; random model ~ O(sqrt) fluctuation)
  (b) A_r / (p * M^r)          M = max|eta_b|; if |A_r| ~ p*M^r the bound sum<=p*M^r is TIGHT (bad);
                               if A_r/(p*M^r) -> 0 there is genuine signed cancellation (the prize)
  (c) A_r / ((p-1) * mean|eta|^r)   relative to the typical-term scale

A thinness signature for the PRIZE (rule-3): (b) should be SMALL & shrinking in THIN and
LARGER / non-shrinking in THICK -- i.e. signed cancellation in sum eta_b^r is a thin-only
phenomenon. If (b) is the SAME thick vs thin, the odd-moment object is thickness-invariant
(rule-3-incompatible, a mapped wall = still a WIN).
"""
import cmath, math, itertools

def is_prime(n):
    if n<2: return False
    if n%2==0: return n==2
    d=3
    while d*d<=n:
        if n%d==0: return False
        d+=2
    return True

def factor(x):
    f=set(); d=2
    while d*d<=x:
        while x%d==0: f.add(d); x//=d
        d+=1
    if x>1: f.add(x)
    return f

def primitive_root(p):
    fac=factor(p-1)
    for g in range(2,p):
        if all(pow(g,(p-1)//q,p)!=1 for q in fac): return g
    return None

def find_primes(target, n, count, prefer_odd_m=True):
    """primes p == 1 mod n near target=n^beta; prefer m=(p-1)/n ODD (low 2-adic, avoid Fermat)."""
    out=[]
    k0=max(1,round(target/n))
    for delta in range(0,2000000):
        for s in (1,-1):
            kk=k0+s*delta
            if kk<1: continue
            p=kk*n+1
            if p>3 and is_prime(p):
                m=(p-1)//n
                if prefer_odd_m and m%2==0: continue
                if p not in out: out.append(p)
            if len(out)>=count: return out
    return out

def subgroup(n,p):
    g=primitive_root(p); h=pow(g,(p-1)//n,p)
    e=[]; x=1
    for _ in range(n): e.append(x); x=(x*h)%p
    return e

def periods(elts,p):
    w=2*math.pi/p
    out=[]
    for b in range(p):
        s=0.0  # eta_b is REAL; accumulate real part only (imag ~ 1e-15)
        im=0.0
        for xx in elts:
            ang=w*((b*xx)%p)
            s+=math.cos(ang); im+=math.sin(ang)
        out.append((s,im))
    return out

def run():
    print("ODD-MOMENT thinness test:  A_r = sum_{b!=0} eta_b^r  (r ODD, signed).")
    print("Per (n,beta): median over several odd-m primes. M=max|eta_b|.")
    print("Lens (b) A_r/(p*M^r): ->0 = signed cancellation (prize); O(1)/flat = bound tight.\n")
    for n in [8,16]:
        log2n=int(math.log2(n))
        odd_rs=[r for r in range(3, 2*log2n+2, 2)]
        print(f"==== n={n}  (log2 n={log2n})  odd r in {odd_rs} ====")
        betas = [2.4, 2.8, 3.2, 4.0, 4.5] if n==8 else [2.4, 2.8, 3.2, 4.0]
        for beta in betas:
            ps=find_primes(int(n**beta), n, 4)
            if not ps: 
                print(f"  beta={beta}: no primes"); continue
            # aggregate medians across primes
            agg={r:[] for r in odd_rs}
            aggM=[]
            realbeta=[]
            for p in ps:
                e=subgroup(n,p)
                per=periods(e,p)
                maxim=max(abs(im) for _,im in per)
                # M over b!=0
                M=max(math.hypot(re,im) for b,(re,im) in enumerate(per) if b!=0)
                aggM.append(M)
                realbeta.append(math.log(p)/math.log(n))
                for r in odd_rs:
                    # eta_b^r real part: (re+i im)^r ; eta real so im~0 -> re^r. use complex for safety
                    Ar=0.0
                    for b in range(1,p):
                        re,im=per[b]
                        z=complex(re,im)**r
                        Ar+=z.real
                    agg[r].append(Ar/(p*(M**r)))
            import statistics as st
            rb=st.median(realbeta); Mm=st.median(aggM)
            cells=" ".join(f"r{r}:{st.median(agg[r]):+.4f}" for r in odd_rs)
            print(f"  beta~{rb:.2f} ({len(ps)}p, M~{Mm:.2f}): {cells}")
        print()

if __name__=="__main__":
    run()
