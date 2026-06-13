#!/usr/bin/env python3
"""
δ* window list-size probe (#389, 2026-06-13).

Tests the Mérai-Shparlinski sparsity route prediction: the worst-case list size of a
smooth RS code RS[F_p, H, k] (H = multiplicative subgroup of 2-power order n) at radius δ
in the window (1-√ρ, 1-ρ) stays ≤ ~n^{3/2} (the MS incidence exponent for the
subgroup×low-degree-graph coupling curve), as long as the relevant curve is irreducible.

For each candidate worst word w (deep-hole / structured words), and each band a (= required
agreement = (1-δ)n) in the window, we compute the EXACT list:
    L(w,a) = #{ degree-<k codewords c : #{x∈H : c(x)=w(x)} ≥ a }
by brute force: every list codeword is the Lagrange interpolant of some k-subset of its
agreement set, so enumerate all k-subsets, interpolate, keep those with agreement ≥ a, dedupe.

Reports, in the window, max-over-words L vs the thresholds n, n^{3/2}, n^2.
If L >> n^{3/2}: the MS route is refuted (curve reducible, list explodes).
If L <= ~n^{3/2}: MS route live for large fields (q >~ n^{3/2}·2^128).
"""
import itertools, math, sys
from collections import defaultdict

def is_prime(m):
    if m < 2: return False
    for i in range(2,int(m**0.5)+1):
        if m%i==0: return False
    return True

def find_prime(n, lo):
    p = max(lo, n+1)
    while True:
        if (p-1)%n==0 and is_prime(p): return p
        p += 1

def subgroup(p,n):
    for g0 in range(2,p):
        vals=set(); xx=1
        for _ in range(p-1):
            xx=(xx*g0)%p; vals.add(xx)
        if len(vals)==p-1:
            g=pow(g0,(p-1)//n,p)
            return [pow(g,i,p) for i in range(n)]
    raise RuntimeError

def interp_poly(p,pts):
    # return tuple of evaluations on all-of-H is done by caller; here return coeff signature
    # we just return the evaluation function via barycentric; represent poly by its values on H
    pass

def list_at(p,H,w,k,a_min):
    """Return dict: frozenset(codeword evals on H) -> agreement, for codewords with agreement>=a_min."""
    n=len(H)
    found={}
    for sub in itertools.combinations(range(n),k):
        xs=[H[i] for i in sub]; ys=[w[i] for i in sub]
        if len(set(xs))!=k: continue
        # evaluate interpolant on all H
        ev=[]
        ok=True
        for j in range(n):
            X=H[j]; fx=0
            for i in range(k):
                num=ys[i]%p; den=1
                for l in range(k):
                    if l==i: continue
                    num=(num*((X-xs[l])%p))%p
                    den=(den*((xs[i]-xs[l])%p))%p
                fx=(fx+num*pow(den,p-2,p))%p
            ev.append(fx)
        agree=sum(1 for j in range(n) if ev[j]==w[j])
        if agree>=a_min:
            found[tuple(ev)]=agree
    return found

def run(n,k,max_p=200):
    p=find_prime(n,2*n)
    if p>max_p: return None
    H=subgroup(p,n)
    rho=k/n
    johnson=1-math.sqrt(rho); cap=1-rho
    # window bands a: agreement in (cap-agree, johnson-agree) = ((1-cap)n,(1-johnson)n)=(rho n, sqrt(rho) n)
    a_lo=math.floor(rho*n)+1          # just above capacity-agreement (k)
    a_hi=math.ceil(math.sqrt(rho)*n)  # Johnson agreement
    # candidate worst words: power/deep-hole maps and a couple structured combos
    cand={}
    for d in [k, k+1, n-1, n-2]:
        cand[f"x^{d}"]=[pow(x,d,p) for x in H]
    # also a "two-power-split" word: x^k on half, x^{k+1} on half via x^k + x^{n-1}
    cand["x^k+inv"]=[(pow(x,k,p)+pow(x,n-1,p))%p for x in H]
    rows=[]
    for a in range(max(a_lo,k+1), a_hi+1):
        best=0; bestw=None
        for name,w in cand.items():
            L=len(list_at(p,H,w,k,a))
            if L>best: best=L; bestw=name
        delta=1-a/n
        rows.append((a,round(delta,3),best,bestw))
    return dict(n=n,k=k,p=p,rho=round(rho,3),johnson=round(johnson,3),cap=round(cap,3),
                n32=round(n**1.5,1),rows=rows)

if __name__=="__main__":
    for (n,k) in [(8,2),(8,4),(16,4),(16,8),(16,12)]:
        r=run(n,k)
        if not r:
            print(f"n={n} k={k} skipped"); continue
        print(f"\nn={n} k={k} p={r['p']} ρ={r['rho']} Johnson={r['johnson']} cap={r['cap']} "
              f"| n={n} n^1.5={r['n32']} n^2={n*n}")
        print(f"   window bands (agreement a, δ, maxList, worstWord):")
        for (a,delta,L,wn) in r['rows']:
            flag=""
            if L> n**1.5: flag=" > n^1.5 !!"
            if L> n*n: flag=" > n^2 !!!"
            print(f"     a={a:2d} δ={delta:5.3f}  L={L:4d}  ({wn}){flag}")
        sys.stdout.flush()
