#!/usr/bin/env python3
"""
Door-(iv) probe: multi-piece coherence for negation-stable coset refinements.

For H=<h> of order n in F_p^*, split H into d cosets of <h^d>, d=4 or 8.  In the prize
2-power regime with d | n/2, every piece is negation-stable, so its period sum is real.  The
multi-piece coherence rho_d(b)=|sum_j A_j|/sum_j |A_j| therefore saturates at 1 whenever all
piece sums have one sign.  This probe measures how often that simple saturation occurs and whether
the worst |eta_b| coset is explained by all-same-sign refinements.
"""
from __future__ import annotations
import argparse, cmath, math, random


def is_prime(n:int)->bool:
    if n < 2: return False
    small=[2,3,5,7,11,13,17,19,23,29,31,37]
    for q in small:
        if n == q: return True
        if n % q == 0: return False
    d=41
    while d*d <= n:
        if n%d==0: return False
        d += 2
    return True

def factor(n:int)->list[int]:
    out=[]; d=2
    while d*d <= n:
        if n%d==0:
            out.append(d)
            while n%d==0: n//=d
        d += 1 if d==2 else 2
    if n>1: out.append(n)
    return out

def primitive_root(p:int)->int:
    fs=factor(p-1)
    for g in range(2,p):
        if all(pow(g,(p-1)//q,p)!=1 for q in fs): return g
    raise RuntimeError('no primitive root')

def next_prime_1_mod_n_near(n:int,beta:int=4)->int:
    k=max(1,(n**beta-1+n-1)//n)
    for r in range(2_000_000):
        for kk in ((k+r) if r else k, k-r):
            if kk>0 and is_prime(kk*n+1): return kk*n+1
    raise RuntimeError('no prime')

def sample_js(total:int, limit:int|None, seed:int):
    if limit is None or limit>=total: return list(range(total))
    rng=random.Random(seed+total)
    s=set(range(min(total,2048))) | {total-1-i for i in range(min(total,2048))}
    while len(s)<limit: s.add(rng.randrange(total))
    return sorted(s)

def scan(n:int,d:int,limit:int|None,seed:int):
    p=65537 if n==16 else next_prime_1_mod_n_near(n,4)
    g=primitive_root(p); m=(p-1)//n; h=pow(g,m,p); hd=pow(h,d,p)
    pieces=[]
    for j in range(d):
        xs=[]; x=pow(h,j,p)
        for _ in range(n//d):
            xs.append(x); x=(x*hd)%p
        pieces.append(xs)
    js=sample_js(m,limit,seed+n+d)
    twopi=2*math.pi
    allsame=0; best_eta=None; best_rho=None
    top=[]
    for j in js:
        b=pow(g,j,p)
        sums=[]
        for P in pieces:
            z=0j
            for x in P:
                z += cmath.exp(1j*twopi*((b*x)%p)/p)
            sums.append(z)
        eta=abs(sum(sums)); den=sum(abs(z) for z in sums); rho=eta/den if den else 0.0
        signs=[1 if z.real>=0 else -1 for z in sums]
        same=(all(s==1 for s in signs) or all(s==-1 for s in signs))
        allsame += int(same)
        row=(eta,rho,j,b,same,[z.real for z in sums])
        if best_eta is None or eta>best_eta[0]: best_eta=row
        if best_rho is None or (rho,eta)>(best_rho[1],best_rho[0]): best_rho=row
        top.append(row); top=sorted(top,reverse=True)[:5]
    return p,m,len(js),allsame,best_eta,best_rho,top

def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--ns',default='16,32,64,128')
    ap.add_argument('--ds',default='4,8')
    ap.add_argument('--limit-large',type=int,default=120000)
    ap.add_argument('--seed',type=int,default=444)
    args=ap.parse_args()
    print('Door-IV multi-piece sign-coherence probe: rho_d=|sum pieces|/sum |pieces| for d-coset refinements.')
    print('Verdict target: all-same-sign real pieces force rho_d=1; this tests how often that degeneracy appears.\n')
    for n in [int(x) for x in args.ns.split(',') if x]:
        for d in [int(x) for x in args.ds.split(',') if x]:
            if d>=n or n%d: continue
            limit=None if n<=64 else args.limit_large
            p,m,scanned,allsame,beta,best,top=scan(n,d,limit,args.seed)
            print(f'## n={n} d={d} p={p} beta={math.log(p)/math.log(n):.3f} quotient_cosets={m} scanned={scanned}')
            print(f'all-same-sign pieces: {allsame}/{scanned} ({allsame/scanned:.3%})')
            eta,rho,j,b,same,reals=beta
            print(f'best |eta|: j={j} b={b} |eta|={eta:.6f} rho_d={rho:.6f} allSame={same} reals={[round(x,3) for x in reals]}')
            eta,rho,j,b,same,reals=best
            print(f'best rho:  j={j} b={b} |eta|={eta:.6f} rho_d={rho:.6f} allSame={same}')
            print('top |eta| rows:')
            for eta,rho,j,b,same,reals in top:
                print(f'  j={j:<8d} |eta|={eta:8.3f} rho_d={rho:.6f} allSame={same}')
            print()
if __name__=='__main__': main()
