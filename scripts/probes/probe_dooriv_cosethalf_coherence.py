#!/usr/bin/env python3
"""
Door-(iv) probe: worst-frequency coset-half coherence for thin 2-power
subgroups of F_p^*.

For n | p-1, let g be a primitive root, H=<g^m> of order n, m=(p-1)/n.
Split H into the two cosets of its index-2 subgroup:
  H0=<g^(2m)> and H1=g^m H0.
For each multiplicative coset of H, represented by b=g^j, measure
  A_b = sum_{x in H0} exp(2π i b x/p)
  B_b = sum_{x in H1} exp(2π i b x/p)
  eta_b = A_b+B_b
  rho(b)=|eta_b|/(|A_b|+|B_b|).
This is the finite "are the two half-period pieces phase-aligned?" object
from Shaw's door-(iv) essay. It is NOT a proof of CORE; it is a probe for
structure in the adversarial b.

The sweep is exact over all quotient cosets for n<=64 by default and sampled
for n=128,256 unless --full-large is passed.
"""
from __future__ import annotations

import argparse, cmath, math, random
from dataclasses import dataclass
from typing import Iterable


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
        if all(pow(g,(p-1)//q,p)!=1 for q in fs):
            return g
    raise RuntimeError("no primitive root")


def next_prime_1_mod_n_near(n:int, beta:int=4)->int:
    target=n**beta
    k=max(1,(target-1 + n-1)//n)
    # prefer odd p, so k parity chosen if n even then k arbitrary gives p odd
    for radius in range(0, 2_000_000):
        for kk in ((k+radius) if radius else k, k-radius):
            if kk <= 0: continue
            p=kk*n+1
            if is_prime(p): return p
    raise RuntimeError(f"no prime found for n={n}")


def angle(z:complex)->float:
    return math.atan2(z.imag,z.real)

def wrap(a:float)->float:
    while a <= -math.pi: a += 2*math.pi
    while a > math.pi: a -= 2*math.pi
    return a

@dataclass
class Row:
    n:int; p:int; m:int; g:int; j:int; b:int; rho:float; eta:float; denom:float
    aabs:float; babs:float; dtheta:float; q:int; q_center:int; rep_min:int


def scan(n:int, p:int, limit:int|None, seed:int) -> tuple[Row, list[Row], int, int, int]:
    g=primitive_root(p)
    m=(p-1)//n
    h=pow(g,m,p)
    h2=pow(h,2,p)
    H0=[]; x=1
    for _ in range(n//2):
        H0.append(x); x=(x*h2)%p
    H1=[(h*x)%p for x in H0]
    total=m
    if limit is None or limit >= total:
        js=list(range(total))
    else:
        rng=random.Random(seed+n+p)
        # include structured reps: beginning/end, quartiles, powers of two, random fill
        base=set(range(min(total,4096))) | {total-1-i for i in range(min(total,4096))}
        for t in [total//8,total//4,3*total//8,total//2,5*total//8,3*total//4,7*total//8]:
            for d in range(-64,65):
                if 0 <= t+d < total: base.add(t+d)
        x=1
        while x<total:
            for d in range(-8,9):
                if 0 <= x+d < total: base.add(x+d)
            x*=2
        while len(base)<limit:
            base.add(rng.randrange(total))
        js=sorted(base)[:limit]
    twopi=2*math.pi
    best=None; top=[]; aligned=0; anti=0
    b=1
    # If sampling non-consecutive js, direct pow is simpler and reliable.
    for j in js:
        bj=pow(g,j,p)
        A=0j; B=0j
        for x in H0:
            A += cmath.exp(1j*twopi*((bj*x)%p)/p)
        for x in H1:
            B += cmath.exp(1j*twopi*((bj*x)%p)/p)
        eta=abs(A+B); den=abs(A)+abs(B)
        rho=eta/den if den else 0.0
        dth=abs(wrap(angle(A)-angle(B)))
        q=pow(bj,n,p)  # quotient coordinate, invariant under bj*H
        rep_min=min(bj, p-bj)
        q_center=min(q, p-q)
        if (A.real >= 0 and B.real >= 0) or (A.real <= 0 and B.real <= 0):
            aligned += 1
        else:
            anti += 1
        row=Row(n,p,m,g,j,bj,rho,eta,den,abs(A),abs(B),dth,q,q_center,rep_min)
        if best is None or (row.rho,row.eta)>(best.rho,best.eta): best=row
        top.append(row); top=sorted(top,key=lambda r:(r.rho,r.eta),reverse=True)[:12]
    assert best is not None
    return best, top, len(js), aligned, anti


def fmt(r:Row)->str:
    return (f"n={r.n:3d} p={r.p:<11d} m={r.m:<8d} scanned_j best_j={r.j:<8d} "
            f"b={r.b:<11d} rho={r.rho:.6f} |eta|={r.eta:.3f} den={r.denom:.3f} "
            f"|A|={r.aabs:.3f} |B|={r.babs:.3f} dtheta={r.dtheta:.4g} "
            f"q=b^n={r.q} q_center={r.q_center} min(b,p-b)={r.rep_min}")


def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--ns', default='16,32,64,128,256')
    ap.add_argument('--limit-large', type=int, default=250_000)
    ap.add_argument('--full-large', action='store_true')
    ap.add_argument('--seed', type=int, default=444)
    args=ap.parse_args()
    print("Door-(iv) coset-half coherence probe. Split H into H0=<h^2>, H1=hH0; rho=|A+B|/(|A|+|B|).")
    print("IMPORTANT: rho near 1 only means the two half-period sums align for that b; it is not a CORE bound.\n")
    for n in [int(s) for s in args.ns.split(',') if s.strip()]:
        p=65537 if n==16 else next_prime_1_mod_n_near(n,4)
        m=(p-1)//n
        limit=None if (args.full_large or n<=64) else args.limit_large
        best, top, scanned, aligned, anti=scan(n,p,limit,args.seed)
        print(f"## n={n} p={p} beta={math.log(p)/math.log(n):.3f} quotient_cosets={m} scanned={scanned}")
        print(f"same-sign half sums: {aligned}/{scanned} ({aligned/scanned:.3%}); opposite-sign: {anti}/{scanned}")
        print(fmt(best))
        print("top-5:")
        for r in top[:5]:
            print("  "+fmt(r))
        # simple anti-concentration diagnostics on top set
        small_b=sum(1 for r in top if r.rep_min <= 1024)
        near_pm1=sum(1 for r in top if r.q_center <= 1024)
        print(f"top12 diagnostics: small additive reps <=1024: {small_b}/12; quotient q near ±1 <=1024: {near_pm1}/12")
        print()

if __name__ == '__main__':
    main()
