#!/usr/bin/env python3
r"""
Probe the off-diagonal real-part inversion pairing for thin dyadic subgroups.

Checks, for proper subgroups mu_n < F_p^* with p >> n^3 and p == 1 mod n:
  sum_{z in mu\{1,-1}} Re eta_b(z-1)
    == sum_{z in mu\{1,-1}} Re eta_b(z^{-1}-1)
  2*sum == sum_z (term(z)+term(z^{-1}))
at the worst frequency b.

A random same-size thin set control is included: the analogous inversion-pair identity is not a
set-theoretic tautology for an unstructured thin set.
"""
from __future__ import annotations
import cmath, math, random

CASES = [
    (8, 40961),
    (16, 65537),
    (32, 786433),
    (64, 1048897),
]


def factor(n: int):
    fs=[]; d=2
    while d*d<=n:
        if n%d==0:
            fs.append(d)
            while n%d==0: n//=d
        d+=1
    if n>1: fs.append(n)
    return fs


def primitive_root(p: int) -> int:
    fs=factor(p-1)
    for g in range(2,p):
        if all(pow(g,(p-1)//q,p)!=1 for q in fs): return g
    raise RuntimeError(p)


def eta(S, p, b):
    return sum(cmath.exp(2j*math.pi*((b*x)%p)/p) for x in S)


def check_subgroup(n,p):
    g=primitive_root(p)
    h=pow(g,(p-1)//n,p)
    mu=[]; x=1
    for _ in range(n):
        mu.append(x); x=(x*h)%p
    mu=set(mu)
    assert len(mu)==n and 1 in mu and (p-1) in mu and n < p-1
    vals=[(abs(eta(mu,p,b)),b) for b in range(1,p)]
    _,b=max(vals)
    off=[z for z in mu if z != 1 and z != p-1]
    lhs=sum(eta(mu,p,(b*(z-1))%p).real for z in off)
    rhs=sum(eta(mu,p,(b*(pow(z,p-2,p)-1))%p).real for z in off)
    paired=sum((eta(mu,p,(b*(z-1))%p).real + eta(mu,p,(b*(pow(z,p-2,p)-1))%p).real) for z in off)
    return b, abs(lhs-rhs), abs(2*lhs-paired)


def check_random_control(n,p,seed=444):
    rng=random.Random(seed+n+p)
    S=set(rng.sample(range(1,p), n))
    S.add(1)
    while len(S)>n: S.pop()
    if p-1 not in S:
        S.add(p-1)
        while len(S)>n:
            y=next(iter(S-{1,p-1}))
            S.remove(y)
    vals=[(abs(eta(S,p,b)),b) for b in range(1,min(p,2000))]
    _,b=max(vals)
    off=[z for z in S if z != 1 and z != p-1]
    lhs=sum(eta(S,p,(b*(z-1))%p).real for z in off)
    rhs=sum(eta(S,p,(b*(pow(z,p-2,p)-1))%p).real for z in off)
    return b, abs(lhs-rhs)


def main():
    max_inv=max_pair=0.0
    print("n p worst_b subgroup_inv_err subgroup_pair_err random_control_err")
    for n,p in CASES:
        b,e1,e2=check_subgroup(n,p)
        rb,re=check_random_control(n,p)
        max_inv=max(max_inv,e1); max_pair=max(max_pair,e2)
        print(n,p,b,f"{e1:.3e}",f"{e2:.3e}",f"{re:.3e}")
        assert e1 < 1e-8 and e2 < 1e-8
    assert max_inv < 1e-8 and max_pair < 1e-8
    print("PASS off-diagonal real pairing on proper thin dyadic subgroups")

if __name__ == "__main__":
    main()
