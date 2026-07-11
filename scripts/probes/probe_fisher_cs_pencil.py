#!/usr/bin/env python3
r"""
PROBE the CAUCHY-SCHWARZ / Fisher double-count for the dilation pencil (the form the sunflower
scope note names: "r^2 <~ M*N by a Cauchy-Schwarz/Fisher double-count, with no common T").

Setup: r blocks B_i subset univ (|univ|=N), each |B_i|=r, all contain apex p, punctured pairwise
|(B_i\{p}) cap (B_j\{p})| <= M.  Let C_i = B_i\{p}, |C_i|=r-1, over N-1 non-apex slots.
  deg(x) = #{i : x in C_i},  sum_x deg(x) = r(r-1)  [over x in U=union C_i, |U|<=N-1].
  sum_{i<j}|C_i cap C_j| = sum_x C(deg x,2) <= C(r,2)*M.
  Cauchy-Schwarz over the |U| non-apex support:  (sum deg)^2 <= |U| * sum deg^2.
  sum deg^2 = sum(2 C(deg,2) + deg) <= 2*C(r,2)*M + r(r-1).
  => (r(r-1))^2 <= |U| * (2*C(r,2)*M + r(r-1)) <= (N-1)*(r(r-1) + r(r-1)*M)  [since 2C(r,2)=r(r-1)]
  => (r(r-1))^2 <= (N-1)*r(r-1)*(1+M)
  => r(r-1) <= (N-1)*(1+M)
This is the CLEAN CS-Fisher bound:  r*(r-1) <= (M+1)*(N-1).
Compare to Bonferroni r(r-1) <= C(r,2)*M + (N-1): for small M the CS form is MUCH stronger.
At M=0: r(r-1) <= N-1 (= pencil_card_core, EXACT). At M~n/2: r(r-1) <= (n/2)(N-1) ~ Johnson collapse.
"""
import math, random

def is_prime(n):
    if n<2: return False
    i=2
    while i*i<=n:
        if n%i==0: return False
        i+=1
    return True

def subgroup(p,n):
    g=2
    while True:
        o=1;x=g%p
        while x!=1: x=x*g%p;o+=1
        if o==p-1: break
        g+=1
    h=pow(g,(p-1)//n,p)
    mu=[];x=1
    for _ in range(n): mu.append(x);x=x*h%p
    return mu

print("Testing CS-Fisher: r(r-1) <= (M+1)(N-1)  [and the intermediate (sum deg)^2 <= |U| sum deg^2]")
print("n   p      M   r   r(r-1)  (M+1)(N-1)  CS_holds  bonf=C(r,2)M+(N-1)  CS_tighter_than_bonf")
allhold=True
for a in range(2,6):
    n=2**a
    k=max(1,int(n**3.5)//n)
    while True:
        cand=k*n+1
        if cand>n and is_prime(cand): p=cand;break
        k+=1
    mu=subgroup(p,n); muset=set(mu)
    N=n
    for trial in range(3):
        random.seed(a*10+trial)
        r=random.randint(2,n)
        S=random.sample(mu,r) if r<=n else mu
        Sset=set(S)
        # build pencil blocks B_zeta = {zeta^{-1} x mod p : x in S}, apex = 1
        blocks=[]
        for zeta in S:
            zinv=pow(zeta,-1,p)
            B=set((zinv*x)%p for x in S)
            blocks.append(B)
        apex=1
        # verify apex in all, size r
        assert all(apex in B and len(B)==r for B in blocks)
        # punctured pairwise max
        C=[B-{apex} for B in blocks]
        M=0
        for i in range(len(C)):
            for j in range(i+1,len(C)):
                M=max(M,len(C[i]&C[j]))
        # CS bound
        lhs=r*(r-1)
        csrhs=(M+1)*(N-1)
        bonf=(r*(r-1)//2)*M + (N-1)
        cshold = lhs<=csrhs
        if not cshold: allhold=False
        cstighter = csrhs<=bonf
        print(f"{n:3d} {p:6d} {M:3d} {r:3d}  {lhs:6d}  {csrhs:8d}    {cshold}     {bonf:8d}          {cstighter}")
print("ALL CS bounds hold:", allhold)
