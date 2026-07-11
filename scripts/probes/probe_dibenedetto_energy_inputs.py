import math
# LINCHPIN verification for beating di Benedetto: is the 3rd additive energy T_3(mu_n) = O(n^3) char-p in the
# PRIZE regime (p>n^4), for prize-shaped AND structured (high-v2) primes?  (T_2 is the proven Sidon floor.)
# E_r(mu_n) = (1/p) Sum_{b in F_p} eta_b^{2r},  eta_b = Sum_{x in mu_n} e_p(bx) (REAL since -1 in mu_n).
# Char-0 closed forms (to compare): E_2 = 3n^2 - 3n ;  E_3 = 15n^3 - 45n^2 + 40n.
# di Benedetto uses worst-case general-subgroup T_2<<H^{49/20}, T_3<<H^4. mu_n: T_2~3n^2 (t2=2), T_3~15n^3 (t3=3).
def isprime(z):
    if z<2:return False
    for q in [2,3,5,7,11,13,17,19,23,29,31,37]:
        if z%q==0:return z==q
    d=z-1;r=0
    while d%2==0:d//=2;r+=1
    for a in [2,3,5,7,11,13,17,19,23,29,31,37]:
        x=pow(a,d,z)
        if x in(1,z-1):continue
        ok=False
        for _ in range(r-1):
            x=x*x%z
            if x==z-1:ok=True;break
        if not ok:return False
    return True
def v2(z):
    c=0
    while z%2==0:z//=2;c+=1
    return c
def prroot(p):
    f=[];m=p-1;dd=2
    while dd*dd<=m:
        if m%dd==0:
            f.append(dd)
            while m%dd==0:m//=dd
        dd+=1
    if m>1:f.append(m)
    for g in range(2,p):
        if all(pow(g,(p-1)//x,p)!=1 for x in f):return g
def energies(n,p,g):
    zeta=pow(g,(p-1)//n,p); D=[pow(zeta,i,p) for i in range(n)]
    m=(p-1)//n; tp=2*math.pi/p
    # eta_b real; compute E_2=(1/p)Sum_b eta^4, E_3=(1/p)Sum_b eta^6 over ALL b (b=0 gives eta=n).
    s4=float(n)**4; s6=float(n)**6   # b=0 term
    gj=1
    for j in range(m):
        re=sum(math.cos(((gj*x)%p)*tp) for x in D)
        e=re
        # eta_b constant on the coset b*mu_n (size n) -> multiply by n
        s4+=n*(e**4); s6+=n*(e**6)
        gj=(gj*g)%p
    E2=s4/p; E3=s6/p
    return E2,E3
print("Linchpin: E_2 vs 3n^2-3n (t2=2), E_3 vs 15n^3-45n^2+40n (t3=3). ratios should be ~1 (p-invariant, O(n^3)).")
print(f"{'n':>4} {'v2':>3} {'p':>11} {'E2':>12} {'E2/(3n^2-3n)':>13} {'E3':>14} {'E3/(15n^3-45n^2+40n)':>20} {'E3/n^3':>8}")
for mu in [3,4,5]:
    n=2**mu; lo=n**4; cf2=3*n*n-3*n; cf3=15*n**3-45*n*n+40*n
    # scan a few primes incl the maximal-v2 (structured) one in a window
    found=[]; p=lo|1; bestv2p=None; bestv2=-1
    while len(found)<3:
        if (p-1)%n==0 and isprime(p):
            found.append(p)
        p+=2
    # also grab a high-v2 structured prime in a wider window
    p=lo|1; hi=lo+200*(n**4)
    while p<hi:
        if (p-1)%n==0 and isprime(p):
            vv=v2(p-1)
            if vv>bestv2: bestv2=vv; bestv2p=p
        p+=2
    if bestv2p and bestv2p not in found: found.append(bestv2p)
    for p in found:
        g=prroot(p); E2,E3=energies(n,p,g)
        print(f"{n:>4} {v2(p-1):>3} {p:>11} {E2:>12.1f} {E2/cf2:>13.5f} {E3:>14.1f} {E3/cf3:>20.5f} {E3/n**3:>8.3f}",flush=True)
print("DONE")
