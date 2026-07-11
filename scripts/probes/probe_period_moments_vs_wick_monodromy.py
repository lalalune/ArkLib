import numpy as np
from fractions import Fraction as Fr
def is_prime(n):
    if n<2: return False
    for q in (2,3,5,7,11,13,17,19,23,29,31,37,41,43):
        if n%q==0: return n==q
    d=n-1;r=0
    while d%2==0:d//=2;r+=1
    for a in (2,3,5,7,11,13,17,19,23,29,31,37):
        x=pow(a,d,n)
        if x in (1,n-1):continue
        ok=False
        for _ in range(r-1):
            x=x*x%n
            if x==n-1:ok=True;break
        if not ok:return False
    return True
def primroot(p):
    fac=set();m=p-1;d=2
    while d*d<=m:
        while m%d==0:fac.add(d);m//=d
        d+=1
    if m>1:fac.add(m)
    for g in range(2,p):
        if all(pow(g,(p-1)//q,p)!=1 for q in fac):return g
def subgroup(p,n):
    g=primroot(p);w=pow(g,(p-1)//n,p);S=[];x=1
    for _ in range(n):S.append(x);x=x*w%p
    return S
def Ncounts(p,roots,Kmax):
    c=np.zeros(p,dtype=np.int64)
    for r in roots: c[r%p]+=1
    Ns=[]
    for K in range(1,Kmax+1):
        Ns.append(sum(int(v)*int(v) for v in c.tolist()))
        if K<Kmax:
            acc=np.zeros(p,dtype=np.int64)
            for r in roots: acc+=np.roll(c,r%p)
            c=acc
    return Ns
print("Normalized period moments  E|eta_b|^{2k}/(E|eta_b|^2)^k  over b!=0  vs reference values:")
print("  real-iid-Gaussian / Wick = (2k-1)!! = 1, 3, 15, 105   (the energy = additive-energy Wick)")
print("  big UNITARY monodromy trace = 1, 2, 6   (classical-group constraint => BELOW Wick)")
print("="*72)
for n,p in [(8,4129),(16,65537),(16,65617),(32,1048609)]:
    if (p-1)%n!=0 or not is_prime(p): continue
    roots=subgroup(p,n); Km=4
    Ns=Ncounts(p,roots,Km)  # N_k = (1/p) Sum_b |eta_b|^{2k} including b=0
    # Sum_{b!=0} |eta_b|^{2k} = p*N_k - n^{2k}
    m2 = (p*Ns[0]-n**2)               # k=1 numerator (=Sum_{b!=0}|eta|^2)
    mom2 = Fr(m2, p-1)
    out=[]
    for k in range(1,Km+1):
        num = p*Ns[k-1]-n**(2*k)
        momk = Fr(num, p-1)
        norm = float(momk / mom2**k)
        out.append(norm)
    dblfac=[1,1,3,15,105]
    print(f"n={n:3d} p={p:8d}: normalized moments k=1..4 = {[f'{x:.3f}' for x in out]}")
    print(f"            vs (2k-1)!! Wick/Gauss = {dblfac[1:5]}   ratio_to_Wick = {[f'{out[k-1]/dblfac[k]:.3f}' for k in range(1,5)]}")
print()
print("VERDICT: if ~(2k-1)!! (1,3,15,105) the family is iid-Gaussian (Wick), NOT a big-monodromy")
print("classical-group trace (which would be 1,2,6,...< Wick). Big monodromy = WRONG object; the")
print("periods are MORE independent than any monodromy group => prize = sub-Gaussian extreme value.")
