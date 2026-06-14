import numpy as np, math, cmath
# Define the free variable R / T_r, verify M=sqrt(n/m)*R, AND investigate "Gauss is reducible":
# for m=odd part of p-1 COMPOSITE, does tau(chi) factor via Hasse-Davenport into prime-order pieces,
# and does the resonance R factor over m's prime factors (tensor/CRT structure)?
def isprime(x):
    if x<2:return False
    for q in [2,3,5,7,11,13,17,19,23,29,31,37,41,43]:
        if x%q==0:return x==q
    d=x-1;s=0
    while d%2==0:d//=2;s+=1
    for a in [2,3,5,7,11,13,17,19,23,29,31,37]:
        y=pow(a,d,x)
        if y in(1,x-1):continue
        ok=False
        for _ in range(s-1):
            y=y*y%x
            if y==x-1:ok=True;break
        if not ok:return False
    return True
def fac(x):
    f={};d=2
    while d*d<=x:
        while x%d==0:f[d]=f.get(d,0)+1;x//=d
        d+=1
    if x>1:f[x]=f.get(x,0)+1
    return f
def proot(p):
    fs=set(fac(p-1))
    for g in range(2,p):
        if all(pow(g,(p-1)//q,p)!=1 for q in fs):return g
def gauss(p,g,jpow):  # tau(chi^jpow), chi = char of order p-1 sending g->e(1/(p-1))
    # chi(g^k)=e(k/(p-1)); tau(chi^a)=sum_{t!=0} chi^a(t) e_p(t)
    w=cmath.exp(2j*math.pi/(p-1))
    # build discrete log table
    dl={}; cur=1
    for k in range(p-1): dl[cur]=k; cur=cur*g%p
    s=0j
    for t in range(1,p):
        s+=w**((jpow*dl[t])%(p-1))*cmath.exp(2j*math.pi*t/p)
    return s
# pick primes where m=oddpart(p-1) is composite
print("Investigate Gauss reducibility: m=oddpart(p-1) factorization, tau-reduction, resonance structure",flush=True)
for p in [4129, 12289, 7681, 10369]:
    if not isprime(p):continue
    pm1=p-1; n=1
    while pm1%2==0: pm1//=2; n*=2
    m=pm1  # odd part
    g=proot(p)
    fm=fac(m)
    print(f"\np={p}: p-1=2^{int(math.log2(n))}*{m}, n(2-part)={n}, m(odd index)={m} = {dict(fm)} {'PRIME' if len(fm)==1 and list(fm.values())[0]==1 else 'COMPOSITE'}",flush=True)
    if m>4000: print("  (m large, skip Gauss compute)"); continue
    # the index-m subgroup mu_n = n-th... wait: mu of order n=2-part is the FFT subgroup; index m.
    # periods of the order-n subgroup: eta_i, i in Z/m. M=max|eta_i|.
    h=pow(g,(p-1)//n,p); mu=[pow(h,i,p) for i in range(n)]
    reps=[pow(g,i,p) for i in range(m)]
    eta=np.array([sum(cmath.exp(2j*math.pi*((r*x)%p)/p) for x in mu).real for r in reps])
    M=np.abs(eta).max()
    # Gauss reduction: chi of order m = g^{n} has order m (since g^n has order (p-1)/gcd(n,p-1)=m).
    # tau(chi^l) for l=1..m-1. Check Hasse-Davenport: tau(chi_1 chi_2)=tau(chi_1)tau(chi_2)/J for coprime orders.
    if len(fm)>=2:
        qs=list(fm); q1=qs[0]**fm[qs[0]]; q2=m//q1  # coprime split m=q1*q2
        # chi_1 = chi^{q2} (order q1), chi_2=chi^{q1} (order q2); chi=chi_1^{a} chi_2^{b} via CRT
        chi_g_pow = n  # chi = char sending g -> e(n/(p-1))? chi=g-dual of order m => chi(g)=e(1/m) via g^n
        t_full=gauss(p,g,n)           # tau(chi), chi order m
        t1=gauss(p,g,n*q2 % (p-1))    # tau(chi^{q2}) order q1
        t2=gauss(p,g,n*q1 % (p-1))    # tau(chi^{q1}) order q2
        # Jacobi: J(chi^{q2},chi^{q1}) = tau(chi^{q2})tau(chi^{q1})/tau(chi^{q2+q1})
        tsum=gauss(p,g,n*(q1+q2)%(p-1))
        J = t1*t2/tsum if abs(tsum)>1e-9 else None
        print(f"  m={q1}*{q2} (coprime). |tau(chi)|/sqrt(p)={abs(t_full)/math.sqrt(p):.4f} |tau1|/sqrt p={abs(t1)/math.sqrt(p):.4f} |tau2|/sqrt p={abs(t2)/math.sqrt(p):.4f} |J|/sqrt p={abs(J)/math.sqrt(p) if J else 0:.4f}",flush=True)
        print(f"  Hasse-Davenport tau(chi^q2)tau(chi^q1)=J*tau(chi^{{q1+q2}}): ratio {abs(t1*t2/(J*tsum)) if J else 0:.6f} (=1 confirms reducibility)",flush=True)
    print(f"  M(2-part subgroup)={M:.3f}, sqrt(n)={math.sqrt(n):.3f}, floor sqrt(2n log m)={math.sqrt(2*n*math.log(m)):.3f}, M/floor={M/math.sqrt(2*n*math.log(m)):.3f}",flush=True)
print("DONE")
