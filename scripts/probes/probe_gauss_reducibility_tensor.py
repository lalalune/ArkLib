import numpy as np, math, cmath
# DECISIVE: does the resonance R (and the periods) TENSORIZE over the prime factorization of m?
# If R(index m=q1*q2) = R(index q1)*R(index q2), Gauss-reducibility reduces the m-problem to small primes.
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
def periods_index(p,idx):
    # Gaussian periods of the subgroup of INDEX idx (order (p-1)/idx). Returns the idx period values.
    g=proot(p); order=(p-1)//idx
    h=pow(g,(p-1)//order,p); sub=[pow(h,i,p) for i in range(order)]
    reps=[pow(g,i,p) for i in range(idx)]
    return np.array([sum(cmath.exp(2j*math.pi*((r*x)%p)/p) for x in reps and sub).real for r in reps]) if False else \
           np.array([sum(cmath.exp(2j*math.pi*((r*x)%p)/p) for x in sub).real for r in reps])
def resonance(p,idx):
    # R = max over the idx periods of |period| (the period IS the resonance object up to scaling)
    eta=periods_index(p,idx)
    return np.abs(eta).max(), eta
print("TENSOR TEST: does M/resonance of index m=q1*q2 factor as f(index q1, index q2)?",flush=True)
for p in [4129, 7681, 10369, 8101]:
    if not isprime(p):continue
    pm1=p-1; n=1
    while pm1%2==0: pm1//=2; n*=2
    m=pm1; fm=fac(m)
    if len(fm)<2 or m>2000: 
        print(f"p={p}: m={m}={dict(fm)} (prime or large, skip)"); continue
    qs=list(fm); q1=qs[0]**fm[qs[0]]; q2=m//q1
    Rm,etam=resonance(p,m)       # index m (= the 2-power FFT subgroup, since n=oddcomplement... wait index m => order n)
    Rq1,_=resonance(p,q1)        # index q1 (larger subgroup)
    Rq2,_=resonance(p,q2)        # index q2
    sn=math.sqrt(n)
    print(f"\np={p}: n(2-part)={n}, m={m}={q1}*{q2}",flush=True)
    print(f"  M(index m, the FFT subgroup order n)={Rm:.3f}",flush=True)
    print(f"  M(index q1={q1})={Rq1:.3f}  M(index q2={q2})={Rq2:.3f}  product/sqrt(p)={Rq1*Rq2/math.sqrt(p):.3f}",flush=True)
    print(f"  test Rm vs Rq1*Rq2/sqrt(p): {Rm:.3f} vs {Rq1*Rq2/math.sqrt(p):.3f}  ratio={Rm/(Rq1*Rq2/math.sqrt(p)+1e-9):.3f}",flush=True)
    print(f"  test Rm vs Rq1*Rq2/sqrt(order_complement)...  | floor sqrt(2n log m)={math.sqrt(2*n*math.log(m)):.3f}",flush=True)
print("\nIf Rm = Rq1*Rq2/sqrt(p) (or similar clean tensor), the resonance FACTORS over m's primes => reduction.",flush=True)
print("DONE")
