import math
def is_prime(m):
    if m<2: return False
    i=2
    while i*i<=m:
        if m%i==0: return False
        i+=1
    return True
def find_prime(n,lo):
    p=lo
    while True:
        if (p-1)%n==0 and is_prime(p): return p
        p+=1
def subgroup(p,n):
    for g0 in range(2,p):
        # find element of order n
        g=pow(g0,(p-1)//n,p)
        s={pow(g,i,p) for i in range(n)}
        if len(s)==n: return [pow(g,i,p) for i in range(n)]
    return None
def double_fact(m):  # (2r-1)!!
    r=1
    k=m
    while k>0:
        r*=k; k-=2
    return r

def run(n,p):
    import cmath
    H=subgroup(p,n)
    # eta_b = sum_{x in H} cos(2pi b x/p) (real part; for 2-power n the imag cancels)
    # compute eta_b for all b=1..p-1
    twopi=2*math.pi
    # precompute
    etas=[]
    for b in range(1,p):
        s=0.0
        for x in H:
            s+=math.cos(twopi*(b*x % p)/p)
        etas.append(s)
    print(f"\n n={n} p={p}  log_n(p)={math.log(p)/math.log(n):.2f}  ln(p)={math.log(p):.1f}")
    print(f"  {'r':>2} {'M_r':>14} {'Gaussian p*(2r-1)!!*n^r':>26} {'ratio':>8}")
    for r in range(1,16):
        Mr=sum(e**(2*r) for e in etas)
        gauss=p*double_fact(2*r-1)*(n**r)
        ratio=Mr/gauss
        flag=""
        if ratio>2: flag=" <-- DEPARTS"
        print(f"  {r:>2} {Mr:>14.3e} {gauss:>26.3e} {ratio:>8.3f}{flag}")

for (n,p) in [(8, find_prime(8, 8**3)), (8, find_prime(8, 8**5)), (16, find_prime(16,16**3))]:
    run(n,p)
