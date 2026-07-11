"""
Undeterminability probe (#444): is delta* (the exact constant C=M/sqrt(n log(q/n))) a SINGLE determinable
value, or PRIME-ARITHMETIC-DEPENDENT / oscillating? If C varies across primes at fixed n (beyond noise),
or oscillates in n, then 'THE exact delta*' is ill-posed as a universal constant -- a genuine (weak)
'cannot be determined as one number' result. If C is prime-stable + converging, delta* is a single value
(determinable once BGK is proven).
M(n) = max_{b!=0} |eta_b|, eta_b = sum_{x in mu_n} cos(2 pi b x / p) (REAL for 2-power n).
"""
import math
def isprime(m):
    if m<2:return False
    for q in(2,3,5,7,11,13,17,19,23,29,31,37,41,43,47):
        if m%q==0:return m==q
    d=m-1;s=0
    while d%2==0:d//=2;s+=1
    for a in(2,3,5,7,11,13,17,19,23,29,31,37):
        x=pow(a,d,m)
        if x in(1,m-1):continue
        for _ in range(s-1):
            x=x*x%m
            if x==m-1:break
        else:return False
    return True
def primes1modn(n,lo,cnt):
    out=[];p=lo+(n-lo%n)+1
    while len(out)<cnt:
        if p%n==1 and isprime(p):out.append(p)
        p+=n
    return out
def subgroup(p,n):
    e=(p-1)//n
    for c in range(2,p):
        h=pow(c,e,p)
        if pow(h,n,p)==1 and len({pow(h,i,p) for i in range(n)})==n:
            return [pow(h,i,p) for i in range(n)]
def M_of(p,n):
    S=subgroup(p,n)
    g=2
    while pow(g,(p-1)//2,p)==1: g+=1
    m=(p-1)//n
    best=0.0
    # sample over up to ~4000 cosets (enough for the max at these sizes); full for small m
    step=max(1,m//4000)
    for j in range(0,m,step):
        b=pow(g,j,p)
        e=sum(math.cos(2*math.pi*(b*x%p)/p) for x in S)
        if abs(e)>best: best=abs(e)
    return best

print("=== (1) prime-DEPENDENCE of C at fixed n: is the constant universal or arithmetic-gated? ===")
print(f"{'n':>4} {'prime p':>12} {'p type':>14} {'M(n)':>9} {'sqrt(n log(q/n))':>16} {'C=M/sqrt':>9}")
for n in (8,16,32):
    # several thin primes p>n^4 + the smallest Fermat-ish (p=1 mod large power of 2)
    ps=primes1modn(n,50*n**4,3)
    for p in ps:
        M=M_of(p,n); base=math.sqrt(n*math.log(p/n)); C=M/base
        v2=0; t=p-1
        while t%2==0: v2+=1; t//=2
        ptype=f"v2(p-1)={v2}"
        print(f"{n:>4} {p:>12} {ptype:>14} {M:>9.4f} {base:>16.4f} {C:>9.4f}")
    print()
print("=== (2) oscillation in n: does C(n) converge or oscillate (limsup vs liminf)? ===")
print(f"{'n':>5} {'p (thin)':>12} {'M(n)':>9} {'C(n)':>8} {'M(2n)/M(n)':>11}")
prevM=None
for n in (8,16,32,64):
    p=primes1modn(n,50*n**4,1)[0]
    M=M_of(p,n); base=math.sqrt(n*math.log(p/n)); C=M/base
    ratio = (M/prevM) if prevM else float('nan')
    print(f"{n:>5} {p:>12} {M:>9.4f} {C:>8.4f} {ratio:>11.4f}")
    prevM=M
