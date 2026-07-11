import math
def is_prime(m):
    if m<2:return False
    i=2
    while i*i<=m:
        if m%i==0:return False
        i+=1
    return True
# fixed large p with p-1 divisible by big 2-power
def find_p_pow2(kmax, lo):
    M=1<<kmax
    p=((lo//M)+1)*M+1
    while not is_prime(p): p+=M
    return p
def subgroup(p,n):
    for g0 in range(2,p):
        g=pow(g0,(p-1)//n,p)
        if len({pow(g,i,p) for i in range(n)})==n:
            return [pow(g,i,p) for i in range(n)]
def maxperiod(H,p):
    tp=2*math.pi; B=0.0
    for b in range(1,p):
        c=sum(math.cos(tp*(b*x%p)/p) for x in H); s=sum(math.sin(tp*(b*x%p)/p) for x in H)
        m=math.hypot(c,s)
        if m>B:B=m
    return B
kmax=9
p=find_p_pow2(kmax, 300000)   # fixed prime, p-1 div by 2^9
lnp=math.log(p)
print(f"fixed p={p}, ln p={lnp:.2f}, p-1 div by 2^{kmax}")
print(f"{'k':>2} {'n=2^k':>6} {'B':>9} {'sqrt(n)':>8} {'sqrt(2n ln p)':>13} {'B/sqrt(n)':>9} {'log2(B)/k(=exp/0.5?)':>12}")
prevB=None
for k in range(1,kmax+1):
    n=1<<k
    H=subgroup(p,n); B=maxperiod(H,p)
    exp_n = math.log(B)/math.log(n) if n>1 else 0  # empirical exponent: B ~ n^exp
    print(f"{k:>2} {n:>6} {B:>9.3f} {math.sqrt(n):>8.3f} {math.sqrt(2*n*lnp):>13.3f} {B/math.sqrt(n):>9.4f} {exp_n:>12.4f}")
    prevB=B
print("\nIf B ~ n^{1/2+o(1)} (prize square-root), the 'exp' column -> 0.5 and B/sqrt(n) grows only ~sqrt(log).")
print("If general n^{1-nu}, exp stays well above 0.5.")
