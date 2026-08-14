"""
CRAZY angle: the full SPECTRAL DISTRIBUTION (ESD) of the periods {eta_b}. Does it have a HARD EDGE
(semicircle/Kesten-McKay -> deterministic max = a real lead) or a GAUSSIAN/sub-Gaussian tail (-> max via
moments = the wall)? Compute the histogram + the extreme tail + compare max to:
  - Gaussian-Gumbel prediction sqrt(2 n log m)  [iid heuristic]
  - the actual max
  - the tail decay rate (count eta_b > t*sqrt(n) for increasing t)
A hard edge would mean #{eta_b > edge} = 0 exactly -- a deterministic cutoff. Gaussian tail = no cutoff.
"""
import math
def isprime(m):
    if m<2:return False
    for q in(2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53):
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
def primes1modn(n,lo):
    p=lo+(n-lo%n)+1
    while p%n!=1 or not isprime(p): p+=1
    return p
def subgroup(p,n):
    e=(p-1)//n
    for c in range(2,p):
        h=pow(c,e,p)
        if pow(h,n,p)==1 and len({pow(h,i,p) for i in range(n)})==n:
            return [pow(h,i,p) for i in range(n)]
def all_periods(p,n):
    S=subgroup(p,n); g=2
    while pow(g,(p-1)//2,p)==1: g+=1
    m=(p-1)//n
    return [sum(math.cos(2*math.pi*(pow(g,j,p)*x%p)/p) for x in S) for j in range(m)]

for n in (16, 32):
    p=primes1modn(n, 50*n**4)
    et=all_periods(p,n); m=len(et)
    sn=math.sqrt(n)
    norm=[e/sn for e in et]  # normalize by sqrt(n) (the Parseval scale)
    M=max(abs(e) for e in et)
    gumbel=math.sqrt(2*n*math.log(m))
    print(f"=== n={n}, p={p}, m={m} periods ===")
    print(f"  M=max|eta|={M:.3f}, sqrt(2 n log m)={gumbel:.3f}, M/gumbel={M/gumbel:.3f}")
    print(f"  mean(eta)={sum(et)/m:.3f} (should ~ -n/m~0), var={sum(e*e for e in et)/m:.3f} (should ~ n={n})")
    # tail: #{|eta|/sqrt(n) > t} for t = 2,3,4,5,6,... -- Gaussian predicts m*2*(1-Phi(t)), hard edge = 0 past edge
    print(f"  TAIL #{{|eta|/sqrt(n) > t}} (Gaussian m*erfc(t/sqrt2) in parens):")
    for t in (2,3,4,5,6,7):
        cnt=sum(1 for e in norm if abs(e)>t)
        gauss_pred = m*math.erfc(t/math.sqrt(2))
        print(f"    t={t}: actual={cnt:>6}  gaussian~{gauss_pred:>8.1f}")
    edge=M/sn
    print(f"  normalized max edge = M/sqrt(n) = {edge:.3f}  (Gaussian-Gumbel edge ~ sqrt(2 log m)={math.sqrt(2*math.log(m)):.3f})")
    print(f"  => {'HARD EDGE suspected (tail drops to 0 sharply)' if sum(1 for e in norm if abs(e)>edge*0.95)<5 else 'GAUSSIAN/soft tail (no hard edge) -> reduces to moment wall'}")
    print()
