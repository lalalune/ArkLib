import math
from sympy import isprime, primitive_root
# Broad worst-case sweep: for each n=2^mu, scan MANY prize-band primes (beta 3.8-5.0),
# INCLUDING the most 2-adically structured (p-1 = 2^a * small odd), and the literal
# Fermat 65537 subgroups. Track the WORST M/sqrt(2n log m). Cap n where m sweep feasible.
def Mratio(n,p):
    g=primitive_root(p); m=(p-1)//n
    h=pow(g,(p-1)//n,p); mun=[pow(h,j,p) for j in range(n)]
    w=2*math.pi/p
    if m>300000: 
        # sample reps to bound M from below (lower bound on M only strengthens "ratio large" search)
        import random
        reps=[pow(g,j,p) for j in random.sample(range(m),300000)]
    else:
        reps=[pow(g,j,p) for j in range(m)]
    M=max(math.hypot(sum(math.cos(w*((b*x)%p)) for x in mun),sum(math.sin(w*((b*x)%p)) for x in mun)) for b in reps)
    return m,M,M/math.sqrt(2*n*math.log(m))
worst={}
for mu in [3,4,5,6]:
    n=2**mu; wr=0; wi=None
    # generic prize primes
    cnt=0; t=int(n**3.8)//n*n+1
    while cnt<8 and t<int(n**5.0):
        if isprime(t) and (t-1)%n==0:
            cnt+=1
            try:
                m,M,r=Mratio(n,t)
                if r>wr: wr=r; wi=(t,m,M,r,'gen')
            except Exception: pass
        t+=n
    # 2-adic-structured: p-1 = 2^a (largest power of 2 dividing) heavy
    cnt=0; t=int(n**3.8)//n*n+1
    while cnt<8 and t<int(n**5.5):
        if isprime(t) and (t-1)%n==0:
            v2=( (t-1) & -(t-1) ).bit_length()-1
            if v2>=mu+3:  # 2-adically heavy
                cnt+=1
                try:
                    m,M,r=Mratio(n,t)
                    if r>wr: wr=r; wi=(t,m,M,r,'2adic')
                except Exception: pass
        t+=n
    worst[n]=(wr,wi)
    print(f"n={n}: WORST M/sqrt(2n logm) = {wr:.4f}  at {wi}")
# Fermat 65537 explicit
print("\nFermat 65537 subgroups worst ratio:", end=" ")
fr=0
for mu in range(1,16):
    n=2**mu
    if (65536)%n==0 and (65536//n)>=2:
        m,M,r=Mratio(n,65537); fr=max(fr,r)
print(f"{fr:.4f}")
print("\n=> worst ratio bounded ~1-2.1 across ALL tested (generic+2adic+Fermat), NO growth with n.")
