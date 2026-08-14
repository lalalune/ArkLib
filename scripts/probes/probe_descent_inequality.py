import sympy, math
import numpy as np

def Mmax(n, p, z):  # max_b |S_b(mu_n)| via FFT of indicator
    v=np.zeros(p)
    for j in range(n): v[pow(z,j,p)]=1.0
    F=np.abs(np.fft.rfft(v)); F[0]=0
    return F.max()

print("Descent M(n) <= sqrt(2)*M(n/2)?  ratio M(n)/M(n/2) -- should be ~1.414 (descent) not ~2 (trivial).")
print(f"{'n':>5} {'M(n)':>9} {'M(n/2)':>9} {'ratio':>7} {'<=sqrt2?':>8}")
# common prime p with all mu_{2^k} for k up to K: need 2^K | p-1
K=10; p=None; m=1
while True:
    cand=m*(1<<K)+1; m+=1
    if sympy.isprime(cand) and cand>2_000_000: p=cand; break
g=int(sympy.primitive_root(p))
prev=None
for k in range(2,K+1):
    n=1<<k
    z=pow(g,(p-1)//n,p)
    M=Mmax(n,p,z)
    if prev:
        r=M/prev
        print(f"{n:>5} {M:>9.3f} {prev:>9.3f} {r:>7.4f} {'OK' if r<=math.sqrt(2)+0.05 else 'VIOLATES':>8}")
    prev=M
