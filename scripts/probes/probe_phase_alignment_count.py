import sympy, math
import numpy as np

# fixed prime with 2^K | p-1
K=11; m=1
while True:
    p=m*(1<<K)+1; m+=1
    if sympy.isprime(p) and p>5_000_000: break
g=int(sympy.primitive_root(p))

def Sabs(b,k):  # |S_b(mu_{2^k})|
    z=pow(g,(p-1)//(1<<k),p)
    s=sum(np.exp(2j*math.pi*(b*pow(z,j,p)%p)/p) for j in range(1<<k))
    return abs(s)

print(f"p={p} (~2^{math.log2(p):.0f}), log log p ~ {math.log(math.log(p)):.1f}")
print("For worst b at level K, count aligned levels (per-step ratio > 1.8).")
for K2 in (7,9,11):
    # find worst b for mu_{2^K2} by FFT
    n=1<<K2; z=pow(g,(p-1)//n,p)
    v=np.zeros(p); 
    for j in range(n): v[pow(z,j,p)]=1.0
    F=np.abs(np.fft.rfft(v)); F[0]=0
    b=int(np.argmax(F))
    # track |S_b(mu_2^j)| for j=1..K2
    mags=[Sabs(b,j) for j in range(1,K2+1)]
    ratios=[mags[j]/mags[j-1] for j in range(1,len(mags))]
    aligned=sum(1 for r in ratios if r>1.8)
    print(f"  K={K2} (n={n}): M={mags[-1]:.2f}, sqrt(n logp)={math.sqrt(n*math.log(p)):.2f}, #aligned levels(r>1.8)={aligned} / {len(ratios)}")
