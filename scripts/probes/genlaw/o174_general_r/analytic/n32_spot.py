# n=32 r=4 (a=5), r=5 (a=6) spot check of full e1-spectrum (UPPER bound on #bad) and K, char 0.
import itertools, math, cmath
def spec(n,m,tol=1e-6):
    M=[cmath.exp(2j*math.pi*j/n) for j in range(n)]
    seen=set()
    for S in itertools.combinations(range(n),m):
        s=sum(M[i] for i in S)
        seen.add((round(s.real,5),round(s.imag,5)))
    return len(seen)
for r in [4,5]:
    K=2**r*math.comb(16,r)
    sp=spec(32,r+1)
    print(f"n=32 r={r}: full spectrum(r+1={r+1})={sp}  K={K}  spectrum<=K? {sp<=K}")
