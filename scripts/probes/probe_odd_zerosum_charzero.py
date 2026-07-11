import itertools, cmath, math
# Test: is zeroSumCount(mu_n, r) = 0 over C for ALL odd r when n=2^k?
# Conjecture: a sum of an ODD number of unit-modulus complex numbers each a 2^k-th root of unity
# cannot be 0 ... actually that's NOT obviously true. Let's check odd r=3,5,7,9 for small n.
def roots(n): return [cmath.exp(2j*math.pi*t/n) for t in range(n)]
def zsc(n,r,tol=1e-9):
    R=roots(n); cnt=0
    for idx in itertools.product(range(n),repeat=r):
        if abs(sum(R[i] for i in idx))<tol: cnt+=1
    return cnt
for n in [2,4,8]:
    for r in [3,5,7,9]:
        if n**r > 5_000_000:
            print(f"n={n} r={r}: SKIP (too big)"); continue
        print(f"n={n} r={r}: zeroSumCount={zsc(n,r)}")
