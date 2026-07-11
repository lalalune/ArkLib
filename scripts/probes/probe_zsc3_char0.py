# Char-0 zeroSumCount(mu_n, 3): ordered triples (x,y,z) in mu_n^3 with x+y+z=0, over C (exact via cyclotomic).
# mu_n = {exp(2pi i k/n)}. Use exact algebraic test: x+y+z=0 with x,y,z n-th roots.
# For n=2^a, test ALL ordered triples (with repetition) for exact zero sum.
import cmath, itertools
def mu_n(n):
    return [cmath.exp(2j*cmath.pi*k/n) for k in range(n)]
print("n   zsc3(char0)  (ordered triples summing to 0, incl repeats)")
for a in range(2,7):
    n=2**a
    S=mu_n(n)
    cnt=0
    for x,y,z in itertools.product(range(n),repeat=3):
        s=S[x]+S[y]+S[z]
        if abs(s)<1e-9: cnt+=1
    print(f"{n:3d}  {cnt}")
# also: does ANY triple with repetition sum to 0? e.g. x,x,y => 2x = -y, |2x|=2 != 1=|y|, impossible.
# x,y,z distinct => char0 dichotomy says needs 3|n. So expect 0 for all 2^a.
