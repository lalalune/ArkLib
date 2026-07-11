import itertools, cmath, math
# zeroSumCount(mu_n, 5) over C for n=2^k. 5-term vanishing sums of roots of unity.
# Minimal vanishing relations of roots of unity: length 2 (a,-a). length 3 needs 3|n.
# length 5 (regular pentagon) needs 5|n. For n=2^k, 3 not|n and 5 not|n.
# So a vanishing 5-sum must decompose into a vanishing pair {a,-a} + a vanishing TRIPLE,
# but triples vanish only if 3|n => impossible for n=2^k. So zeroSumCount(mu_n,5)=0 over C for n=2^k.
def roots(n): return [cmath.exp(2j*math.pi*t/n) for t in range(n)]
def zsc5(n, tol=1e-9):
    R=roots(n); cnt=0; ex=[]
    for idx in itertools.product(range(n),repeat=5):
        if abs(sum(R[i] for i in idx))<tol:
            cnt+=1
            if len(ex)<3: ex.append(idx)
    return cnt, ex
for k in range(1,5):
    n=2**k
    c,ex=zsc5(n)
    print(f"n=2^{k}={n}: zeroSumCount5={c} examples={ex}")
