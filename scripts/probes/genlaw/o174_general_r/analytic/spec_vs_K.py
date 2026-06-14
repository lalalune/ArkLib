import itertools, math, cmath
def mu(n): return [cmath.exp(2j*math.pi*j/n) for j in range(n)]
def spectrum_card(n, m, tol=1e-7):
    M=mu(n); seen=set()
    for S in itertools.combinations(range(n), m):
        s=sum(M[i] for i in S)
        seen.add((round(s.real/tol), round(s.imag/tol)))
    return len(seen)
print("n=16: r  |spec(r+1)|  K=2^r C(8,r)  spec<=K?  #bad")
ladder={3:97,4:145,5:89,6:113,7:225,8:104}
for r in range(3,9):
    sp=spectrum_card(16,r+1); K=2**r*math.comb(8,r)
    print(f"      {r}  {sp:>6}      {K:>6}    {str(sp<=K):>5}   {ladder[r]}")
