# Candidate P10/P13: the 2-adic energy doubling recursion.
# μ_{2n} = μ_n ∪ ζ·μ_n (ζ primitive 2n-th root, ζ²∈μ_n). Does E(μ_{2n}) ≤ 4 E(μ_n) + O(n)?
# If so, induction gives E(μ_{2^m}) = O(4^m) = O(n²). Probe over split fields.
import sympy
from collections import Counter
def energy_of(G, p):
    r = Counter((a+b)%p for a in G for b in G)
    return sum(v*v for v in r.values())
def musub(n,p):
    g=sympy.primitive_root(p); h=pow(g,(p-1)//n,p)
    return [pow(h,j,p) for j in range(n)]
print(f"{'n':>5}{'p':>9}{'E(n)':>9}{'E(2n)':>10}{'E(2n)/E(n)':>12}{'(E2n-4En)/n':>14}")
for m in range(2,8):
    n=2**m; n2=2*n
    # prime p ≡ 1 mod 2n, p ≈ (2n)^3
    target=n2**3
    p=None
    for cand in range(target - target%n2 + 1, target*2, n2):
        if sympy.isprime(cand): p=cand; break
    if p is None: continue
    Gn=musub(n,p); G2n=musub(n2,p)
    # sanity: μ_n ⊂ μ_{2n}
    En=energy_of(Gn,p); E2n=energy_of(G2n,p)
    print(f"{n:>5}{p:>9}{En:>9}{E2n:>10}{E2n/En:>12.3f}{(E2n-4*En)/n:>14.2f}")
