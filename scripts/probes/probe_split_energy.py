# DECISIVE PROBE: additive energy E(μ_n) of the 2-power multiplicative subgroup in the
# SPLIT case n|p-1 (μ_n ⊂ F_p), for production-like p. Is E ≈ 3n² (char-0) or ~n^{8/3} (GV)?
import sympy
def subgroup(n, p):
    # μ_n = elements of order dividing n in F_p^*; need n | p-1
    g = sympy.primitive_root(p)
    h = pow(g, (p-1)//n, p)  # generator of μ_n
    return [pow(h, j, p) for j in range(n)]
def energy(G, p):
    # E = #{(a,b,c,d): a+b=c+d}; via r(t)=#{(a,b): a+b=t}, E = Σ_t r(t)²
    from collections import Counter
    r = Counter((a+b) % p for a in G for b in G)
    return sum(v*v for v in r.values())
def maxrep(G, p):
    from collections import Counter
    r = Counter((a-b) % p for a in G for b in G if a!=b)  # t=a-b, t≠0
    return max(v for t,v in r.items() if t!=0) if r else 0

print(f"{'n':>4}{'p':>8}{'E':>10}{'3n²':>10}{'E/n²':>8}{'n^(8/3)':>10}{'maxrep':>8}{'4n^(2/3)':>10}")
import math
for m in range(2, 9):
    n = 2**m
    # find a prime p ≡ 1 mod n, production-like p ≈ n^2 .. n^3
    for target in [n*n, n*n*n]:
        p = None
        c = max(target,3)
        # next prime ≡ 1 mod n above target
        for cand in range(c - c%n + 1, c*2, n):
            if cand>1 and sympy.isprime(cand):
                p = cand; break
        if p is None: continue
        G = subgroup(n, p)
        E = energy(G, p); mr = maxrep(G, p)
        print(f"{n:>4}{p:>8}{E:>10}{3*n*n:>10}{E/(n*n):>8.2f}{n**(8/3):>10.1f}{mr:>8}{4*n**(2/3):>10.1f}")
