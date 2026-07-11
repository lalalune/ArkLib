import itertools, sympy, math
from collections import Counter

def mu_n(p, n):
    g = sympy.primitive_root(p)
    h = pow(g, (p-1)//n, p)
    return sorted({pow(h, k, p) for k in range(n)})

def fiber_counts(G, r, p):
    cnt = Counter()
    for v in itertools.product(G, repeat=r):
        cnt[sum(v) % p] += 1
    return cnt

def rEnergy_from(cnt):
    return sum(c*c for c in cnt.values())

print("PROBE: depth-r energy ceiling over PROPER thin mu_n, p>>n^3, p==1 mod n")
print("Candidate structural ceiling: E_r(G) <= |G|^{r-1} * R_r,  R_r = max_t fiber(t)")
print("and the convolution recursion E_r = sum_t r_r(t)^2, r_r(t)=#{v:sum v=t}.")
for n in [4, 8, 16]:
    p = None
    cand = max(n*1000+1, n**3*3)
    while p is None:
        if cand % n == 1 and sympy.isprime(cand):
            p = cand
        cand += 1
    G = mu_n(p, n)
    print(f"\nn={n} p={p} |G|={len(G)} (p/n^3={p/n**3:.1f})")
    rmax = 5 if n<=8 else 3
    for r in range(1, rmax+1):
        cnt = fiber_counts(G, r, p)
        E = rEnergy_from(cnt)
        Gr = len(G)**r
        Rr = max(cnt.values())              # max fiber (incl t=0)
        Rr_off = max((c for t,c in cnt.items() if t!=0), default=0)
        triv = len(G)**(2*r-1)
        # candidate: E_r <= |G|^{r-1} * sum_t r_r(t) = |G|^{2r-1} trivial
        # sharper:   E_r <= Rr * sum_t r_r(t) = Rr * |G|^r
        cand_bound = Rr * Gr
        print(f"  r={r}: E_r={E:>9} Rr(max fiber)={Rr:>6} Rr_off={Rr_off:>6} "
              f"Rr*|G|^r={cand_bound:>10} E<=Rr*|G|^r? {E<=cand_bound} "
              f"|G|^(2r-1)={triv:>10} E/|G|^r={E/Gr:6.3f}")
