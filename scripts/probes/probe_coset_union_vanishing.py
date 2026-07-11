import cmath, itertools, math
def roots(n):
    return [cmath.exp(2j*cmath.pi*k/n) for k in range(n)]
def is_zero(z, tol=1e-9):
    return abs(z) < tol
# Claim: in mu_n (n=2^a) subset C, a UNION of cosets of the order-d subgroup H_d (d | n, d>=2)
# has subset-sum 0, because each coset {zeta^{i+kd} : k} = zeta^i * {d-th roots} sums to 0.
# Count of coset-unions = 2^{n/d}. This is a depth-(d-1) vanishing LOWER bound: 2^{n/d} <= V_1(mu_n).
# (matches OverdetVanishingCosetCount: coset-union supply.)
for n in [8,16]:
    R = roots(n)
    for d in [2,4,8]:
        if n % d: continue
        ncos = n//d
        # cosets indexed by residue i in 0..d-1, members {i, i+d, i+2d, ...}
        cosets = [[ (i + k*d) for k in range(ncos)] for i in range(d)]
        # each coset sums to 0?
        each0 = all(is_zero(sum(R[idx] for idx in cos)) for cos in cosets)
        # every union of cosets sums to 0?
        ok = True
        for mask in range(1<<d):
            chosen=[]
            for i in range(d):
                if mask & (1<<i): chosen += cosets[i]
            if not is_zero(sum(R[idx] for idx in chosen) if chosen else 0+0j):
                ok=False; break
        print(f"n={n} d={d}: #cosets={d}, each-coset-sums-0={each0}, all-unions-vanish={ok}, #unions=2^{d}")
