# Follow-up: is the exact bad-scalar census EXACTLY the stratified-spread set
# (sums over ALL r-subsets, including antipodal pairs => lower strata)?
from itertools import combinations
p = 4129
def is_prim(z):
    for q in (2, 3, 43):
        if pow(z, (p-1)//q, p) == 1: return False
    return True
z = next(z for z in range(2, 200) if is_prim(z))
g8 = pow(z, (p-1)//8, p)
H = [pow(g8, i, p) for i in range(8)]
def interp_val(pts, x):
    s = 0
    for i, (xi, yi) in enumerate(pts):
        num = den = 1
        for j, (xj, _) in enumerate(pts):
            if i != j:
                num = num * (x - xj) % p
                den = den * (xi - xj) % p
        s = (s + yi * num * pow(den, p-2, p)) % p
    return s
def close_to_code(vals, domain, degbound, agree_t):
    n = len(domain)
    for S in combinations(range(n), agree_t):
        base = [(domain[i], vals[i]) for i in S[:degbound+1]]
        if all(interp_val(base, domain[i]) == vals[i] for i in S[degbound+1:]):
            return True
    return False
orig_bad = set(lam for lam in range(p)
               if close_to_code([(pow(x,4,p) + lam*pow(x,3,p)) % p for x in H], H, 2, 4))
# stratified prediction: -sum(T) for ALL 4-subsets T of mu_8 (antipodal pairs sum to 0)
strat = set((-sum(T)) % p for T in combinations(H, 4))
print("exact census:", len(orig_bad), "| all-4-subset sums:", len(strat),
      "| equal sets:", strat == orig_bad)
# stratified closed form check: sum_j 2^(r-2j) C(s/2, r-2j) at s=8,r=4
from math import comb
print("stratified closed form:", sum(2**(4-2*j) * comb(4, 4-2*j) for j in range(3)))
# folded side: s=4, r=2 on mu_4
mu4 = [pow(g8, 2*i, p) for i in range(4)]
beta = 7
fold_bad = set(g for g in range(p)
               if close_to_code([(pow(y,2,p) + g*beta*y) % p for y in mu4], mu4, 0, 2))
strat4 = set((-sum(T)) * pow(beta, p-2, p) % p for T in combinations(mu4, 2))
print("folded census:", len(fold_bad), "| 2-subset sums/beta:", len(strat4),
      "| equal sets:", strat4 == fold_bad)
print("folded closed form:", sum(2**(2-2*j) * comb(2, 2-2*j) for j in range(2)))
