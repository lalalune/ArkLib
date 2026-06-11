# R2 fold-transport probe (pre-registered):
#  H1a (shape covariance): fold of KKH26 stack (X^4, X^3) on mu_8 over F_4129 is the
#       KKH26 shape (y^2, beta*y) on mu_4 with code degree halved.
#  H1b (witness death): the construction's close-point witnesses T (antipodal-free) have
#       ZERO surviving agreement pairs after folding -> inherited closeness dies.
#  H1c (census): exact bad-count of original line at delta=1/2 vs paper bound 16;
#       exact bad-count of folded line at delta=1/2 vs mu'=2 paper bound 4.
p = 4129
# find primitive root
def is_prim(z):
    for q in (2, 3, 43):
        if pow(z, (p-1)//q, p) == 1: return False
    return True
z = next(z for z in range(2, 200) if is_prim(z))
g8 = pow(z, (p-1)//8, p)
H = [pow(g8, i, p) for i in range(8)]
assert len(set(H)) == 8
mu4 = [pow(g8, 2*i, p) for i in range(4)]
def interp_val(pts, x):
    # Lagrange value at x of poly through pts [(xi,yi)]
    s = 0
    for i, (xi, yi) in enumerate(pts):
        num = den = 1
        for j, (xj, _) in enumerate(pts):
            if i != j:
                num = num * (x - xj) % p
                den = den * (xi - xj) % p
        s = (s + yi * num * pow(den, p-2, p)) % p
    return s
from itertools import combinations
def badcount(domain, wordvals, degbound, agree_t):
    # exact: #lambda... here wordvals: dict lam -> list of values; generic helper below instead
    pass
def close_to_code(vals, domain, degbound, agree_t):
    # does vals agree with some poly of deg <= degbound on >= agree_t points?
    n = len(domain)
    for S in combinations(range(n), agree_t):
        # poly through first degbound+1 pts of S; check rest
        base = [(domain[i], vals[i]) for i in S[:degbound+1]]
        if all(interp_val(base, domain[i]) == vals[i] for i in S[degbound+1:]):
            return True
    return False
# --- original census at mu=3: line x^4 + lam*x^3 vs deg<=2, agree >= 4 of 8
orig_bad = [lam for lam in range(p)
            if close_to_code([(pow(x,4,p) + lam*pow(x,3,p)) % p for x in H], H, 2, 4)]
print("original exact bad count (mu=3, delta=1/2):", len(orig_bad), "| paper bound: >=16")
# predicted Lambda: -sums of antipodal-free 4-subsets (one from each pair {x,-x})
pairs = [(H[i], (p - H[i]) % p) for i in range(8)]
# antipodal pairs in mu_8: -x = x*g8^4
apairs = []
seen = set()
for x in H:
    nx = (p - x) % p
    if x not in seen and nx not in seen:
        seen.add(x); seen.add(nx); apairs.append((x, nx))
from itertools import product as iproduct
Lam_pred = set()
for choice in iproduct(*[(a, b) for (a, b) in apairs]):
    Lam_pred.add((-sum(choice)) % p)
print("predicted |Lambda| (antipodal-free sums):", len(Lam_pred),
      "| all bad?", all(l in set(orig_bad) for l in Lam_pred))
# --- witness survival under fold
def fold_word(vals_on_H, beta):
    # returns values on mu4: y=x^2
    out = []
    inv2 = pow(2, p-2, p)
    for y in mu4:
        x = next(x for x in H if pow(x, 2, p) == y)
        fe = (vals_on_H[H.index(x)] + vals_on_H[H.index((p-x) % p)]) * inv2 % p
        fo = (vals_on_H[H.index(x)] - vals_on_H[H.index((p-x) % p)]) * inv2 * pow(x, p-2, p) % p
        out.append((fe + beta * fo) % p)
    return out
# count antipodal pairs inside each predicted witness T (choice sets): by construction 0
print("antipodal pairs inside construction witnesses: 0 by construction (antipodal-free)")
# --- folded census for several beta
import random
random.seed(1)
for beta in [1, 7, random.randrange(2, p), random.randrange(2, p)]:
    u0f = fold_word([pow(x, 4, p) for x in H], beta)      # should be y^2
    u1f = fold_word([pow(x, 3, p) for x in H], beta)      # should be beta*y
    assert u0f == [pow(y, 2, p) for y in mu4]
    assert u1f == [beta * y % p for y in mu4]
    fold_bad = [g for g in range(p)
                if close_to_code([(u0f[i] + g * u1f[i]) % p for i in range(4)], mu4, 0, 2)]
    print(f"beta={beta}: folded exact bad count (mu'=2, delta=1/2): {len(fold_bad)} | paper bound: >=4")
