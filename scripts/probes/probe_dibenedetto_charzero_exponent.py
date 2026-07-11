# Probe: the EXACT char-0 (cyclotomic) additive energies of mu_n (n=2^a thin dyadic)
# E2 = 3n^2 - 3n, E3 = 15n^3 - 45n^2 + 40n  (PROVEN: B4_closed/B6_eq_E3, recursion-solved)
# Verify: (1) E_k <= c_k n^k all n>=1 with c_2=3, c_3=15 (so t_2<=2, t_3<=3 as exponent bounds)
#         (2) E_k >= n^k floor (Cauchy-Schwarz t_2>=2, diagonal t_3>=3) so exponents are TIGHT
#         (3) the saving evaluated at realised exponents t_k(n)=log E_k/log n stays <= 1/24
#         (4) char-p sanity: directly count E_2 of the REAL thin subgroup mu_n in F_p at a
#             PROPER subgroup p ~ n^4, p == 1 mod n, p >> n^3, NEVER n=q-1, vs char-0 closed form
from math import log
from sympy import isprime, primitive_root
from collections import Counter

def E2_cz(n): return 3*n**2 - 3*n
def E3_cz(n): return 15*n**3 - 45*n**2 + 40*n

print("== char-0 closed-form energies, upper/lower envelope ==")
for a in range(2, 22):
    n = 2**a
    e2, e3 = E2_cz(n), E3_cz(n)
    assert n**2 <= e2 <= 3*n**2, (n, e2)
    assert n**3 <= e3 <= 15*n**3, (n, e3)
    t2 = log(e2)/log(n); t3 = log(e3)/log(n)
    sav = (10 - 2*t3 - t2/2)/72
    if a <= 6 or a % 5 == 0:
        print(f"n=2^{a:<2}={n:<9} E2={e2:<14} E3={e3:<16} t2={t2:.5f} t3={t3:.5f} sav={sav:.6f} (<=1/24? {sav<=1/24})")

print("\n== exponent limits (t2->2, t3->3 from above? below?) ==")
for a in [10, 15, 20, 25, 30]:
    n = 2**a
    t2 = log(E2_cz(n))/log(n); t3 = log(E3_cz(n))/log(n)
    print(f"n=2^{a}: t2={t2:.6f}  t3={t3:.6f}")

def thin_subgroup(n, p):
    g = primitive_root(p)
    e = (p-1)//n
    h = pow(g, e, p)
    return [pow(h, k, p) for k in range(n)]

def E2_charp(S, p):
    c = Counter((a+b) % p for a in S for b in S)
    return sum(v*v for v in c.values())

print("\n== char-p E2 vs char-0 closed form (proper thin mu_n, p~n^4, p==1 mod n, NEVER n=q-1) ==")
for a in [3, 4, 5]:
    n = 2**a
    target = n**4
    p = target | 1
    while not (isprime(p) and (p-1) % n == 0):
        p += 2
    S = thin_subgroup(n, p)
    assert len(set(S)) == n
    e2p = E2_charp(S, p)
    print(f"n={n} p={p} (p%n={p%n}, p/n^3={p/n**3:.1f}) charp E2={e2p} char0 E2={E2_cz(n)} match={e2p==E2_cz(n)}")
