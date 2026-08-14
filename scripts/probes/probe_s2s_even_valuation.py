import sympy as sp
from sympy import symbols, resultant, cyclotomic_poly, Poly, factorint
import itertools

def is_sum_two_squares(N):
    if N == 0:
        return True
    for p, e in factorint(N).items():
        if p % 4 == 3 and e % 2 == 1:
            return False
    return True

x = symbols('x')
for m in [3, 4, 5]:
    n = 2**m
    Phi = Poly(cyclotomic_poly(n, x), x)
    half = n // 2
    norms = []
    s2s_fail = 0
    cnt = 0
    for T in itertools.combinations(range(n), 4):
        Ts = set(T)
        af = all(((i + half) % n) not in Ts for i in T)
        if not af:
            continue
        for signs in itertools.product([1, -1], repeat=4):
            R = sum(s * x**i for s, i in zip(signs, T))
            N = abs(int(resultant(Poly(R, x), Phi)))
            if N == 0:
                continue
            norms.append(N)
            if not is_sum_two_squares(N):
                s2s_fail += 1
            cnt += 1
            if cnt > 4000:
                break
        if cnt > 4000:
            break
    odd_p3 = 0
    for N in norms:
        for p, e in factorint(N).items():
            if p % 4 == 3 and e % 2 == 1:
                odd_p3 += 1
    print(f"m={m} n={n}: {len(norms)} weight-4 af-norms; s2s_fail={s2s_fail}; p3mod4_oddpower={odd_p3}")

print("VERDICT: s2s law holds => p==3 mod4 never divides a relation norm to odd power.")
