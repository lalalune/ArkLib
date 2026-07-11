from math import gcd

def orbit(gen, n):
    seen = set(); orbs = []
    for s in range(n):
        if s in seen:
            continue
        o = []; x = s
        while x not in seen:
            seen.add(x); o.append(x); x = (x + gen) % n
        orbs.append(sorted(o))
    return orbs

def test(n, shift):
    d = gcd(shift, n); S = n // d
    orbs = orbit(shift, n)
    B = set(orbs[0]) | {0}
    n2 = 2 * n
    dbl = {2 * i for i in B}
    has_rung = (S != 0) and ((n // 2) % S == 0)
    if has_rung and d % 2 == 0:
        odd = {(2 * i + 1) % n2 for i in orbs[0]}
    else:
        odd = set()
    Bp = dbl | odd
    evens = {j for j in Bp if j % 2 == 0}
    odds = {j for j in Bp if j % 2 == 1}
    half_even = {j // 2 for j in evens}
    c1 = (evens & odds == set())
    c2 = (evens | odds == Bp)
    c3 = (len(Bp) == len(evens) + len(odds))
    c4 = (half_even == B)
    c5 = (dbl == evens)
    primitive = (d == 1)
    c6 = (primitive == (len(odds) == 0))
    ok = all([c1, c2, c3, c4, c5, c6])
    return ok, d, S, len(odds), primitive, has_rung

print("n     shift  d    S     |Odd|  primitive  rung?  PASS")
fails = 0; total = 0
for mu in range(2, 9):
    n = 2 ** mu
    cand = [1, 3, 2, 4, 6, n // 2, n // 4]
    for shift in cand:
        if shift <= 0 or shift >= n:
            continue
        ok, d, S, lod, prim, rung = test(n, shift)
        total += 1
        if not ok:
            fails += 1
        print(f"{n:<5} {shift:<6} {d:<4} {S:<5} {lod:<6} {str(prim):<10} {str(rung):<6} {ok}")
print(f"\n{total-fails}/{total} PASS, {fails} fails")
