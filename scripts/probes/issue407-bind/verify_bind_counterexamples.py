from sympy import isprime, primitive_root, primefactors
import math
cases = [
    (32, 14814881, [1, 2, 7, 8, 9, 10, 12, 13, 19, 22, 27]),
    (64, 136085377, [1, 2, 5, 8, 9, 10, 12, 15, 16, 18, 21, 22, 32, 36, 39, 41, 48, 52, 55, 57, 58, 60, 61, 62]),
]
for n, p, S in cases:
    assert isprime(p), "p not prime"
    assert (p - 1) % n == 0, "n does not divide p-1"
    g = primitive_root(p)
    w = pow(g, (p - 1) // n, p)
    assert pow(w, n, p) == 1
    assert all(pow(w, n // q, p) != 1 for q in primefactors(n)), "w not primitive n-th root"
    m = n // 2
    Ss = set(S)
    antipodal = all(((i + m) % n) in Ss for i in S)
    val = sum(pow(w, i, p) for i in S) % p
    any_conj = False
    t_hit = None
    for t in range(1, n):
        if math.gcd(t, n) == 1:
            if sum(pow(w, (i * t) % n, p) for i in S) % p == 0:
                any_conj = True
                t_hit = t
                break
    print(f"n={n} p={p} beta={math.log(p)/math.log(n):.3f} #S={len(S)}")
    print(f"  non-antipodal: {not antipodal}")
    print(f"  Sum_(i in S) w^i mod p = {val}  => vanishes on chosen w: {val==0}")
    print(f"  vanishes on some Galois conjugate w^t: {any_conj} (t={t_hit})")
    print(f"  p>n^3 (thin): {p>n**3};  n|p-1: {(p-1)%n==0}")
    verdict = (not antipodal) and (val == 0 or any_conj) and p > n**3 and (p - 1) % n == 0
    print(f"  >>> VALID (BIND) COUNTEREXAMPLE: {verdict}\n")
