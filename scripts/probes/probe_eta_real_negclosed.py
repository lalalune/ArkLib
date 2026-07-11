import cmath, math
import sympy

# Probe: if -1 in G (negation-closed subgroup), is eta_b = sum_{x in G} e_p(b x) REAL for all b?
# Prize regime: PROPER thin 2-power subgroups mu_n < F_p*, p >> n^3, NEVER n=q-1.

def find_prime(n, beta):
    target = int(n ** beta)
    p = target | 1
    while True:
        if sympy.isprime(p) and (p - 1) % n == 0:
            return p
        p += 2

def eta(b, G, p):
    return sum(cmath.exp(2j * math.pi * (b * x % p) / p) for x in G)

maxim = 0.0
checks = 0
neg_one_cases = 0
for a in range(2, 7):              # n = 2^a, a=2..6
    n = 2 ** a
    for beta in [2.0, 3.2, 4.0]:
        p = find_prime(n, beta)
        if (p - 1) // n < 2:       # ensure PROPER (n != q-1)
            continue
        g = sympy.primitive_root(p)
        h = pow(g, (p - 1) // n, p)   # generator of mu_n
        G = sorted({pow(h, k, p) for k in range(n)})
        assert len(G) == n, (n, len(G))
        assert G[0] == 1
        neg1 = (p - 1)             # -1 mod p
        has_neg1 = (neg1 in G)
        if has_neg1:
            neg_one_cases += 1
        worst_im = 0.0
        for b in range(1, min(p, 40)):
            e = eta(b, G, p)
            worst_im = max(worst_im, abs(e.imag))
        maxim = max(maxim, worst_im)
        checks += 1
        flag = "REAL" if worst_im < 1e-9 else f"IM={worst_im:.2e}"
        print(f"n={n:3d} beta={beta} p={p} m=(p-1)/n={(p-1)//n} -1in G:{has_neg1} -> {flag}")
print(f"\n{checks} cases, {neg_one_cases} with -1 in G, max |Im eta_b| = {maxim:.3e}")
