# Adversarial check (#444): verify energy_logConvex E_r^2 <= E_{r-1}*E_{r+1} on REAL mu_n
# additive energies (NOT the spectral side) -- the claim must hold as stated on the integer counts.
# E_r(G) = #{(v,w) in (Fin r -> G)^2 : sum v = sum w}, computed via freq convolution.
from sympy import primitive_root


def mu_n(p, n):
    g = primitive_root(p)
    h = pow(g, (p - 1) // n, p)
    s = []
    x = 1
    for _ in range(n):
        s.append(x)
        x = (x * h) % p
    return s


def freq_table(sub, p, r):
    # freq_r[d] = # r-tuples from sub summing to d mod p
    cur = {0: 1}
    for _ in range(r):
        nxt = {}
        for d, c in cur.items():
            for s in sub:
                e = (d + s) % p
                nxt[e] = nxt.get(e, 0) + c
        cur = nxt
    return cur


def energy(sub, p, r):
    if r == 0:
        return 1  # E_0 = #{(): () } = 1 (empty tuple, sum=0)
    f = freq_table(sub, p, r)
    return sum(c * c for c in f.values())


print("energy_logConvex: E_r^2 <= E_{r-1}*E_{r+1}  (r>=1)")
fails = 0
total = 0
for (p, n) in [(193, 8), (257, 16), (769, 16), (1153, 32)]:
    if (p - 1) % n != 0:
        continue
    sub = mu_n(p, n)
    E = [energy(sub, p, r) for r in range(0, 8)]
    for r in range(1, 7):
        lhs = E[r] * E[r]
        rhs = E[r - 1] * E[r + 1]
        ok = lhs <= rhs
        total += 1
        if not ok:
            fails += 1
        print(f"  n={n} p={p} r={r}: E_r^2={lhs}  E_{{r-1}}E_{{r+1}}={rhs}  ok={ok}")
print(f"RESULT: {fails} fails / {total}")
