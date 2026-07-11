#!/usr/bin/env python3
# Probe the GROUPED orbit decomposition of the worst period^2:
#   ||eta_b||^2 = |mu_n| + Re(eta_{-2b}) + 2 * sum_{zeta in H} Re(eta_{b(zeta-1)})
# where the involution zeta->zeta^{-1} on mu_n\{1} has the unique fixed point zeta=-1 (n even),
# contributing the real singleton b((-1)-1) = -2b, and H is a transversal of {zeta,zeta^{-1}}
# pairs on mu_n\{1,-1}, each pair contributing 2*Re(eta_{b(zeta-1)}).
# Equivalently the transversal-free real-sum split:
#   sum_{zeta in mu_n\{1}} Re(eta_{b(zeta-1)}) = Re(eta_{-2b}) + 2*sum_{H} Re(eta_{b(zeta-1)}).
# PROPER thin mu_n ONLY (m=(p-1)/n >= 4), n=2^a even, NEVER n=q-1. Incl Fermat-shaped primes.
import cmath, math, sympy

def setup(p, n):
    def primroot(g, p):
        for q in sympy.primefactors(p - 1):
            if pow(g, (p - 1) // q, p) == 1:
                return False
        return True
    g = 2
    while not primroot(g, p):
        g += 1
    base = pow(g, (p - 1) // n, p)
    S = []
    x = 1
    for _ in range(n):
        S.append(x)
        x = x * base % p
    return S

def eta(p, S, b):
    return sum(cmath.exp(2j * math.pi * ((b * x) % p) / p) for x in S)

cases = []
for n in [8, 16, 32, 64]:
    c = 0
    for k in range(2, 300000):
        p = k * n + 1
        if sympy.isprime(p) and (p - 1) // n >= 4:
            cases.append((p, n))
            c += 1
            if c >= 2:
                break

print("=== grouped orbit decomposition (proper thin mu_n, even n) ===")
maxerr = 0.0
for p, n in cases:
    S = setup(p, n)
    Sset = set(S)
    inv = {x: pow(x, p - 2, p) for x in S}
    # worst b over full sweep
    b = max(range(1, p), key=lambda bb: abs(eta(p, S, bb)))
    lhs = abs(eta(p, S, b)) ** 2
    full = sum(eta(p, S, (b * ((z - 1) % p)) % p).real for z in S if z != 1)
    neg1 = (-1) % p
    has_neg1 = neg1 in Sset
    singleton = eta(p, S, (b * ((neg1 - 1) % p)) % p).real if has_neg1 else 0.0
    seen = set()
    H = []
    for z in S:
        if z == 1 or z == neg1 or z in seen:
            continue
        H.append(z)
        seen.add(z)
        seen.add(inv[z])
    half = 2 * sum(eta(p, S, (b * ((z - 1) % p)) % p).real for z in H)
    grouped = singleton + half
    err1 = abs(full - grouped)
    err2 = abs(lhs - (n + grouped))
    maxerr = max(maxerr, err1, err2)
    print(f"p={p} n={n} m={(p-1)//n} b={b} |H|={len(H)} neg1_in={has_neg1} "
          f"err(full=grouped)={err1:.2e} err(lhs)={err2:.2e}")

# CONTROL (rule 3): random same-size thin set should NOT satisfy the involution split
import random
print("--- control: random thin set (NOT a subgroup) ---")
random.seed(7)
p, n = cases[0]
T = random.sample(range(1, p), n)
Tset = set(T)
b = max(range(1, p), key=lambda bb: abs(eta(p, T, bb)))
full_c = sum(eta(p, T, (b * ((z - 1) % p)) % p).real for z in T if z != 1)
# there is no group inverse; "pairing" by modular inverse is meaningless -> expect large mismatch
inv = {x: pow(x, p - 2, p) for x in T}
neg1 = (-1) % p
has_neg1 = neg1 in Tset
singleton = eta(p, T, (b * ((neg1 - 1) % p)) % p).real if has_neg1 else 0.0
seen = set(); H = []
for z in T:
    if z == 1 or z == neg1 or z in seen: continue
    if inv[z] in Tset:
        H.append(z); seen.add(z); seen.add(inv[z])
    else:
        H.append(z); seen.add(z)
half = 2 * sum(eta(p, T, (b * ((z - 1) % p)) % p).real for z in H)
ctrl_err = abs(full_c - (singleton + half))
print(f"random thin: err(full=grouped) = {ctrl_err:.3e}  (expect large -> thinness-essential)")

print(f"MAX SUBGROUP ERR = {maxerr:.2e} -> {'PASS' if maxerr < 1e-9 else 'FAIL'}")
