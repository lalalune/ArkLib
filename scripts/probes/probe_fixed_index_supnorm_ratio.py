#!/usr/bin/env python3
# DECISIVE REGIME PROBE (2026-06-14).
#
# Question this settles: the prize bound is  M(n,p) := max_{t≠0} |Σ_{x∈μ_n} e_p(tx)|
#                                                       ≤ C·√(n·log(p/n)).
# Write m = (p-1)/n = index of μ_n in F_p*  (so log(p/n) ≈ log m).
# The PRIZE REGIME fixes q≈n·2^128, i.e. m≈2^128 CONSTANT while n→∞ (the FFT domain grows).
# This is a FIXED-INDEX / positive-proportion (n=Θ(p)) family — NOT the thin n=p^{1/4}
# family that lands on the BGK/Paley wall. The two families predict different behaviour of
#
#         R(n,m) := M(n,p) / √(n·ln m).
#
#   * If R stays bounded by a small constant as BOTH n grows (fixed m) AND m grows (fixed n),
#     the prize bound is the right shape and the open content is purely the worst-case constant.
#   * The growth of R *in m at fixed n* vs *in n at fixed m* tells us which variable is hard:
#     fixed-index hardness lives in m (effective Gauss-sum equidistribution), thin-subgroup
#     hardness lives in n (BGK). The prize holds m≈const and sends n→∞.
#
# Efficient: η_t depends only on the coset t·μ_n, so there are exactly m distinct period
# values. Compute one sum of n terms per coset ⇒ total work m·n = p-1 (feasible to p~10^7).
import sympy, cmath, math

def musub(n, p):
    g = sympy.primitive_root(p)
    h = pow(g, (p - 1) // n, p)
    return [pow(h, j, p) for j in range(n)]

def supnorm(n, p):
    """max over t≠0 of |Σ_{x∈μ_n} e_p(t x)|, using one rep per coset of μ_n."""
    G = musub(n, p)
    g = sympy.primitive_root(p)
    m = (p - 1) // n
    w = 2 * math.pi / p
    mx = 0.0
    Gset = G  # the subgroup as a list
    # coset reps: g^c for c = 0..m-1 ; η_{g^c} = Σ_{x∈μ_n} e_p(g^c x)
    rep = 1
    for c in range(m):
        s = 0j
        for x in Gset:
            s += cmath.exp(1j * w * ((rep * x) % p))
        a = abs(s)
        if a > mx:
            mx = a
        rep = (rep * g) % p
    return mx

def find_prime(n, mtarget):
    """smallest prime p = n*m + 1 with m >= mtarget (so index ~ mtarget, μ_n ⊂ F_p*)."""
    m = mtarget
    while True:
        p = n * m + 1
        if sympy.isprime(p):
            return p, m
        m += 1

print("R(n,m) = M / sqrt(n*ln m).  m = index = (p-1)/n.")
print(f"{'n':>6}{'m(index)':>10}{'p':>10}{'M':>9}{'M/sqrt(n)':>11}{'sqrt(ln m)':>11}{'R':>8}")
print("-- A) FIXED INDEX m≈const, n grows (THE PRIZE FAMILY) --")
for mtarget in [16, 64]:
    for mu in range(4, 12):           # n = 2^mu
        n = 2 ** mu
        if n * mtarget > 4_000_000:    # work cap m*n = p-1
            break
        p, m = find_prime(n, mtarget)
        if m > 2 * mtarget:            # skip if no prime kept index near target
            continue
        M = supnorm(n, p)
        R = M / math.sqrt(n * math.log(m))
        print(f"{n:>6}{m:>10}{p:>10}{M:>9.2f}{M/math.sqrt(n):>11.3f}{math.sqrt(math.log(m)):>11.3f}{R:>8.3f}")
print("-- B) THIN: n fixed, index m grows (n=p^{1/k}, k shrinks → BGK family) --")
n = 256
for mtarget in [8, 32, 128, 512, 2048, 8192]:
    if n * mtarget > 4_000_000:
        break
    p, m = find_prime(n, mtarget)
    M = supnorm(n, p)
    R = M / math.sqrt(n * math.log(m))
    k = math.log(p) / math.log(n)
    print(f"{n:>6}{m:>10}{p:>10}{M:>9.2f}{M/math.sqrt(n):>11.3f}{math.sqrt(math.log(m)):>11.3f}{R:>8.3f}   (n=p^(1/{k:.2f}))")
