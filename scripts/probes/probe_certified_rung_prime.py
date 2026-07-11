#!/usr/bin/env python3
"""probe_certified_rung_prime.py — generator/cross-check for CertifiedRungPrime.lean (#371).

Verifies (exact arithmetic, deterministic):
  C1  P = 65581*2^64 + 1 is prime (deterministic Miller-Rabin, valid < 3.3e24),
      h = 65581 is prime, P > 2^80 = 32^16 (the pin's hp threshold), 32 | P-1.
  C2  Lucas certificate with witness 3: 3^(P-1) = 1, 3^((P-1)/2) != 1,
      3^((P-1)/65581) != 1 (the only prime cofactors of P-1 = h*2^64 are {2, h}).
  C3  the squaring chains replayed exactly as the Lean file's literals:
      t_k = 3^(2^k), x = 3^h via h = 2^16+2^5+2^3+2^2+1, u_k = x^(2^k);
      u_64 = 1, u_63 != 1, t_64 != 1.
  C4  g = 3^((P-1)/32) = u_59 = 350966889535864008599609, g^16 != 1, g^32 = 1
      (order exactly 32).
  C5  the four rung bands at mu = 5: C(32,r)/r < 2^r*C(16,r) for r = 7,8,9,10,
      with the exact edge values 480836, 1314787, 3116533, 6451224; r = 11 closed.
  C6  beyond-Johnson: r^2 < (r-1)*32 for r = 7..10.

Exit 0 iff all checks pass.
"""
import sys
from math import comb

P = 65581 * 2**64 + 1
H = 65581
G = 350966889535864008599609
FAIL = 0


def check(name, ok):
    global FAIL
    print(("  OK   " if ok else "  FAIL ") + name)
    if not ok:
        FAIL = 1


def is_prime(n):
    if n < 2:
        return False
    for p in [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37]:
        if n % p == 0:
            return n == p
    d, s = n - 1, 0
    while d % 2 == 0:
        d //= 2
        s += 1
    for a in [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37]:
        x = pow(a, d, n)
        if x in (1, n - 1):
            continue
        for _ in range(s - 1):
            x = x * x % n
            if x == n - 1:
                break
        else:
            return False
    return True


# C1
check("P prime", is_prime(P))
check("h prime", is_prime(H))
check("P > 32^16", P > 32**16)
check("32 | P-1", (P - 1) % 32 == 0)

# C2
check("3^(P-1) = 1", pow(3, P - 1, P) == 1)
check("3^((P-1)/2) != 1", pow(3, (P - 1) // 2, P) != 1)
check("3^((P-1)/h) != 1", pow(3, (P - 1) // H, P) != 1)

# C3 chains
t = [3]
for k in range(64):
    t.append(t[-1] * t[-1] % P)
x = t[16] * t[5] % P * t[3] % P * t[2] % P * 3 % P
check("x = 3^h (binary decomposition)", x == pow(3, H, P))
check("h binary = 2^16+2^5+2^3+2^2+1", 2**16 + 2**5 + 2**3 + 2**2 + 1 == H)
u = [x]
for k in range(64):
    u.append(u[-1] * u[-1] % P)
check("u_64 = 1", u[64] == 1)
check("u_63 != 1", u[63] != 1)
check("t_64 != 1", t[64] != 1)

# C4
check("g = u_59", u[59] == G)
check("g = 3^((P-1)/32)", pow(3, (P - 1) // 32, P) == G)
check("g^16 != 1", pow(G, 16, P) != 1)
check("g^32 = 1", pow(G, 32, P) == 1)

# C5
edges = {7: 480836, 8: 1314787, 9: 3116533, 10: 6451224}
for r, e in edges.items():
    check(f"edge r={r}: C(32,{r})//{r} = {e}", comb(32, r) // r == e)
    check(f"band r={r}: {e} < 2^{r}*C(16,{r}) = {2**r * comb(16, r)}",
          e < 2**r * comb(16, r))
check("band r=11 closed", comb(32, 11) // 11 >= 2**11 * comb(16, 11))

# C6
for r in edges:
    check(f"beyond Johnson r={r}: {r * r} < {(r - 1) * 32}", r * r < (r - 1) * 32)

sys.exit(FAIL)
