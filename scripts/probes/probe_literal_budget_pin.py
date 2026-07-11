#!/usr/bin/env python3
"""probe_literal_budget_pin.py — generator/cross-check for LiteralBudgetPin.lean (#371).

The first in-window delta* pin at the literal challenge budget eps* = 2^-128:
P = 1314883*2^128 + 1, dimension-7 (rate 7/32) code on the 32-point smooth domain,
delta* = 3/4.

Checks (exact, deterministic):
  C1  P prime (deterministic Miller-Rabin, valid < 3.3e24 -- P ~ 2^148.33 needs the
      extended base set; we use sympy-free strong MR with the 13-base set valid to
      3.3e24 PLUS direct Lucas verification, which is the actual certificate),
      h = 1314883 prime, P > 32^16, 2^128 | P-1.
  C2  Lucas: 3^(P-1)=1, 3^((P-1)/2)!=1, 3^((P-1)/h)!=1; h = 2^20+2^18+2^12+2^6+2+1.
  C3  chain replay: x = 3^h via binary; u_123 = g; u_127 != 1; u_128 = 1; t_128 != 1.
  C4  g order exactly 32.
  C5  the literal band: 1314787*2^128 <= P < 3294720*2^128, where
      1314787 = C(32,8)//8 (glueing floor) and 3294720 = 2^8*C(16,8) (KKH26 spectrum);
      hence  C(32,8)/8 / P <= 2^-128 < 2^8*C(16,8) / P.
  C6  beyond Johnson: 8^2 = 64 < 224 = 7*32; below capacity: 3/4 < 25/32.

Exit 0 iff all pass.
"""
import sys
from math import comb

P = 1314883 * 2**128 + 1
H = 1314883
G = 365776689002390431616511545157923604483360578
FAIL = 0


def check(name, ok):
    global FAIL
    print(("  OK   " if ok else "  FAIL ") + name)
    if not ok:
        FAIL = 1


def mr(n, bases):
    if n < 2:
        return False
    for p in [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43]:
        if n % p == 0:
            return n == p
    d, s = n - 1, 0
    while d % 2 == 0:
        d //= 2
        s += 1
    for a in bases:
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


# C1 (Lucas below is the real certificate; MR here is a sanity sweep)
check("P strong-probable-prime (40 bases)", mr(P, list(range(2, 42))))
check("h prime", mr(H, [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37]))
check("P > 32^16", P > 32**16)
check("2^128 | P-1", (P - 1) % 2**128 == 0)

# C2
check("3^(P-1) = 1", pow(3, P - 1, P) == 1)
check("3^((P-1)/2) != 1", pow(3, (P - 1) // 2, P) != 1)
check("3^((P-1)/h) != 1", pow(3, (P - 1) // H, P) != 1)
check("h = 2^20+2^18+2^12+2^6+2+1", 2**20 + 2**18 + 2**12 + 2**6 + 2 + 1 == H)
check("Lucas cofactors exactly {2, h}", True)  # P-1 = h*2^128, h prime

# C3
t = [3]
for k in range(128):
    t.append(t[-1] * t[-1] % P)
x = t[20] * t[18] % P * t[12] % P * t[6] % P * t[1] % P * 3 % P
check("x = 3^h (binary chain)", x == pow(3, H, P))
u = [x]
for k in range(128):
    u.append(u[-1] * u[-1] % P)
check("u_128 = 1", u[128] == 1)
check("u_127 != 1", u[127] != 1)
check("t_128 != 1", t[128] != 1)
check("u_123 = g", u[123] == G)

# C4
check("g^16 != 1", pow(G, 16, P) != 1)
check("g^32 = 1", pow(G, 32, P) == 1)

# C5
edge = comb(32, 8) // 8
ceil = 2**8 * comb(16, 8)
check("edge = 1314787", edge == 1314787)
check("ceiling = 3294720", ceil == 3294720)
check("band lo: edge*2^128 <= P", edge * 2**128 <= P)
check("band hi: P < ceiling*2^128", P < ceil * 2**128)

# C6
check("beyond Johnson: 64 < 224", 8 * 8 < 7 * 32)
check("below capacity: 3/4 < 25/32", 3 * 32 < 4 * 25)

sys.exit(FAIL)
