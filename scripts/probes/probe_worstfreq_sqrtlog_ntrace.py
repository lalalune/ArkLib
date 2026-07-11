#!/usr/bin/env python3
"""
ISOLATE THE n-GROWTH of the constant C in |S_b*| <= C*sqrt(n*log(p/n)).
Hold the regime fixed (p ~ n^3, a middle regime, feasible to a=7) and trace
C(n) = R / sqrt(log(p/n)) as n = 8,16,32,64,128. If C(n) is bounded/flat => the
sqrt(n log) law holds with an absolute constant => conjecture-consistent at worst freq.
If C(n) creeps up => the worst frequency has an n-dependent excess => FALSE signal.

Tractability: full b-sweep is O(p*n). At p~n^3: a=7 -> p~2e6, n=128 -> 2.5e8 ops, ~minutes.
We cap the sweep: |S_b| is constant on mu_n-cosets, so we only need ONE b per coset of mu_n
in F_p^*. There are (p-1)/n cosets. We pick coset reps by iterating b and skipping any b
that is h^j * (smaller b) — cheaply: a b is a "new coset rep" iff b is the minimum of its
mu_n-coset. We test that by checking b <= b*u mod p for all u in mu_n (n checks). Net cost
~ (p-1)/n cosets * n (rep test) + (p-1)/n * n (the sum) = O(p) for the sums. Good.
"""
import math

def setup(a, target_p):
    n = 2 ** a
    p = max(target_p, n + 1)
    while True:
        p += 1
        if (p - 1) % n:
            continue
        if all(p % d for d in range(2, int(p ** 0.5) + 1)):
            break
    g = None
    for c in range(2, p):
        o = 1; y = c % p
        while y != 1:
            y = (y * c) % p; o += 1
            if o > p: break
        if o == p - 1:
            g = c; break
    h = pow(g, (p - 1) // n, p)
    H = [pow(h, i, p) for i in range(n)]
    return p, H, set(H)

def worst_mag_coset(p, H, Hset, n):
    w = 2 * math.pi / p
    best = -1.0
    seen = bytearray(p)  # mark coset members already covered
    for b in range(1, p):
        if seen[b]:
            continue
        # mark the whole mu_n-coset of b, and compute |S_b| once
        coset = [(b * u) % p for u in H]
        for cb in coset:
            seen[cb] = 1
        sr = si = 0.0
        for x in H:
            ang = w * ((b * x) % p)
            sr += math.cos(ang); si += math.sin(ang)
        m = sr * sr + si * si
        if m > best:
            best = m
    return math.sqrt(best)

print("n-trace of the worst-freq constant C(n) = R / sqrt(log(p/n)),  p ~ n^3")
print(f"{'a':>2} {'n':>5} {'p':>10} {'|S_b*|':>9} {'R':>7} {'sqrt(log)':>9} {'C(n)':>7}")
print("-" * 56)
for a in [3, 4, 5, 6, 7]:
    n = 2 ** a
    p, H, Hset = setup(a, int(n ** 3))
    mag = worst_mag_coset(p, H, Hset, n)
    R = mag / math.sqrt(n)
    lg = math.sqrt(math.log(p / n))
    print(f"{a:>2} {n:>5} {p:>10} {mag:>9.3f} {R:>7.3f} {lg:>9.3f} {R/lg:>7.3f}")

print()
print("C(n) column: BOUNDED/FLAT => sqrt(n log(p/n)) law with absolute constant")
print("=> worst-frequency character sum obeys the BGK/MRSS shape => prize floor reachable,")
print("conjecture-consistent. GROWING C(n) => worst freq beats the bound => FALSE signal.")
