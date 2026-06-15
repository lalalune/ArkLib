"""
wf407 / T24-pfree, PART 2+3 : the bridge and the defect re-entry.

Arrow (CharSumMomentDeepWall.charSum_le_of_moment):
    B^{2r} <= sum_b |eta_b|^{2r} = q * E_r(F_q)        (*)   [char-p energy, exact]
so  B <= (q * E_r(F_q))^{1/2r}.
The p-free object is E_r^inf (char-0); E_r(F_q) = E_r^inf + D_r(q), D_r(q) >= 0.

FAST: E_r(F_q) = sum_v (count of r-fold root sums == v)^2.  Build by repeated
convolution over Z/p.  E_r^inf via exact roots-of-unity-vanishing counting.
"""

import itertools, math, cmath
from collections import Counter

def prime_factors(n):
    fs = set(); d = 2
    while d * d <= n:
        while n % d == 0:
            fs.add(d); n //= d
        d += 1
    if n > 1: fs.add(n)
    return fs

def find_primes_with_roots(n, count, lo=8):
    out = []; p = max(lo, n + 1); p += (1 - p) % n
    if p <= 1: p += n
    while len(out) < count:
        if p > 1 and all(p % d for d in range(2, int(p**0.5) + 1)):
            out.append(p)
        p += n
    return out

def roots_mod_p(n, p):
    pf = prime_factors(n)
    for cand in range(2, p):
        if pow(cand, n, p) == 1 and all(pow(cand, n // q, p) != 1 for q in pf):
            return [pow(cand, i, p) for i in range(n)]
    raise RuntimeError("no gen")

def E_r_char_p_fast(n, r, p, roots):
    # distribution of sums of r roots, mod p, via convolution
    dist = Counter({0: 1})
    for _ in range(r):
        nd = Counter()
        for v, c in dist.items():
            for x in roots:
                nd[(v + x) % p] += c
        dist = nd
    return sum(c * c for c in dist.values())

def char0_zero_pow2(plus, minus, n):
    h = n // 2; coeff = [0] * h
    for a in plus:  coeff[a % h] += (-1 if (a // h) % 2 else 1)
    for b in minus: coeff[b % h] -= (-1 if (b // h) % 2 else 1)
    return all(c == 0 for c in coeff)

def E_r_char0(n, r):
    cnt = 0
    for xs in itertools.product(range(n), repeat=r):
        for ys in itertools.product(range(n), repeat=r):
            if char0_zero_pow2(xs, ys, n): cnt += 1
    return cnt

def true_B(n, p, roots):
    best = 0.0; w = 2 * math.pi / p
    for b in range(1, p):
        s = sum(cmath.exp(1j * w * ((b * x) % p)) for x in roots)
        if abs(s) > best: best = abs(s)
    return best

print("=" * 80)
print("PART 2: char-p DEFECT D_r(q) = E_r(F_q) - E_r^inf   (0 = p-free value holds)")
print("=" * 80)
for n in [4, 8]:
    print(f"\n##### n = {n} #####", flush=True)
    rmax = 4 if n == 4 else 3   # n=8,r=4 char-0 enum is 8^8; cap at r=3 (8^6, fast)
    Einf = {r: E_r_char0(n, r) for r in range(1, rmax + 1)}
    primes = find_primes_with_roots(n, 8, lo=8)
    print(f"  primes (p=1 mod {n}): {primes}")
    print(f"  E_r^inf: " + "  ".join(f"r{r}={Einf[r]}" for r in range(1, rmax + 1)))
    print("  p".ljust(8) + "log_n p".ljust(9)
          + "".join(f"D_{r}".ljust(11) for r in range(1, rmax + 1)))
    for p in primes:
        roots = roots_mod_p(n, p)
        row = f"  {p}".ljust(8) + f"{math.log(p, n):.2f}".ljust(9)
        for r in range(1, rmax + 1):
            Ep = E_r_char_p_fast(n, r, p, roots)
            D = Ep - Einf[r]
            mark = "*" if Ep > 2 * Einf[r] else (" " if D == 0 else ".")
            row += (f"{D}{mark}").ljust(11)
        print(row)
    print("   legend: 0' '=p-free holds, '.'=defect<main, '*'=(PU) E_p>2E_inf FAILS")

print()
print("=" * 80)
print("PART 3: bridge test --- is the p-free bound B_pf=(q E_r^inf)^{1/2r} VALID?")
print("=" * 80)
print("  if B_pf < B_true at some (p,r) the p-free bound is FALSE -> no p-uniform bridge")
for n in [8]:
    primes = find_primes_with_roots(n, 6, lo=8)
    Einf = {r: E_r_char0(n, r) for r in range(1, 4)}  # r<=3
    print(f" n={n}:")
    print("  p".ljust(7) + "B_true".ljust(9) + "r".ljust(3)
          + "B_pf".ljust(11) + "B_cp".ljust(11) + "verdict")
    for p in primes:
        roots = roots_mod_p(n, p)
        Bt = true_B(n, p, roots)
        for r in range(1, 4):
            Ep = E_r_char_p_fast(n, r, p, roots)
            Bpf = (p * Einf[r]) ** (1.0 / (2 * r))
            Bcp = (p * Ep) ** (1.0 / (2 * r))
            flag = "p-free BND FALSE" if Bpf < Bt - 1e-9 else "(holds)"
            print(f"  {p}".ljust(7) + f"{Bt:.3f}".ljust(9) + f"{r}".ljust(3)
                  + f"{Bpf:.4f}".ljust(11) + f"{Bcp:.4f}".ljust(11) + flag)
        print()
