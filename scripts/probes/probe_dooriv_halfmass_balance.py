#!/usr/bin/env python3
"""
Door-(iv) probe: half-mass BALANCE at the worst frequency.

The prize is now localized to bounding H(n) = max_b (‖A‖ + ‖B‖), where for the
2-power subgroup mu_n < F_p^*, eta_b = Sum_{y in mu_n} e_p(b*y) = A + B with
A = Sum over the index-2 subgroup mu_{n/2}, B = Sum over the nontrivial coset.

Known (in-tree): coherence rho(b*) = 1 at the worst b (period halves are real,
same-sign), so |eta_{b*}| = ‖A‖ + ‖B‖ = H exactly at b*.

UNMEASURED arithmetic statistic: the BALANCE between ‖A‖ and ‖B‖ at the worst b.
If worst-b forces ‖A‖ ≈ ‖B‖ (balanced), the dyadic descent is symmetric and the
two halves carry equal burden. If worst-b is systematically IMBALANCED, that is an
exploitable arithmetic structure (one half dominates -> reduce to a thinner sum).

We measure, over proper subgroups in the prize regime (p >> n^3, structured primes,
NEVER n=q-1):
  - balance ratio r(b) = min(‖A‖,‖B‖)/max(‖A‖,‖B‖) in [0,1]; 1 = perfectly balanced.
  - r at the GLOBAL worst-b b* = argmax_b ‖eta_b‖ (full F_p^* scan for small n).
  - distribution of r over all b, and whether worst-b r is special (extreme/typical).
HONESTY: full-group scan for n=16 (global argmax), sampled for larger n (flagged).
"""
import cmath, math

def find_prime(lo):
    n = lo | 1
    while True:
        if all(n % d for d in range(3, int(n**0.5)+1, 2)) and n > 2:
            return n
        n += 2

def primitive_root(p):
    # find a generator of F_p^*
    from sympy import factorint
    phi = p - 1
    facs = list(factorint(phi).keys())
    for g in range(2, p):
        if all(pow(g, phi//q, p) != 1 for q in facs):
            return g
    raise RuntimeError

def subgroup_mu(p, g, n):
    # mu_n = unique subgroup of order n (n | p-1). generator = g^((p-1)/n).
    assert (p-1) % n == 0
    h = pow(g, (p-1)//n, p)
    elts = []
    x = 1
    for _ in range(n):
        elts.append(x)
        x = (x*h) % p
    return elts, h

def eta_halves(p, b, mu_n, h_n, n):
    # A = sum over mu_{n/2} = <h_n^2>; B = sum over coset h_n * mu_{n/2}
    half = n//2
    h2 = (h_n*h_n) % p
    A = 0j; B = 0j
    x = 1
    for _ in range(half):
        A += cmath.exp(2j*math.pi*(b*x % p)/p)
        x = (x*h2) % p
    # coset rep h_n
    x = h_n % p
    for _ in range(half):
        B += cmath.exp(2j*math.pi*(b*x % p)/p)
        x = (x*h2) % p
    return A, B

def run(n, beta, full_scan_limit=70000):
    p_target = max(int(n**beta), n**3 * 4)
    # need n | p-1
    base = ((p_target // n) + 1) * n + 1
    while True:
        p = base
        if p > 2 and all(p % d for d in range(3, int(p**0.5)+1, 2)):
            break
        base += n
    g = primitive_root(p)
    mu_n, h_n = subgroup_mu(p, g, n)
    full = (p-1) <= full_scan_limit
    if full:
        bs = range(1, p)
    else:
        # structured + random sample, flagged
        import random
        random.seed(12345)
        bs = sorted(set([1, g, h_n] + [random.randint(1, p-1) for _ in range(4000)]))
    best_mag = -1; best_b = None; best_r = None
    rs = []
    for b in bs:
        A, B = eta_halves(p, b, mu_n, h_n, n)
        mag = abs(A+B)
        nA, nB = abs(A), abs(B)
        mx = max(nA, nB); mn = min(nA, nB)
        r = (mn/mx) if mx > 1e-12 else 1.0
        rs.append(r)
        if mag > best_mag:
            best_mag = mag; best_b = b; best_r = r
    rs.sort()
    med = rs[len(rs)//2]
    mean = sum(rs)/len(rs)
    # percentile of worst-b's balance ratio among all r
    below = sum(1 for x in rs if x <= best_r)
    pct = below/len(rs)
    print(f"n={n:4d} beta={beta} p={p} {'FULL' if full else 'SAMPLED'} |b|={len(rs)}")
    print(f"   worst-b={best_b} ‖eta‖={best_mag:.4f} (√n={n**0.5:.3f})  balance r(b*)={best_r:.4f}  percentile={pct:.3f}")
    print(f"   r over all b: mean={mean:.4f} median={med:.4f} min={rs[0]:.4f} max={rs[-1]:.4f}")
    return best_r, mean, med

if __name__ == "__main__":
    print("=== Door-(iv) half-mass BALANCE at worst frequency (prize regime) ===")
    for n, beta in [(16,4),(16,5),(32,4),(32,5),(64,4)]:
        run(n, beta)
        print()
