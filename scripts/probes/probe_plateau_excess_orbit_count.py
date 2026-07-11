"""
probe_plateau_excess_orbit_count — DECISIVE structural measurement for #444 angle 5.

THE QUESTION: at the d=2 IMPRIMITIVE binding direction, the plateau excess |P|
(the extra mu_2-invariant rungs created when level n doubles to 2n) — is it a
FIXED CONSTANT (=> w(2n)=w(n)+c ADDITIVE => PRIZE HOLDS) or does it DOUBLE
(=> MULTIPLICATIVE => PRIZE FAILS)?

The angle-5 claim under test (the Lean target _Close27): at the binding the
clique-orbit count O=1 (single orbit of size S=n/2 + the gamma=0 fixed point),
so |P| <= a fixed constant independent of n.

STRATEGY (no infeasible n=32 brute force): measure, at a FIXED d=2 direction,
at the binding radius, EXACTLY two structural quantities at n=8 and n=16:
  (1) O = number of distinct gamma-ORBITS in the bad set under <omega^{b-a}>,
  (2) |bad gamma set| at the binding rung,
and decompose D = S*O + (fixed-point contribution). The angle predicts O=1
constant. If O=1 at BOTH n=8 and n=16 (d=2 binder), the orbit-count is
constant => the per-level excess |P| is bounded by S_P*1 with S_P the NEW
invariant-orbit size — and we check whether the NUMBER of new orbits (not their
size) is constant. That number is the additive constant c.

Exact char-0 over C (cyclotomic), p == 1 mod n, p >> n^4, multiple primes.
"""
import math
from itertools import combinations


def is_prime(x):
    if x < 2:
        return False
    for q in (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37):
        if x % q == 0:
            return x == q
    d = x - 1
    s = 0
    while d % 2 == 0:
        d //= 2
        s += 1
    for a in (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37):
        y = pow(a, d, x)
        if y in (1, x - 1):
            continue
        for _ in range(s - 1):
            y = y * y % x
            if y == x - 1:
                break
        else:
            return False
    return True


def prime_1_mod_n(n, start_mult=1):
    p = max(n**4, start_mult * n**4)
    p += (1 - p) % n
    if p < n**4:
        p += n
    while not is_prime(p):
        p += n
    return p


def primitive_root(p):
    fs = []
    x = p - 1
    d = 2
    while d * d <= x:
        if x % d == 0:
            fs.append(d)
            while x % d == 0:
                x //= d
        d += 1
    if x > 1:
        fs.append(x)
    for g in range(2, p):
        if all(pow(g, (p - 1) // q, p) != 1 for q in fs):
            return g
    return 0


def ddk(vals, nodes, k, p):
    vs = list(vals[:k + 1])
    for j in range(1, k + 1):
        for i in range(k, j - 1, -1):
            inv = pow((nodes[i] - nodes[i - j]) % p, p - 2, p)
            vs[i] = (vs[i] - vs[i - 1]) * inv % p
    return vs[k]


def in_rs(vals, nodes, k, p):
    s = len(nodes)
    if s <= k:
        return True
    for st in range(s - k):
        if ddk(vals[st:st + k + 1], nodes[st:st + k + 1], k, p) != 0:
            return False
    return True


def bad_gammas(a, b, mu, k, p, s):
    """Set of gamma s.t. x^a + gamma x^b agrees with deg<k on >= s pts of mu.
       Returns set of gamma values (or None if HEAVY/saturated)."""
    n = len(mu)
    mua = [pow(v, a, p) for v in mu]
    mub = [pow(v, b, p) for v in mu]
    gammas = set()
    for comb in combinations(range(n), s):
        nodes = [mu[i] for i in comb]
        u0 = [mua[i] for i in comb]
        u1 = [mub[i] for i in comb]
        if in_rs(u1, nodes, k, p):
            if in_rs(u0, nodes, k, p):
                return None  # HEAVY
            continue
        a1 = ddk(u1[:k + 1], nodes[:k + 1], k, p)
        a0 = ddk(u0[:k + 1], nodes[:k + 1], k, p)
        if a1 == 0:
            continue
        gm = (-a0) * pow(a1, p - 2, p) % p
        full = [(u0[i] + gm * u1[i]) % p for i in range(s)]
        if in_rs(full, nodes, k, p):
            gammas.add(gm)
    return gammas


def orbit_decompose(gammas, b, a, mu, p):
    """Decompose gamma-set into orbits under multiplication by w^{b-a}.
       The action on alpha=gamma is alpha -> alpha * w^{b-a} (Chai-Fan).
       Returns (num_orbits, num_fixedpoints(gamma=0), orbit_sizes)."""
    n = len(mu)
    d = (b - a) % n
    w = mu[1]  # primitive n-th root = generator omega
    mult = pow(w, d, p)  # omega^{b-a}
    gs = set(gammas)
    orbits = []
    seen = set()
    fixed0 = 0
    for g in list(gs):
        if g in seen:
            continue
        if g == 0:
            fixed0 += 1
            seen.add(0)
            orbits.append([0])
            continue
        orb = []
        cur = g
        while cur not in seen:
            seen.add(cur)
            orb.append(cur)
            cur = cur * mult % p
            if cur not in gs:
                break
        orbits.append(orb)
    nonzero_orbits = [o for o in orbits if not (len(o) == 1 and o[0] == 0)]
    return len(nonzero_orbits), fixed0, [len(o) for o in nonzero_orbits]


def find_d2_binder(n, k, p):
    """Find the worst far direction with gcd(b-a,n)=2 at the binding radius.
       Returns (s_binding, (a,b), bad_gamma_count, orbit_data)."""
    g = primitive_root(p)
    h = pow(g, (p - 1) // n, p)
    mu = [pow(h, i, p) for i in range(n)]
    budget = n
    # find the global binding s* first
    for s in range(k + 2, n):
        # among d=2 directions, find the worst at this radius
        best = -1
        bestdir = None
        bestg = None
        for b in range(k, s):
            for a in range(k, n):
                if a == b:
                    continue
                if math.gcd((b - a) % n, n) != 2:
                    continue
                gam = bad_gammas(a, b, mu, k, p, s)
                if gam is None:
                    continue  # heavy
                if len(gam) > best:
                    best = len(gam)
                    bestdir = (a, b)
                    bestg = gam
        if bestdir is None:
            continue
        if best <= budget:
            od = orbit_decompose(bestg, bestdir[1], bestdir[0], mu, p)
            return s, bestdir, best, od, mu
        # also report the PRE-binding (s-1) rung structure
    return None, None, None, None, mu


def run():
    print("PLATEAU EXCESS ORBIT COUNT at the d=2 imprimitive binder (exact char-0):\n")
    print(f"{'n':>4} {'k':>3} {'p':>10} {'s*':>4} {'binder':>10} {'|bad|':>6} "
          f"{'#orbits':>8} {'#fix0':>6} {'orbsizes':>12}")
    data = {}
    for (n, k) in [(8, 2), (16, 4)]:
        row = []
        for sm in (1, 2, 3):
            p = prime_1_mod_n(n, start_mult=sm)
            s, bd, bc, od, mu = find_d2_binder(n, k, p)
            if s is None:
                print(f"{n:>4} {k:>3} {p:>10}   no d=2 binder found")
                continue
            no, nf, osz = od
            print(f"{n:>4} {k:>3} {p:>10} {s:>4} {str(bd):>10} {bc:>6} "
                  f"{no:>8} {nf:>6} {str(osz):>12}")
            row.append((s, bd, bc, no, nf, tuple(osz)))
        data[n] = row
    print()
    print("STRUCTURE AT THE BINDING (D = S*O + fixed-point):")
    for n in (8, 16):
        if not data[n]:
            continue
        # p-independence check
        cores = set((r[3], r[4]) for r in data[n])  # (#orbits, #fix0)
        print(f"  n={n}: (#orbits,#fix0) across primes = {cores}  "
              f"{'p-INDEPENDENT' if len(cores)==1 else 'p-DEPENDENT(!)'}")
    print()
    if data[8] and data[16]:
        o8 = data[8][0][3]
        o16 = data[16][0][3]
        print(f"  ORBIT COUNT O: n=8 -> {o8}, n=16 -> {o16}")
        if o8 == o16 == 1:
            print("  => O=1 CONSTANT at the binding (single orbit). Angle-5 premise HOLDS:")
            print("     D = S*1 + fix0, so the bad-count at the binder is governed by ONE orbit.")
            print("     The plateau excess |P| = number of NEW invariant orbits per level.")
        elif o16 == 2 * o8:
            print("  => O DOUBLES => MULTIPLICATIVE warning.")
        else:
            print(f"  => O: {o8} -> {o16}, neither constant-1 nor doubling cleanly.")


if __name__ == "__main__":
    run()
