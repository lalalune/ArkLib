#!/usr/bin/env python3
"""Fast focused half-Johnson reality check: q-invariance + delta* placement.
Only cheap instances (n-k <= 2 over a prime sweep; plus n=5,k=2 / n=6,k=3 single primes)."""
from itertools import product, combinations
from math import sqrt


def smooth_domain(p, n):
    assert (p - 1) % n == 0, (p, n)
    for cand in range(2, p):
        g = pow(cand, (p - 1) // n, p)
        if all(pow(g, d, p) != 1 for d in range(1, n)) and pow(g, n, p) == 1:
            return [pow(g, i, p) for i in range(n)]
    raise ValueError("no order-n element")


def rref(mat, p):
    m = [r[:] for r in mat]; rows = len(m); cols = len(m[0]) if m else 0; piv = []; r = 0
    for c in range(cols):
        pr = next((i for i in range(r, rows) if m[i][c] % p), None)
        if pr is None: continue
        m[r], m[pr] = m[pr], m[r]; inv = pow(m[r][c], p - 2, p)
        m[r] = [(x * inv) % p for x in m[r]]
        for i in range(rows):
            if i != r and m[i][c] % p:
                f = m[i][c]; m[i] = [(a - f * b) % p for a, b in zip(m[i], m[r])]
        piv.append(c); r += 1
        if r == rows: break
    return m[:r], piv


def nullspace(mat, p):
    red, piv = rref(mat, p); cols = len(mat[0])
    free = [c for c in range(cols) if c not in piv]; basis = []
    for f in free:
        v = [0] * cols; v[f] = 1
        for r, c in enumerate(piv): v[c] = (-red[r][f]) % p
        basis.append(v)
    return basis


def solve_particular(H, s, p):
    rows = [H[i] + [s[i]] for i in range(len(H))]; red, piv = rref(rows, p)
    n = len(H[0]); w = [0] * n
    for r, c in enumerate(piv):
        if c == n: raise ValueError("inconsistent")
        w[c] = red[r][n]
    return w


def ext_from(word, S, xs, k, p):
    if len(S) <= k: return True
    base, rest = S[:k], S[k:]
    for j in rest:
        val = 0
        for a in base:
            num, den = 1, 1
            for b in base:
                if b != a:
                    num = num * ((xs[j] - xs[b]) % p) % p
                    den = den * ((xs[a] - xs[b]) % p) % p
            val = (val + word[a] * num * pow(den, p - 2, p)) % p
        if val != word[j] % p: return False
    return True


def eps_profile(p, n, k):
    xs = smooth_domain(p, n)
    G = [[pow(x, j, p) for x in xs] for j in range(k)]
    H = nullspace(G, p); assert len(H) == n - k
    subsets = []
    for size in range(k + 1, n + 1): subsets.extend(combinations(range(n), size))
    syndromes = list(product(range(p), repeat=n - k))
    ext_mask = {}
    for s in syndromes:
        w = solve_particular(H, list(s), p); mask = 0
        for bit, S in enumerate(subsets):
            if ext_from(w, list(S), xs, k, p): mask |= 1 << bit
        ext_mask[s] = mask
    adm = {}
    for m in range(k + 1, n + 1):
        am = 0
        for bit, S in enumerate(subsets):
            if len(S) >= m: am |= 1 << bit
        adm[m] = am
    best = {m: 0 for m in adm}
    nz = [s for s in syndromes if any(s)]
    for s0 in syndromes:
        e0 = ext_mask[s0]
        for s1 in nz:
            notjoint = ~(e0 & ext_mask[s1])
            bms = []
            for g in range(p):
                line = tuple((a + g * b) % p for a, b in zip(s0, s1))
                bms.append(ext_mask[line] & notjoint)
            for m, am in adm.items():
                cnt = sum(1 for bm in bms if bm & am)
                if cnt > best[m]: best[m] = cnt
    return best


def L(n, k):
    rho = k / n
    return dict(rho=rho, halfJ=(1 - sqrt(rho)) / 2, J=1 - sqrt(rho), cap=1 - rho)


def zone(d, lm):
    if d < 0: return "none"
    if d < lm['halfJ'] - 1e-9: return "<halfJ"
    if d < lm['J'] - 1e-9: return "(halfJ,J)"
    if d < lm['cap'] - 1e-9: return "[J,cap)"
    return ">=cap"


print("=" * 74)
print("M1  Q-INVARIANCE of worst-case incidence (bad-scalar count) at fixed (n,k)")
print("=" * 74)
# cheap families: n=4,k=2 (rho=1/2, n-k=2); n=5,k=2 (rho=2/5, n-k=3, small primes only)
for tag, n, k, primes in [("rho=1/2 n=4 k=2", 4, 2, [5, 13, 17, 29, 37, 41]),
                          ("rho=2/5 n=5 k=2", 5, 2, [11])]:
    lm = L(n, k)
    print(f"\n{tag}: rho={lm['rho']:.3f} halfJ={lm['halfJ']:.3f} J={lm['J']:.3f} cap={lm['cap']:.3f}", flush=True)
    profs = {p: eps_profile(p, n, k) for p in primes}
    ms = sorted(next(iter(profs.values())), reverse=True)
    print("   delta  zone        " + "".join(f"  q={p:<3}" for p in primes))
    for m in ms:
        d = 1 - m / n
        cs = [profs[p][m] for p in primes]
        inv = "==" if len(set(cs)) == 1 else "!!"
        print(f"   {d:.3f}  {zone(d, lm):<10}" + "".join(f"{c:>6}" for c in cs) + f"   [{inv}]")
    allinv = all(len(set(profs[p][m] for p in primes)) == 1 for m in ms)
    print(f"   => incidence integers {'ARE Q-INVARIANT (eps_mca = const/q -> 0)' if allinv else 'VARY with q'}")

print("\n" + "=" * 74)
print("M2  delta* placement vs half-Johnson, for several eps* targets (single primes)")
print("=" * 74)
for n, k, p in [(4, 2, 17), (5, 2, 11), (6, 3, 13), (6, 3, 7)]:
    lm = L(n, k)
    best = eps_profile(p, n, k)
    rows = sorted(((1 - m / n, best[m]) for m in best), reverse=True)
    print(f"\nRS[F{p},n={n},k={k}] rho={lm['rho']:.3f} halfJ={lm['halfJ']:.3f} "
          f"J={lm['J']:.3f} cap={lm['cap']:.3f}")
    for d, b in rows:
        print(f"   delta={d:.3f}  incidence={b:>2}  eps_mca={b}/{p}={b/p:.4f}  {zone(d, lm)}")
    print("   delta*(eps*) at this q:")
    for lab, eps in [("1/q", 1 / p), ("2/q", 2 / p), ("3/q", 3 / p), ("(q-1)/q", (p - 1) / p)]:
        good = [d for d, b in rows if b / p <= eps + 1e-12]
        ds = max(good) if good else -1.0
        print(f"      eps*={lab:<8}-> delta*={ds:>6.3f}  ({zone(ds, lm)})")

print("\nDONE")
