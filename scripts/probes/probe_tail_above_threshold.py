# REFINED PROBE: the subgaussian_max_le proof only invokes the tail Prop at s in (s*, v) for v>s*.
# So the I031 max-bridge only NEEDS the tail Prop for s >= s* = sqrt(2C log m).
# Q: with C=n, is the tail Prop TRUE for all s >= s*? (above threshold, count must be 0 by pointwise)
# This tests whether the WEAKENED tail Prop (restricted to s>=s*) is EXACTLY the pointwise M<=s* bound.
import cmath, math

def primitive_root(p):
    if p == 2:
        return 1
    fac = set(); pm = p - 1; d = 2
    while d * d <= pm:
        if pm % d == 0:
            fac.add(d)
            while pm % d == 0:
                pm //= d
        d += 1
    if pm > 1:
        fac.add(pm)
    for g in range(2, p):
        if all(pow(g, (p - 1) // f, p) != 1 for f in fac):
            return g

def eta_norms(p, n):
    g = primitive_root(p); m = (p - 1) // n; h = pow(g, m, p)
    mun = []; x = 1
    for _ in range(n):
        mun.append(x); x = (x * h) % p
    w = cmath.exp(2j * math.pi / p)
    return [abs(sum(w ** ((b * y) % p) for y in mun)) for b in range(1, p)], m

print(f"{'p':>6} {'n':>3} {'m':>5} {'M':>8} {'s*=root(2nlnm)':>14} {'tail_OK_s>=s*':>13} {'M<=s*':>7}")
for (p, n) in [(17, 4), (41, 4), (73, 8), (97, 8), (193, 8), (337, 16),
               (521, 8), (257, 16), (641, 16), (769, 16), (4129, 16), (12289, 16), (40961, 16)]:
    if (p - 1) % n != 0 or (p - 1) // n < 2:
        continue
    norms, m = eta_norms(p, n); M = max(norms); C = n
    sstar = math.sqrt(2 * C * math.log(m))
    ok = True
    for k in range(0, 200):
        s = sstar + 0.05 * k
        cnt = sum(1 for v in norms if s < v)
        rhs = m * math.exp(-(s ** 2) / (2 * C))
        if cnt > rhs + 1e-9:
            ok = False; break
    print(f"{p:>6} {n:>3} {m:>5} {M:>8.3f} {sstar:>14.3f} {str(ok):>13} {str(M <= sstar + 1e-9):>7}")
