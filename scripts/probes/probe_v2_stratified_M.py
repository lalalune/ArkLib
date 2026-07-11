import math, sys
# Decisive probe: is the char-p sup-norm M(n) GATED by v2(p-1)?
# Measure c = M(n)/sqrt(n * ln m) stratified by v2(p-1), at beta~4.
# Hypothesis (from stalled W1/W7 agents): c stays below the envelope-break threshold ~1.243
# at v2=mu (minimal, the generic prize prime) but exceeds it at v2>mu (extra-structured).
THRESH = 1.243
def isprime(z):
    if z < 2: return False
    for q in [2,3,5,7,11,13,17,19,23,29,31,37]:
        if z % q == 0: return z == q
    d = z-1; r = 0
    while d % 2 == 0: d //= 2; r += 1
    for a in [2,3,5,7,11,13,17,19,23,29,31,37]:
        x = pow(a, d, z)
        if x in (1, z-1): continue
        ok = False
        for _ in range(r-1):
            x = x*x % z
            if x == z-1: ok = True; break
        if not ok: return False
    return True
def v2(z):
    c = 0
    while z % 2 == 0: z //= 2; c += 1
    return c
def prroot(p):
    f = []; m = p-1; dd = 2
    while dd*dd <= m:
        if m % dd == 0:
            f.append(dd)
            while m % dd == 0: m //= dd
        dd += 1
    if m > 1: f.append(m)
    for g in range(2, p):
        if all(pow(g, (p-1)//x, p) != 1 for x in f): return g
def Mexact(n, p):
    g = prroot(p); zeta = pow(g, (p-1)//n, p)
    D = [pow(zeta, i, p) for i in range(n)]
    m = (p-1)//n
    tp = 2*math.pi/p
    best = 0.0; gj = 1
    for j in range(m):
        re = im = 0.0
        for x in D:
            ang = ((gj*x) % p) * tp
            re += math.cos(ang); im += math.sin(ang)
        mag = math.hypot(re, im)
        if mag > best: best = mag
        gj = (gj*g) % p
    return best, m

print(f"{'n':>4} {'v2':>4} {'p':>12} {'beta':>5} {'M':>9} {'c=M/sqrt(n ln m)':>16}")
for mu in [4, 5, 6]:
    n = 2**mu
    lo = n**4
    strata = {}           # v2 -> list of (p, c)
    p = (lo | 1)
    hi = lo + 4*(n**4)     # scan a window of ~4*n^4
    PER = 3               # primes per v2 stratum
    while p < hi:
        if (p-1) % n == 0 and isprime(p):
            vv = v2(p-1)
            strata.setdefault(vv, [])
            if len(strata[vv]) < PER:
                M, m = Mexact(n, p)
                lm = math.log(m)
                c = M / math.sqrt(n*lm)
                strata[vv].append((p, c))
                beta = math.log(p)/math.log(n)
                flag = "  <-- EXCEEDS 1.243" if c > THRESH else ""
                print(f"{n:>4} {vv:>4} {p:>12} {beta:>5.2f} {M:>9.2f} {c:>16.4f}{flag}", flush=True)
        p += 2
    print(f"  --- n={n} (mu={mu}) summary: c by v2 stratum ---")
    for vv in sorted(strata):
        cs = [c for _, c in strata[vv]]
        if cs:
            tag = " (=mu, MINIMAL = generic prize prime)" if vv == mu else ""
            print(f"     v2={vv}{tag}: max c={max(cs):.4f}  mean={sum(cs)/len(cs):.4f}  n_primes={len(cs)}")
    print(flush=True)
print("DONE")
