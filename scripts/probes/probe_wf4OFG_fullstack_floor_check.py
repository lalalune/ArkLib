"""
wf-OFG (#444): Is `epsMCA(C, δbind) <= eps*` actually TRUE at the Johnson-side
binding radius δbind = (n-s*)/n with s* = n/2 - 1?

epsMCA = (1/q) * max over ALL stacks (u0,u1) of #{γ : mcaEvent fires}.
Budget = q*eps* ~ n. So `epsMCA <= eps*` holds  <=>  max bad-scalar count <= n.

The over-det/far stratum gives the p-independent combinatorial count I(n)~1.37e-3 n^4
(I(16)=89 etc) -- but THAT is a count of (s-subset, γ) witness incidences, NOT the
bad-γ count #{γ}. The bad-γ COUNT per stack is what enters epsMCA. This probe measures
the TRUE max bad-γ count over a broad direction family (monomial + multi-term + near-code)
at radius δbind, to decide whether the floor `epsMCA <= eps*` is reachable at δbind, or
whether some stack (the under-det / BGK stratum) already blows the bad-γ count past budget.

We work char-0 (one big prime p == 1 mod n, p >> n) so the count is p-independent for the
over-det part. mcaEvent ~ line-explainability (far) ; for near directions we directly count
γ with the line within radius (Hamming) of the code, the honest mcaEvent over-approximation.
"""
import itertools, sys
from collections import Counter

def isprime(x):
    if x < 2: return False
    d = x-1; s = 0
    while d % 2 == 0: d //= 2; s += 1
    for a in [2,3,5,7,11,13,17,19,23,29,31,37]:
        if a % x == 0: continue
        y = pow(a, d, x)
        if y in (1, x-1): continue
        ok = False
        for _ in range(s-1):
            y = y*y % x
            if y == x-1: ok = True; break
        if not ok: return False
    return True

def find_prime(n, lo):
    p = lo - lo % n + 1
    while True:
        if p > lo and isprime(p): return p
        p += n

def fac(x):
    f = {}; dd = 2
    while dd*dd <= x:
        while x % dd == 0: f[dd] = f.get(dd,0)+1; x //= dd
        dd += 1
    if x > 1: f[x] = f.get(x,0)+1
    return f

def proot(p):
    fs = set(fac(p-1))
    for g in range(2, p):
        if all(pow(g,(p-1)//q,p) != 1 for q in fs): return g

def setup(n, p):
    g = proot(p); h = pow(g,(p-1)//n,p); return [pow(h,i,p) for i in range(n)]

def baddir_count(u0vals, u1vals, mu, n, k, p, r):
    """#{γ in F_p : line u0+γ u1 agrees with RS[k] on some (n-r)-subset}.
    This is the line-explainability bad-γ COUNT (= mcaEvent count for far directions,
    an over-approx in general). u0vals,u1vals are length-n eval vectors over μ_n."""
    s = n - r
    inv = lambda z: pow(z, p-2, p)
    def ddk(vals, pts):
        vs = list(vals[:k+1]); xs = pts[:k+1]
        for j in range(1, k+1):
            for i in range(k, j-1, -1):
                vs[i] = (vs[i]-vs[i-1]) * inv((xs[i]-xs[i-j]) % p) % p
        return vs[k]
    def in_RS(vals, pts):
        if len(pts) <= k: return True
        for st in range(len(pts)-k):
            if ddk(vals[st:st+k+1], pts[st:st+k+1]) != 0: return False
        return True
    gam = set()
    for R in itertools.combinations(range(n), s):
        pts = [mu[i] for i in R]; a0 = [u0vals[i] for i in R]; a1 = [u1vals[i] for i in R]
        if in_RS(a1, pts):
            if in_RS(a0, pts): return p   # whole-line: "all of F" branch (degenerate)
            continue
        d0 = ddk(a0, pts); d1 = ddk(a1, pts)
        if d1 % p == 0: continue
        gm = (-d0 * inv(d1)) % p
        if in_RS([(a0[i]+gm*a1[i]) % p for i in range(s)], pts): gam.add(gm)
    return len(gam)

def run(n, mu_pow_count_only=False):
    mu_exp = n
    p = find_prime(n, n**4 * 4)   # char-0: p >> n^3
    mu = setup(n, p)
    k = n // 4                    # rho = 1/4
    sstar = n // 2 - 1            # binding over-det s*
    r = n - sstar                 # δbind = r/n  ... wait, radius = s = far-agreement size n-r
    # binding radius: agreement size s* => witness size s* => r = n - s*. δbind=(n-s*)/n.
    rad_r = n - sstar
    budget = n                    # q*eps* ~ n
    print(f"=== n={n}, p={p} (char-0, p>n^4), k={k}, s*={sstar}, "
          f"witness-size s*={sstar}, δbind=(n-s*)/n={(n-sstar)}/{n}={(n-sstar)/n:.4f}, budget~n={budget}")
    sys.stdout.write("  sweeping directions...\n"); sys.stdout.flush()

    best = 0; arg = None; dist = Counter()
    # family 1: pure monomials u0=x^a, u1=x^b  (over-det far)
    cnt = 0
    for a in range(0, n):
        for b in range(0, n):
            if a == b: continue
            u0 = [pow(x, a, p) for x in mu]; u1 = [pow(x, b, p) for x in mu]
            I = baddir_count(u0, u1, mu, n, k, p, rad_r)
            if I < p:
                dist[I] += 1
                if I > best: best = I; arg = ("mono", a, b)
            cnt += 1
    # family 2: u1 = monomial, u0 = SHORT codeword-perturbed (near-code u0) -- probes whether
    # a near-code u0 raises the bad count. u0 = small * x^a where 'small' < distance.
    # family 3: 2-term directions u1 = x^b + c x^b'  (multi-term far)
    for b in range(0, n):
        for bp in range(0, n):
            if b == bp: continue
            for c in (1, 2, p-1):
                u1 = [(pow(x, b, p) + c*pow(x, bp, p)) % p for x in mu]
                # pair with a monomial offset
                u0 = [pow(x, (b+1) % n, p) for x in mu]
                I = baddir_count(u0, u1, mu, n, k, p, rad_r)
                if I < p:
                    dist[I] += 1
                    if I > best: best = I; arg = ("2term", b, bp, c)
    print(f"  MAX bad-γ COUNT over swept directions = {best} at {arg}")
    print(f"  budget (q*eps* ~ n) = {budget}   =>  epsMCA<=eps* at δbind "
          f"{'HOLDS (max<=budget)' if best <= budget else 'FAILS on this family (max>budget)'}")
    top = dict(sorted(dist.items())[-8:])
    print(f"  top bad-γ-count distribution (count:freq): {top}")
    return best, budget

if __name__ == "__main__":
    for n in (8, 16, 24):
        run(n)
    print("DONE")
