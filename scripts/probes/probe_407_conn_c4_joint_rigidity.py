"""
#407 CONNECTION C4 — bootstrap the PROVEN e2-rigidity (E2VanishRigidityModP.lean) into a
TOWER of e_j-rigidity thresholds, and test whether the JOINT {e_1=e_3=0} system (the
count-lane spurious-config constraints) has a SMALLER / lower-max bad-prime set than each
individual constraint, dropping toward poly(n).

PROVEN ENGINE (in-tree, axiom-clean):
  e2_extra_solution_threshold : a NEW mod-p e2=0 solution forces p <= (n^2+n)^{n/2}.
  Mechanism: e_2(S)=0 <=> R^(2)_U(zeta)=0 where R^(2)_U(X) = (sum_{i in U} X^i)^2 - sum X^{2i}
  is an INTEGER polynomial; fold to degree < n/2 against Phi_n = X^{n/2}+1; the resultant
  engine `not_isRoot_of_l1On_pow_lt` gives: if R folds to nonzero in char 0 and
  p > (l1mass)^{n/2}, then no mod-p root => threshold = (l1mass)^{n/2} with l1mass <= n^2+n.

GENERALIZATION (this probe, goal a): the SAME fold+resultant argument applies to ANY e_j,
because j! * e_j(S) = R^(j)_U(zeta) for an INTEGER polynomial R^(j)_U(X) (Newton in power
sums p_m(S) = sum_{i in U} X^{m*i}, all integer polys in X):
  R^(1)_U(X) = sum X^i                                        (1! e_1 = p_1)
  R^(2)_U(X) = (sum X^i)^2 - sum X^{2i}                       (2! e_2 = p_1^2 - p_2)
  R^(3)_U(X) = (sum X^i)^3 - 3(sum X^i)(sum X^{2i}) + 2 sum X^{3i}   (3! e_3)
  R^(4)_U(X) = p1^4 - 6 p1^2 p2 + 3 p2^2 + 8 p1 p3 - 6 p4     (4! e_4)
Each has POLY(|U|) l1 mass (sum of |coeffs|), so the per-e_j rigidity threshold is
(l1mass_j)^{n/2}, the SAME species as the proven e_2 bound. We verify R^(j)(zeta)=j! e_j
and measure l1 masses + thresholds.

Goal (b): the count-lane spurious config is antipodal-free U with e_1=e_3=0 simultaneously.
We compute the bad-prime set for {e_1=0}, {e_3=0}, and JOINT {e_1=0 AND e_3=0}, and test
whether the joint MAX bad prime is strictly smaller (toward poly(n)).

Goal (c): assemble the tower / state provable-vs-open.

Everything is exact integer arithmetic in Z[zeta_n] = Z[X]/(X^{n/2}+1) (n=2^k); we VERIFY
each identity numerically against complex evaluation before asserting.
"""
import itertools, math
from functools import reduce
from sympy import primerange, primitive_root

# ----------------- exact Z[zeta_n] arithmetic, n = 2^k, zeta^{n/2} = -1 -----------------
def zeta_pow(e, h):
    e %= (2*h)
    v = [0]*h
    if e < h: v[e] = 1
    else: v[e-h] = -1
    return v

def zadd(a, b, h): return [a[i]+b[i] for i in range(h)]
def zscale(a, c, h): return [c*a[i] for i in range(h)]

def zmul(a, b, h):
    res = [0]*(2*h)
    for i, ai in enumerate(a):
        if ai == 0: continue
        for jj, bj in enumerate(b):
            if bj == 0: continue
            res[i+jj] += ai*bj
    out = [0]*h
    for d in range(2*h):
        if d < h: out[d] += res[d]
        else: out[d-h] -= res[d]
    return out

def power_sum(U, m, h):
    acc = [0]*h
    for i in U: acc = zadd(acc, zeta_pow(m*i, h), h)
    return acc

# integer relation polynomials j! e_j as elements of Z[zeta] (folded mod X^{h}+1 already)
def Rfold(U, j, h):
    p1 = power_sum(U, 1, h)
    if j == 1:
        return p1
    p2 = power_sum(U, 2, h)
    if j == 2:
        return zadd(zmul(p1, p1, h), zscale(p2, -1, h), h)            # p1^2 - p2
    p3 = power_sum(U, 3, h)
    if j == 3:
        t = zmul(zmul(p1, p1, h), p1, h)                              # p1^3
        t = zadd(t, zscale(zmul(p1, p2, h), -3, h), h)                # -3 p1 p2
        t = zadd(t, zscale(p3, 2, h), h)                              # +2 p3
        return t
    p4 = power_sum(U, 4, h)
    if j == 4:
        p1sq = zmul(p1, p1, h)
        t = zmul(p1sq, p1sq, h)                                       # p1^4
        t = zadd(t, zscale(zmul(p1sq, p2, h), -6, h), h)              # -6 p1^2 p2
        t = zadd(t, zscale(zmul(p2, p2, h), 3, h), h)                 # +3 p2^2
        t = zadd(t, zscale(zmul(p1, p3, h), 8, h), h)                 # +8 p1 p3
        t = zadd(t, zscale(p4, -6, h), h)                             # -6 p4
        return t
    raise ValueError(j)

FACT = {1:1, 2:2, 3:6, 4:24}

def is_zero(v): return all(x == 0 for x in v)
def l1(v): return sum(abs(x) for x in v)

# ----------------- VERIFY R^(j)(zeta) = j! e_j(S) -----------------
def ej_complex(U, j, n):
    zc = complex(math.cos(2*math.pi/n), math.sin(2*math.pi/n))
    roots = [zc**i for i in U]
    return sum(reduce(lambda a, b: a*b, comb, 1) for comb in itertools.combinations(roots, j))

def verify(n, trials=80):
    import random
    random.seed(7)
    h = n//2
    zc = complex(math.cos(2*math.pi/n), math.sin(2*math.pi/n))
    ok = True
    for _ in range(trials):
        w = random.randint(4, n); U = sorted(random.sample(range(n), w))
        for j in (1, 2, 3, 4):
            v = Rfold(U, j, h)
            rv = sum(v[t]*zc**t for t in range(h))
            ejc = ej_complex(U, j, n)
            if abs(rv - FACT[j]*ejc) > 1e-5:
                ok = False
                print(f"  MISMATCH n={n} j={j} U={U}: R={rv} j!ej={FACT[j]*ejc}")
    print(f"[verify] R^(j)(zeta)=j! e_j  (n={n}, {trials} random U, j=1..4): {'OK' if ok else 'FAIL'}")
    return ok

# ----------------- (a) folded l1 masses + thresholds -----------------
def thresholds(n):
    h = n//2
    print(f"\n=== (a) n={n} (h={h}): FOLDED l1 mass of R^(j)_U (max over U) + rigidity threshold (l1)^{h} ===")
    print(f"    proven e_2 bound: l1 <= n^2+n = {n*n+n}; threshold = (n^2+n)^{h}")
    res = {}
    for j in (1, 2, 3, 4):
        maxl1 = 0; argU = None
        wmax = min(n, j+4)
        for w in range(j, wmax+1):
            for U in itertools.combinations(range(n), w):
                m = l1(Rfold(list(U), j, h))
                if m > maxl1: maxl1 = m; argU = U
        # crude analytic bound from coeff-sum (eval at 1) of the |·| split:
        # R^(1): |U|;  R^(2): |U|^2+|U|;  R^(3): |U|^3+3|U|^2+2|U|;  R^(4): |U|^4+6|U|^3+3|U|^2+8|U|^2+6|U|
        nn = n
        crude = {1: nn, 2: nn**2+nn, 3: nn**3+3*nn**2+2*nn,
                 4: nn**4+6*nn**3+3*nn**2+8*nn**2+6*nn}[j]
        res[j] = (maxl1, crude)
        thr = f"{maxl1}^{h}"
        print(f"  e_{j}: measured folded max l1 = {maxl1:6d}   crude poly bound = {crude:8d}   threshold ~ {thr}   argmaxU={argU}")
    return res

# ----------------- bad-prime sets (individual + JOINT) -----------------
def primes_1modn(n, lo, hi):
    return [p for p in primerange(lo, hi) if (p-1) % n == 0]

def gen_mu(n, p):
    g = pow(primitive_root(p), (p-1)//n, p)
    return [pow(g, i, p) for i in range(n)]

def ej_mod_p(U, j, mu, p):
    coeffs = [0]*(len(U)+1); coeffs[0] = 1; deg = 0
    for i in U:
        r = mu[i]
        for d in range(deg, -1, -1):
            coeffs[d+1] = (coeffs[d+1] + coeffs[d]*r) % p
        deg += 1
    return coeffs[j] % p

def char0_zero(U, j, h):
    return is_zero(Rfold(list(U), j, h))

def bad_primes(n, constraints, widths, prime_hi):
    """primes p=1 mod n < prime_hi with a config U (some width) where every e_j (j in
    constraints) vanishes mod p but NOT all vanish over C (spurious)."""
    h = n//2
    bad = {}
    ps = primes_1modn(n, n+1, prime_hi)
    for p in ps:
        mu = gen_mu(n, p)
        hit = None
        for w in widths:
            for U in itertools.combinations(range(n), w):
                if all(ej_mod_p(U, j, mu, p) == 0 for j in constraints):
                    if not all(char0_zero(U, j, h) for j in constraints):
                        hit = U; break
            if hit: break
        if hit: bad[p] = hit
    return sorted(bad.keys()), ps, bad

def joint_vs_individual(n, widths, prime_hi):
    print(f"\n=== (b) n={n}: bad-prime sets, individual vs JOINT, widths={widths}, p<{prime_hi} ===")
    b1, ps, _ = bad_primes(n, (1,), widths, prime_hi)
    b3, _,  _ = bad_primes(n, (3,), widths, prime_hi)
    bJ, _,  detail = bad_primes(n, (1, 3), widths, prime_hi)
    print(f"  #primes(=1 mod {n}) scanned: {len(ps)} (range {n+1}..{prime_hi})")
    print(f"  bad {{e_1=0}}     : {b1}   max={max(b1) if b1 else None}")
    print(f"  bad {{e_3=0}}     : {b3}   max={max(b3) if b3 else None}")
    print(f"  bad {{e_1=e_3=0}} : {bJ}   max={max(bJ) if bJ else None}   <-- JOINT (count-lane)")
    print(f"      joint subset of e1-bad? {set(bJ) <= set(b1)};  of e3-bad? {set(bJ) <= set(b3)}")
    print(f"      Q^2 = n^2 = {n*n};  n^3 = {n**3}")
    for p in bJ:
        print(f"      joint bad p={p}: witness exps U={detail[p]}")
    return b1, b3, bJ

if __name__ == "__main__":
    print("########## VERIFY identities ##########")
    for n in (8, 16):
        verify(n)

    print("\n########## (a) per-e_j folded thresholds ##########")
    for n in (8, 16, 32):
        thresholds(n)

    print("\n########## (b) JOINT vs individual bad-prime sets ##########")
    joint_vs_individual(16, widths=(4, 6, 8), prime_hi=20000)
    joint_vs_individual(32, widths=(4, 6),    prime_hi=8000)
