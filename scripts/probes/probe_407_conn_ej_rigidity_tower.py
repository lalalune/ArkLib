"""
#407 CONNECTION C4 — bootstrap the proven e2-rigidity into a TOWER of e_j-rigidity
thresholds and test whether the JOINT {e_1=e_3=0} system has a SMALLER bad-prime set.

Setup (matches E2VanishRigidityModP.lean):
  S = {zeta^i : i in U}, U subset of range(n), n = 2^k, zeta primitive n-th root.
  e_j(S) = j-th elementary symmetric function.
  Over F_p with primitive n-th root g, a config is "e_j-bad" if e_j(S)=0 over F_p
  but NOT over C (a spurious new mod-p solution).

The e2 rigidity engine: e_j(S)=0 <=> an INTEGER polynomial relation R^{(j)}_U(zeta)=0.
  By Newton's identities, e_j is a polynomial in the power sums p_1,...,p_j.
  Each p_m(S) = sum_{i in U} zeta^{m*i} is an integer-coeff poly in zeta.
  So e_j(S) = N_j(zeta)/j!-ish ... we work with j!*e_j (integer relation) to stay over Z.

Goal (a): compute the l^1 mass / threshold of R^{(j)}_U for j=1,3,4 and compare to e2.
Goal (b): does {e_1=0 AND e_3=0} have a strictly smaller bad-prime set than each alone?
Goal (c): measure the JOINT bad-prime max vs poly(n).

We VERIFY every claimed identity numerically before asserting.
"""
import itertools, math
from sympy import primerange, primitive_root, isprime
from sympy import symbols, Poly, expand, fwht
from functools import reduce

# ---------- exact integer / cyclotomic arithmetic via Z[zeta_n] = Z[X]/(X^{n/2}+1) ----------
# For n = 2^k, the minimal poly of zeta_n is Phi_n(X) = X^{n/2} + 1.
# Represent elements of Z[zeta_n] as coefficient vectors of length n/2 (basis 1,zeta,...,zeta^{n/2-1}),
# with zeta^{n/2} = -1.

def zmul(a, b, h):
    """multiply two elements (length-h coeff vectors) in Z[zeta], zeta^h = -1."""
    res = [0]*(2*h)
    for i, ai in enumerate(a):
        if ai == 0: continue
        for jj, bj in enumerate(b):
            if bj == 0: continue
            res[i+jj] += ai*bj
    # reduce: zeta^{h+t} = -zeta^t
    out = [0]*h
    for d in range(2*h):
        if d < h: out[d] += res[d]
        else: out[d-h] -= res[d]
    return out

def zadd(a,b,h): return [a[i]+b[i] for i in range(h)]
def zsub(a,b,h): return [a[i]-b[i] for i in range(h)]

def zeta_pow(e, h):
    """zeta^e as a coeff vector, zeta^h=-1 so period 2h with sign."""
    e %= (2*h)
    v = [0]*h
    if e < h: v[e] = 1
    else: v[e-h] = -1
    return v

def power_sum_in_Zzeta(U, m, h):
    """p_m(S) = sum_{i in U} zeta^{m*i}  as an element of Z[zeta], for n=2h."""
    acc = [0]*h
    for i in U:
        acc = zadd(acc, zeta_pow(m*i, h), h)
    return acc

def newton_ej_relation(U, j, h):
    """
    Return the integer element j! * e_j(S) in Z[zeta] (as coeff vector),
    computed from power sums via Newton's identities:
       j! e_j = det of the j x j matrix [[p_1,1,0,..],[p_2,p_1,2,..],...]
    We use the recursion: e_0=1, k*e_k = sum_{i=1}^{k} (-1)^{i-1} e_{k-i} p_i.
    But that produces e_k directly (rational). To keep INTEGER, return j! e_j.
    Actually Newton gives e_k exactly as an element of Z[zeta] (it IS an integer
    symmetric function of integer-ish roots). We compute e_k directly in Z[zeta]
    via the recursion multiplying through, tracking denominator.
    Simpler: e_k = elementary symmetric, compute directly from the multiset of roots
    as elements of Z[zeta]. The roots are zeta^i (i in U).
    """
    # direct elementary symmetric via generating polynomial prod (1 + zeta^i * t)
    # coefficient of t^j is e_j. Do it in Z[zeta][t].
    # coeffs[t-degree] = element of Z[zeta]
    coeffs = [[0]*h for _ in range(len(U)+1)]
    coeffs[0] = [1]+[0]*(h-1)   # e_0 = 1
    deg = 0
    for i in U:
        ri = zeta_pow(i, h)
        # multiply current poly (in t) by (1 + ri t)
        newc = [list(c) for c in coeffs]
        for d in range(deg, -1, -1):
            # contribution to degree d+1
            term = zmul(coeffs[d], ri, h)
            newc[d+1] = zadd(newc[d+1], term, h)
        coeffs = newc
        deg += 1
    return coeffs[j]  # e_j(S) exactly as element of Z[zeta]

def is_zero_Zzeta(v): return all(x==0 for x in v)

def l1_mass(v): return sum(abs(x) for x in v)

# ---------- verification: e_j over C vs the Z[zeta] computation ----------
def verify_ej_identity(n=16):
    h = n//2
    import random
    random.seed(1)
    # test against complex evaluation
    zc = complex(math.cos(2*math.pi/n), math.sin(2*math.pi/n))
    ok = True
    for _ in range(200):
        w = random.randint(2, n)
        U = sorted(random.sample(range(n), w))
        roots = [zc**i for i in U]
        for j in range(1, min(6, w+1)):
            # complex e_j
            ej_c = sum(reduce(lambda a,b:a*b, comb, 1) for comb in itertools.combinations(roots, j))
            # Z[zeta] e_j -> complex
            v = newton_ej_relation(U, j, h)
            ej_z = sum(v[t]*(zc**t) for t in range(h))
            if abs(ej_c - ej_z) > 1e-6:
                ok = False
                print(f"  MISMATCH n={n} U={U} j={j}: C={ej_c} Zzeta={ej_z}")
    print(f"[verify] e_j Z[zeta] vs C  (n={n}, 200 random U): {'OK' if ok else 'FAIL'}")
    return ok

# ---------- (a) l^1 mass / threshold of e_j=0 relation ----------
def ej_threshold_data(n, js=(1,2,3,4)):
    h = n//2
    print(f"\n=== (a) n={n}, h=n/2={h}: l^1 mass of e_j(S) over Z[zeta] (max over U), threshold exponent = h ===")
    print(f"    proven e2 l^1 bound = card(U)^2 + card(U); threshold = (l1)^h, p_bad <= (l1)^h")
    for j in js:
        maxl1 = 0; argU=None
        # scan widths >= j
        for w in range(j, n+1):
            for U in itertools.combinations(range(n), w):
                if len(U) < j: continue
                v = newton_ej_relation(list(U), j, h)
                m = l1_mass(v)
                if m > maxl1:
                    maxl1 = m; argU = U
            # only need a few widths to see growth; cap to keep it fast
            if w >= min(n, j+4): break
        # compare to a card-based heuristic
        wmax = min(n, j+4)
        print(f"  e_{j}: max l1 (w<= {wmax}) = {maxl1:6d}   ~ C({wmax},{j})={math.comb(wmax,j)}   threshold (l1)^h = {maxl1}^{h}")

# ---------- bad-prime sets for individual and JOINT constraints ----------
def primes_1_mod_n(n, lo, hi):
    return [p for p in primerange(lo, hi) if (p-1)%n==0]

def gen_mu(n, p):
    g = pow(primitive_root(p), (p-1)//n, p)
    return [pow(g, i, p) % p for i in range(n)], g

def ej_mod_p(U, j, mu, p):
    """e_j(S) mod p where S = {mu[i] : i in U}."""
    roots = [mu[i] for i in U]
    # elementary symmetric via poly expansion mod p
    coeffs = [0]*(len(roots)+1); coeffs[0]=1
    deg=0
    for r in roots:
        for d in range(deg, -1, -1):
            coeffs[d+1] = (coeffs[d+1] + coeffs[d]*r) % p
        deg+=1
    return coeffs[j] % p

def char0_ej_zero(U, j, h):
    """is e_j(S)=0 over C / Z[zeta]?"""
    return is_zero_Zzeta(newton_ej_relation(list(U), j, h))

def bad_primes_for_constraints(n, constraints, widths, prime_hi, require_distinct_squares=False):
    """
    For each prime p ≡ 1 mod n below prime_hi, find configs U (of given widths) where
    ALL e_j (j in constraints) vanish mod p but NOT all over C (spurious / 'bad').
    Returns set of bad primes and detail.
    constraints: tuple of j's that must SIMULTANEOUSLY vanish.
    """
    h = n//2
    bad = {}
    ps = primes_1_mod_n(n, n+1, prime_hi)
    for p in ps:
        mu, g = gen_mu(n, p)
        found = False
        for w in widths:
            for U in itertools.combinations(range(n), w):
                # mod-p: all constraints vanish?
                if all(ej_mod_p(U, j, mu, p)==0 for j in constraints):
                    # char-0: do all vanish?  spurious if NOT all vanish over C
                    c0 = all(char0_ej_zero(U, j, h) for j in constraints)
                    if not c0:
                        found = True
                        bad.setdefault(p, []).append((U, w))
                        break
            if found: break
    return bad, ps

if __name__ == "__main__":
    print("########## VERIFY e_j identity ##########")
    verify_ej_identity(16)
    verify_ej_identity(8)

    print("\n########## (a) e_j thresholds ##########")
    ej_threshold_data(8, js=(1,2,3,4))
    ej_threshold_data(16, js=(1,2,3,4))
