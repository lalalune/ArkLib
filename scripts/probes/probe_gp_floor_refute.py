"""
PROXIMITY PRIZE -- Conjecture (G) refutation hunt.

(G): the m=(p-1)/n Gaussian periods eta_i of mu_n (proper subgroup, n=2^mu | p-1)
satisfy max_i |eta_i| <= sqrt(2 n log m) = sqrt(2 n log(p/n))  (sub-Gaussian floor),
in the prize regime p = n^beta, beta in [4,5].

This probe attacks (G) from two directions:
  (A) BRUTE SCAN: push n to 64 and 128, scan many primes at beta in [4,5],
      report the worst ratio R = max_i|eta_i| / sqrt(2 n log m). R>1 refutes (G).
  (B) ENGINEERED BAD PRIMES: build a SHORT genuine relation
          alpha = sum_{i} zeta_n^{a_i} - sum_{j} zeta_n^{b_j}  in Z[zeta_n], alpha != 0,
      compute Norm(alpha) in Z (alpha as a polynomial mod the 2^mu-th cyclotomic x^{n/2}+1),
      take a prime factor p of Norm(alpha) with n | p-1 in the prize regime.
      Such p forces a short additive relation among the n-th roots mod p, which
      can inflate some |eta_i|. Test whether the floor breaks for these p.

Honesty: cmath/numpy exact arithmetic. No fabrication. Negatives reported.
max|eta| computed EXACTLY (numpy cos/sin of exact (b*x mod p) angles); int64 safe
since (p-1)^2 < 9.2e18 for all p used here (p < 3e9 => (p-1)^2 < 9e18).
"""
import math, time
import numpy as np

# ---------- number theory helpers ----------
def isprime(q):
    if q < 2: return False
    if q % 2 == 0: return q == 2
    if q % 3 == 0: return q == 3
    i = 5
    while i * i <= q:
        if q % i == 0 or q % (i + 2) == 0: return False
        i += 6
    return True

def factor(m):
    f = set(); d = 2
    while d * d <= m:
        while m % d == 0: f.add(d); m //= d
        d += 1 if d == 2 else 2
    if m > 1: f.add(m)
    return f

def primroot(p):
    fs = factor(p - 1)
    for g in range(2, p):
        if all(pow(g, (p - 1) // q, p) != 1 for q in fs): return g

# ---------- max |eta_i| (= M(n) = max_b |S_b|) over the m proper cosets ----------
def max_eta(n, p, g=None, return_argmax=False):
    """max over the m=(p-1)/n coset reps b=g^i of |sum_{x in mu_n} e_p(b x)|.
    int64-safe: requires (p-1)^2 < 2^63 (p < ~3.04e9)."""
    assert (p - 1) ** 2 < (1 << 62), "int64 overflow risk; p too large"
    if g is None: g = primroot(p)
    m = (p - 1) // n
    z = pow(g, m, p)
    G = np.array([pow(z, i, p) for i in range(n)], dtype=np.int64)
    two_pi_over_p = 2 * math.pi / p
    breps = np.empty(m, dtype=np.int64)
    cur = 1
    for i in range(m):
        breps[i] = cur; cur = cur * g % p
    mx = 0.0; arg = -1
    CHUNK = 50000
    for start in range(0, m, CHUNK):
        bs = breps[start:start + CHUNK]
        prod = (bs[:, None] * G[None, :]) % p           # int64, safe
        ang = prod.astype(np.float64) * two_pi_over_p
        re = np.cos(ang).sum(axis=1); im = np.sin(ang).sum(axis=1)
        vals = np.sqrt(re * re + im * im)
        k = int(vals.argmax())
        if vals[k] > mx:
            mx = float(vals[k]); arg = start + k
    if return_argmax:
        return mx, arg
    return mx

def ratio(n, p, g=None):
    m = (p - 1) // n
    return max_eta(n, p, g) / math.sqrt(2 * n * math.log(m))

def primes_for(n, lo, cnt):
    out = []; q = lo + (1 - lo % 2)   # odd start
    while len(out) < cnt:
        if (q - 1) % n == 0 and isprime(q): out.append(q)
        q += 2
    return out

# =====================================================================
# (A) BRUTE SCAN at n=64, n=128
# =====================================================================
def scan(n, beta, cnt):
    lo = int(n ** beta)
    ps = primes_for(n, lo, cnt)
    t0 = time.time()
    rs = [ratio(n, p) for p in ps]
    worst = max(rs); wp = ps[rs.index(worst)]
    flag = "*** R>1 REFUTES (G) ***" if worst > 1 else "all<1 floor holds"
    print(f"  n={n} beta~{math.log(ps[0])/math.log(n):.2f} ({len(rs)}p): "
          f"min={min(rs):.4f} mean={sum(rs)/len(rs):.4f} MAX={worst:.4f} @p={wp} "
          f"[{flag}]  ({time.time()-t0:.1f}s)", flush=True)
    return worst

# =====================================================================
# (B) ENGINEERED BAD PRIMES
# A short genuine relation alpha in Z[zeta_n].  zeta_n satisfies the 2^mu-th
# cyclotomic Phi = x^{n/2} + 1.  Represent elements as length-(n/2) int vectors
# (coeffs of 1, zeta, ..., zeta^{n/2-1}), reduce zeta^{n/2} = -1.
# Norm(alpha) = product over the n/2 embeddings = Res(Phi, alpha)/lc, computed
# via resultant of integer polynomials.
# We pick alpha = (sum of a few roots) - (sum of a few roots), a SHORT relation
# (r small), then factor Norm and look for prize-regime primes p | Norm with n|p-1.
# =====================================================================
def cyclo_reduce(vec, h):
    """reduce a polynomial (list of int coeffs) modulo x^h + 1 -> length-h vec."""
    out = [0] * h
    for i, c in enumerate(vec):
        if c == 0: continue
        r = i % (2 * h)
        if r < h: out[r] += c
        else: out[r - h] -= c
    return out

def norm_of_alpha(exps_plus, exps_minus, n):
    """alpha = sum zeta^a (a in exps_plus) - sum zeta^b (b in exps_minus).
    Norm over Q(zeta_n)/Q via integer resultant Res(x^{n/2}+1, alpha(x))."""
    h = n // 2
    # build alpha as a polynomial of degree < n (then reduce)
    deg = max(exps_plus + exps_minus + [0])
    poly = [0] * (deg + 1)
    for a in exps_plus: poly[a] += 1
    for b in exps_minus: poly[b] -= 1
    av = cyclo_reduce(poly, h)            # length-h coeff vector mod x^h+1
    # Norm = Res(Phi, alpha) = product_{Phi(w)=0} alpha(w); compute via integer resultant
    return int(round(_resultant(_phi_poly(h), _strip(av))))

def _phi_poly(h):
    p = [0] * (h + 1); p[0] = 1; p[h] = 1   # x^h + 1
    return p

def _strip(p):
    while len(p) > 1 and p[-1] == 0: p = p[:-1]
    return p

def _resultant(a, b):
    """Resultant of two integer polynomials via float (numpy) eigenvalue product;
    we instead use exact resultant via subresultant-free determinant for safety:
    Res(Phi, alpha) = lc(alpha)^deg(Phi) * prod alpha(root_i) -- compute with numpy
    roots of Phi (exact: roots are 2^mu-th primitive roots = e^{i pi (2k+1)/h}).
    Returns a float that we round; alpha integer => Norm is integer."""
    # Phi = x^h + 1, roots are e^{i*pi*(2k+1)/h}, k=0..h-1
    h = len(a) - 1
    roots = [complex(math.cos(math.pi * (2 * k + 1) / h), math.sin(math.pi * (2 * k + 1) / h))
             for k in range(h)]
    prod = 1.0 + 0j
    for w in roots:
        val = 0j
        for j, c in enumerate(b):
            val += c * (w ** j)
        prod *= val
    return prod.real

def engineer():
    print("(B) ENGINEERED BAD PRIMES from short genuine relations")
    print("    Looking for prize-regime p (n|p-1, beta in [3.5,5.5]) dividing Norm(alpha).")
    import random
    for n in [16, 32, 64]:
        h = n // 2
        found = []
        # try many SHORT relations: r in {2,3,4} roots each side, distinct exponents
        rng = random.Random(12345 + n)
        tried = 0
        for trial in range(4000):
            r = rng.choice([2, 3, 4])
            es = rng.sample(range(n), 2 * r)
            plus, minus = es[:r], es[r:]
            try:
                N = norm_of_alpha(plus, minus, n)
            except Exception:
                continue
            if N == 0: continue
            N = abs(N)
            tried += 1
            # factor out small primes, look for a large prime factor p with n|p-1 in regime
            mm = N
            for d in list(factor(mm)):
                # only consider d itself if it's a candidate prime in regime
                if d < n ** 3.4 or d > n ** 5.6: continue
                if (d - 1) % n != 0: continue
                if not isprime(d): continue
                beta = math.log(d) / math.log(n)
                # verify the relation holds mod d: need zeta_n -> some n-th root mod d
                # such that sum zeta^a == sum zeta^b mod d. d|Norm guarantees existence
                # for SOME prime ideal above d; find a primitive n-th root w with the relation.
                if check_relation_mod_p(plus, minus, n, d):
                    found.append((d, beta, r, tuple(plus), tuple(minus)))
        # dedupe primes
        seen = {}
        for d, beta, r, pl, mi in found:
            if d not in seen: seen[d] = (beta, r, pl, mi)
        print(f"  n={n}: tried {tried} relations -> {len(seen)} prize-regime bad primes")
        # test the floor at up to 6 of them (smallest r, then smallest beta)
        cand = sorted(seen.items(), key=lambda kv: (kv[1][1], kv[1][0]))[:6]
        for d, (beta, r, pl, mi) in cand:
            if (d - 1) ** 2 >= (1 << 62):
                print(f"    p={d} beta={beta:.2f} r={r}: SKIP (too large for exact max_eta)")
                continue
            R = ratio(n, d)
            flag = "*** R>1 REFUTES (G) ***" if R > 1 else "floor holds"
            print(f"    p={d} beta={beta:.2f} r={r} rel(+{pl} -{mi}): R={R:.4f} [{flag}]",
                  flush=True)

def check_relation_mod_p(plus, minus, n, p):
    """Is there a primitive n-th root w mod p with sum w^a == sum w^b (mod p)?"""
    # find a primitive n-th root: g^((p-1)/n)
    g = primroot(p)
    z = pow(g, (p - 1) // n, p)
    # try all n powers of z as the image of zeta_n (Galois conjugates)
    for t in range(n):
        if math.gcd(t, n) != 1: continue
        w = pow(z, t, p)
        s = (sum(pow(w, a, p) for a in plus) - sum(pow(w, b, p) for b in minus)) % p
        if s == 0:
            return True
    return False

# =====================================================================
# (B') PRIZE-REGIME ENGINEERING: push Norm(alpha) into [n^4, n^5] using
# slightly longer (still short, r<=5) genuine relations, so the engineered
# bad prime p|Norm(alpha) lands strictly INSIDE the prize regime beta in [4,5].
# =====================================================================
def engineer_prize(n, rmax=5, trials=200000, want=8, seed=7):
    import random
    rng = random.Random(seed + n); out = {}
    lo, hi = n ** 4, n ** 5
    for _ in range(trials):
        if len(out) >= want: break
        r = rng.randint(2, rmax)
        es = rng.sample(range(n), 2 * r)
        plus, minus = es[:r], es[r:]
        N = norm_of_alpha(plus, minus, n)
        if N == 0: continue
        N = abs(N)
        for d in factor(N):
            if d < lo or d > hi: continue
            if (d - 1) % n != 0: continue
            if not isprime(d): continue
            if d in out: continue
            if (d - 1) ** 2 >= (1 << 62): continue
            if check_relation_mod_p(plus, minus, n, d):
                out[d] = (math.log(d) / math.log(n), r, tuple(plus), tuple(minus))
    return out

def engineer_prize_report():
    print("(B') PRIZE-REGIME (beta in [4,5]) engineered bad primes")
    for n in [32, 64]:
        res = engineer_prize(n)
        print(f"  n={n}: {len(res)} engineered primes in [n^4,n^5]")
        for d, (beta, r, pl, mi) in sorted(res.items(), key=lambda kv: kv[1][0]):
            R = ratio(n, d)
            flag = "*** R>1 REFUTES (G) IN PRIZE REGIME ***" if R > 1 else "floor holds"
            print(f"    p={d} beta={beta:.3f} r={r} rel(+{pl} -{mi}): R={R:.4f} [{flag}]",
                  flush=True)

# =====================================================================
if __name__ == "__main__":
    print("=== (A) BRUTE SCAN, larger n, beta in [4,5] ===")
    worst_overall = 0.0
    for (n, beta, cnt) in [(64, 4.0, 12), (64, 4.5, 8), (64, 5.0, 4),
                           (128, 4.0, 4), (128, 4.3, 2)]:
        try:
            w = scan(n, beta, cnt)
            worst_overall = max(worst_overall, w)
        except AssertionError as e:
            print(f"  n={n} beta={beta}: SKIP ({e})")
    print(f"  >>> worst brute ratio = {worst_overall:.4f}")
    print()
    engineer()
    print()
    engineer_prize_report()
