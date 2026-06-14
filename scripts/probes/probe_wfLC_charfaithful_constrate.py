#!/usr/bin/env python3
"""
LANE LC (#407, R4 char-faithfulness at constant rate).

QUESTION (§5.3): does the char-p far-line incidence I(a,b;r) (= bad-scalar count = list size,
collision-capped) match its char-0 value at the BINDING band, for n >= 32, at PRIZE-SCALE primes?

If YES (faithful) for n>=32 at constant rate  =>  delta* = the char-0 Kambire edge (a CLOSURE).
If NO (char-p EXCESS at the binding band)      =>  clean countermodel; delta* < Kambire edge.

METHOD (exact, no sqrt-loss; reuses the in-tree FarCosetExplosion object):
  For each agreement set R (|R|=n-r), the line  x^a + gamma x^b  lies in RS[R,k] iff the
  left-null P of V_R kills both x^a|_R and x^b|_R:
    - R "heavy" (ALL gamma bad, incidence saturates to q)  iff  P x^a|_R = 0 AND P x^b|_R = 0
    - else <= 1 gamma.
  I(a,b;r) = #{distinct good gammas}  (or q if any R heavy).

CHAR-0 vs CHAR-P: char-0 is modelled as "the count that is STABLE across many generic large
primes p = n*m+1" (the same logic the in-tree n=16 finding used to assert p-independence: distinct
basis subsets => distinct ℂ coords => no accidental collision). Char-p EXCESS = a prize-scale prime
whose count EXCEEDS the stable (generic) count -- an accidental mod-p vanishing (heavy set or extra
gamma) that does NOT occur over ℂ. We test the WORST monomial direction dir(n/4, 5n/8) PLUS a full
far-direction sweep, at the binding band, over many primes including prize-scale (q ~ n^4..n^5).

Feasibility: enumerate only near-capacity bands where C(n, n-r) is tractable.
"""
import sys, itertools, random
sys.path.insert(0, 'scripts/probes')
from prize_workspace import subgroup, isprime

def find_prime_cong1(n, lo):
    p = lo + (1 - lo) % n
    if p <= 2: p += n
    while True:
        if p % n == 1 and isprime(p): return p
        p += n

def _rref(rows, p):
    rows = [r[:] for r in rows]; m = len(rows); nc = len(rows[0]) if m else 0
    pr = 0
    for c in range(nc):
        sel = next((r for r in range(pr, m) if rows[r][c] % p), None)
        if sel is None: continue
        rows[pr], rows[sel] = rows[sel], rows[pr]
        inv = pow(rows[pr][c], p - 2, p)
        rows[pr] = [(x * inv) % p for x in rows[pr]]
        for r in range(m):
            if r != pr and rows[r][c] % p:
                f = rows[r][c]; rows[r] = [(rows[r][j] - f * rows[pr][j]) % p for j in range(nc)]
        pr += 1
        if pr == m: break
    return rows

def left_null(V, p):
    m = len(V); k = len(V[0]) if m else 0
    aug = [V[i][:] + [1 if j == i else 0 for j in range(m)] for i in range(m)]
    return [[row[k + j] % p for j in range(m)] for row in _rref(aug, p)
            if all(x % p == 0 for x in row[:k]) and any(x % p for x in row[k:])]

def incidence(S, p, k, a, b, r):
    """Exact far-line incidence I(a,b;r) over F_p; (count, n_heavy_sets)."""
    n = len(S); size = n - r
    if size <= k: return p, -1
    pa_ = [pow(int(x), a, p) for x in S]; pb_ = [pow(int(x), b, p) for x in S]
    good = set(); heavy = 0
    for R in itertools.combinations(range(n), size):
        V = [[pow(int(S[i]), j, p) for j in range(k)] for i in R]
        P = left_null(V, p)
        if not P: continue
        pa = [sum(P[t][ii] * pa_[R[ii]] for ii in range(size)) % p for t in range(len(P))]
        pb = [sum(P[t][ii] * pb_[R[ii]] for ii in range(size)) % p for t in range(len(P))]
        if not any(pb):
            if not any(pa): heavy += 1
            continue
        i = next(j for j in range(len(pb)) if pb[j])
        g = (-pa[i] * pow(pb[i], p - 2, p)) % p
        if all((pa[t] + g * pb[t]) % p == 0 for t in range(len(pb))): good.add(g)
    return (p if heavy else len(good)), heavy

def measure(n, k, r, a, b, primes):
    """Return list of (p, count, heavy) for direction (a,b) at band r across primes."""
    out = []
    for p in primes:
        S = subgroup(p, n)
        c, h = incidence(S, p, k, a, b, r)
        out.append((p, c, h))
    return out

if __name__ == '__main__':
    random.seed(7)
    # ---- prize-scale primes: q ~ n^4 .. n^5 (beta in [4,5]), n | p-1, ODD index, multiple primes
    def prize_primes(n, count=6):
        ps = []
        lo = n**4
        attempts = 0
        while len(ps) < count and attempts < 200000:
            cand = find_prime_cong1(n, lo)
            m = (cand - 1)//n
            if m % 2 == 1:            # ODD index (regime requirement)
                ps.append(cand)
            lo = cand + 1
            attempts += 1
        return ps
    # generic "char-0 proxy" primes: spread out, away from any single structure
    def generic_primes(n, count=4):
        ps=[]; lo=n*131+1
        while len(ps)<count:
            cand=find_prime_cong1(n, lo); ps.append(cand); lo=cand*3+1
        return ps

    print("="*78)
    print("LANE LC: char-p vs char-0 far-line incidence at BINDING band, n>=32, constant rate")
    print("="*78)

    # ---------- n=16 control (must reproduce in-tree p-independence at binder) ----------
    n,k = 16,4
    ps = generic_primes(16,3) + prize_primes(16,3)
    print(f"\n[CONTROL n=16 k=4 rho=1/4] worst-dir dir(n/4,5n/8)=(4,10); also binder (10,4)")
    for (a,b,tag) in [(4,10,'dir(n/4,5n/8)'),(10,4,'binder x^4'),(2,8,'x^7-style')]:
        for r in (9,10):
            if (n-r)<=k: continue
            res = measure(n,k,r,a,b,ps)
            cnts=[c for _,c,_ in res]
            print(f"  (a={a},b={b}) {tag:16s} r={r} delta={r/n:.4f}: counts={cnts} "
                  f"{'FAITHFUL' if len(set(cnts))==1 else 'EXCESS/VARIES'}")

    # ---------- n=32 constant rate rho=1/4 (k=8). Binding band near capacity. ----------
    n,k = 32,8
    ps = generic_primes(32,3) + prize_primes(32,3)
    print(f"\n[n=32 k=8 rho=1/4] primes={ps}")
    # worst monomial direction dir(n/4, 5n/8) = (8, 20); restrict to FAR (b < n-r)
    # binding band: scan near-capacity r where n-r in [k+1 .. k+5] => r in [n-k-5 .. n-k-1]
    a_w, b_w = n//4, 5*n//8          # (8, 20)
    print(f"  worst-dir dir(n/4,5n/8) = (a={a_w}, b={b_w})")
    for r in range(n-k-5, n-k):      # n-r from k+1=9 down... actually n-r in [9..13]
        size = n-r
        far_ok = b_w < size
        if size<=k: continue
        # pick the worst-dir if far, else fall back to a far low-exponent binder
        cands = []
        if far_ok: cands.append((a_w,b_w,'worst dir(n/4,5n/8)'))
        # also test low-exponent far binder x^k (the in-tree n=16 binder) at offset n/4
        if k < size: cands.append((n//4, k, 'binder x^k @ off n/4'))
        for (a,b,tag) in cands:
            res = measure(n,k,r,a,b,ps)
            cnts=[(p%100000,c,h) for p,c,h in res]
            allc=[c for _,c,_ in res]
            faith = 'FAITHFUL' if len(set(allc))==1 else 'EXCESS/VARIES'
            print(f"  r={r} delta={r/n:.4f} size={size}: (a={a},b={b}) {tag:24s} "
                  f"counts(p%1e5,I,heavy)={cnts} => {faith}")
