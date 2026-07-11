"""
δ* window char-faithfulness at CONSTANT RATE, pushed to n=64 (ρ=1/16, k=4).  (#407)

Next octave after n=16 (ρ=1/4) and n=32 (ρ=1/8). Same method as the n=16/n=32
probes: exact monomial-pencil far-line incidence I_pencil(δ) over μ_n ⊊ F_p*
(p≡1 mod n), computed WITHOUT per-γ enumeration. For each (k+1)-subset A of
positions solve the (k+1)x(k+1) linear system [g(ζ^i)=ζ^{ib}+γζ^{ia}, i∈A] for
(g,γ), then compute the TRUE agreement of that γ over all n points.
I(w) = #{distinct γ : agreement ≥ w}.  C(n,k+1) solves, INDEPENDENT of p, so it
reaches p ≫ n³ = 262144 (the prize-faithful direction; prize p ≈ n·2^128 ≫ n³).

DECIDING OBSERVABLE: is the δ*-crossing band char-INVARIANT at n=64 for p≫n³?
  invariant  -> rigid (r=k/2), δ* char-independent  -> favors closure
  char-dep   -> floppy (r=1), q-dependent           -> onset of BGK wall

ENGINEERING: C(64,5)=7.62M subsets. We batch-process subsets and run a numpy
modular Gaussian elimination on a batch of (k+1)x(k+2) augmented systems at once.
All intermediate values are kept < p by reducing mod p after every multiply, so
int64 never overflows (p ~ 1e6 -> products < 1e12 < 9.2e18). The agreement of
each distinct γ is computed once via a vectorized Horner over all n points.

Far pencils: a,b ≥ k, a,b ≠ n/2, gcd structure varied. ρ=1/16 window:
(1−√ρ, 1−ρ) = (0.75, 0.9375) -> w in (4, 16) crossing region.
"""
import itertools, math, sys, time
import numpy as np


def isp(x):
    if x < 2:
        return False
    d = 2
    while d * d <= x:
        if x % d == 0:
            return False
        d += 1
    return True


def proot(p, n):
    for c in range(2, p):
        h = pow(c, (p - 1) // n, p)
        if pow(h, n, p) == 1 and pow(h, n // 2, p) != 1:
            return h
    return None


def batch_solve_mod(Ms, rhss, p):
    """
    Solve a batch of square systems M x = b mod p, all m x m.
    Ms:   (B, m, m) int64,  rhss: (B, m) int64.  p: prime.
    Returns (sols (B,m) int64, ok (B,) bool).  ok=False where singular.
    Modular Gaussian elimination with partial (nonzero) pivot, values kept < p.
    """
    B, m, _ = Ms.shape
    A = np.concatenate([Ms % p, (rhss % p)[:, :, None]], axis=2).astype(np.int64)  # (B,m,m+1)
    ok = np.ones(B, dtype=bool)
    for c in range(m):
        # find, per system, a pivot row >= c with nonzero entry in col c
        col = A[:, :, c].copy()
        col[:, :c] = 0  # ignore rows above c
        nz = col != 0
        has = nz.any(axis=1)
        ok &= has
        piv = np.where(has, np.argmax(nz, axis=1), c)  # first nonzero row at/below c
        # swap row c and row piv
        idx = np.arange(B)
        tmp = A[idx, c, :].copy()
        A[idx, c, :] = A[idx, piv, :]
        A[idx, piv, :] = tmp
        # normalize pivot row: multiply by inverse of A[:,c,c]
        pivval = A[:, c, c].copy()
        pivval[pivval == 0] = 1  # avoid 0^(p-2); singular ones masked by ok
        inv = pow_mod_vec(pivval, p - 2, p)
        A[:, c, :] = (A[:, c, :] * inv[:, None]) % p
        # eliminate column c from all other rows
        for r in range(m):
            if r == c:
                continue
            f = A[:, r, c].copy()
            A[:, r, :] = (A[:, r, :] - f[:, None] * A[:, c, :]) % p
    sols = A[:, :, m] % p
    return sols, ok


def pow_mod_vec(base, e, p):
    """Vectorized modular exponentiation, base (B,) int64, scalar exponent e."""
    base = base % p
    result = np.ones_like(base)
    b = base.copy()
    while e > 0:
        if e & 1:
            result = (result * b) % p
        e >>= 1
        if e:
            b = (b * b) % p
    return result


def bandcounts(p, n, k, a, b, batch=200000, verbose=False):
    z = proot(p, n)
    pts = np.array([pow(z, i, p) for i in range(n)], dtype=np.int64)
    za = np.array([pow(z, (i * a) % n, p) for i in range(n)], dtype=np.int64)
    zb = np.array([pow(z, (i * b) % n, p) for i in range(n)], dtype=np.int64)
    # powr[i][j] = pts[i]^j for j in 0..k-1
    powr = np.empty((n, k), dtype=np.int64)
    powr[:, 0] = 1
    for j in range(1, k):
        powr[:, j] = (powr[:, j - 1] * pts) % p
    # all (k+1)-subsets; process in batches
    ga = {}  # gamma -> agreement (computed lazily, only first time gamma seen)
    seen_gamma = {}  # gamma -> g-coeff tuple (first witness), for distinct gammas only
    combos = itertools.combinations(range(n), k + 1)
    t0 = time.time()
    total = 0
    while True:
        buf = list(itertools.islice(combos, batch))
        if not buf:
            break
        idx = np.array(buf, dtype=np.int64)  # (Bc, k+1)
        Bc = idx.shape[0]
        # build (Bc, k+1, k+1): cols 0..k-1 = powr[i][j], col k = -za[i]
        M = np.empty((Bc, k + 1, k + 1), dtype=np.int64)
        M[:, :, :k] = powr[idx]                      # (Bc,k+1,k)
        M[:, :, k] = (-za[idx]) % p                  # (Bc,k+1)
        rhs = zb[idx]                                # (Bc,k+1)
        sols, ok = batch_solve_mod(M, rhs, p)
        okr = np.nonzero(ok)[0]
        gammas = sols[okr, k]
        gs = sols[okr, :k]
        # keep first g for each distinct gamma not yet seen
        for r in range(len(okr)):
            gm = int(gammas[r])
            if gm not in seen_gamma:
                seen_gamma[gm] = gs[r].copy()
        total += Bc
        if verbose:
            sys.stderr.write(
                f"\r    p={p} pencil({a},{b}): {total}/{math.comb(n,k+1)} "
                f"({100*total/math.comb(n,k+1):.0f}%) {time.time()-t0:.0f}s ngamma={len(seen_gamma)}")
            sys.stderr.flush()
    if verbose:
        sys.stderr.write("\n")
    # VECTORIZED agreement: for all G distinct gammas at once.
    G = len(seen_gamma)
    if G == 0:
        return {w: 0 for w in range(k + 1, n + 1)}
    gam_arr = np.fromiter(seen_gamma.keys(), dtype=np.int64, count=G)          # (G,)
    coef = np.stack(list(seen_gamma.values())).astype(np.int64)               # (G,k)
    # g(pts[i]) for all gammas, all points: Horner over k coeffs.
    # gi[G, n]; pts (n,). Build with broadcasting, mod p each step.
    gi = np.zeros((G, n), dtype=np.int64)
    for j in range(k - 1, -1, -1):
        gi = (gi * pts[None, :] + coef[:, j][:, None]) % p                    # (G,n)
    target = (zb[None, :] + (gam_arr[:, None] * za[None, :]) % p) % p          # (G,n)
    agree = np.count_nonzero(gi == target, axis=1)                            # (G,)
    return {w: int(np.count_nonzero(agree >= w)) for w in range(k + 1, n + 1)}


def main():
    n, k = 64, 4   # rho = 1/16; window (1-sqrt(1/16), 1-1/16) = (0.75, 0.9375)
    n3 = n ** 3    # 262144
    # primes p ≡ 1 mod 64, spanning thin (p<n^3) to p >> n^3 (prize-faithful direction)
    cand = [193, 257, 449, 769, 65537, 274177, 786433, 1179649, 5767169, 13631489]
    primes = [p for p in cand if isp(p) and (p - 1) % n == 0]
    print(f"n={n} k={k} rho={k/n}=1/16, n^3={n3}, primes={primes}", flush=True)
    print(f"window (1-sqrt(rho), 1-rho) = (0.750, 0.9375); crossing-region bands w in 5..15", flush=True)
    # far pencils, varied gcd(b-a, n)
    pencils = [(5, 7), (5, 9), (9, 13), (17, 23)]
    for (a, b) in pencils:
        g = math.gcd(b - a, n)
        print(f"\npencil({a},{b}) gcd(b-a,n)={g}:", flush=True)
        prof = {}
        for p in primes:
            t0 = time.time()
            bc = bandcounts(p, n, k, a, b, verbose=True)
            prof[p] = bc
            wsel = [bc[w] for w in range(5, 16)]
            print(f"  p={p:>9} (p/n^3={p/n3:.2f}) [{time.time()-t0:.0f}s]: w5..w15={wsel}", flush=True)
        # report char-invariance per band, p >> n^3 only
        for w in range(6, 14):
            big = [prof[p][w] for p in primes if p > n3]
            d = 1 - w / n
            print(f"   band w={w:>2} (d={d:.3f}) p>>n^3: {big} char-invariant={len(set(big))<=1}",
                  flush=True)


if __name__ == "__main__":
    main()
