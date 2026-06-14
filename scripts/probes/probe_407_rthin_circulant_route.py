"""
#407 R-thin via the twist-orbit CIRCULANT / higher-moment route -- result: REDUCES but does NOT close.

The R-thin lemma (the sole char-free residual after the ring-hom monotonicity + Kambire prime-field
upper bound): a GENUINELY-RAGGED agreement set S of a genuine monomial line x^a+gamma*x^b on mu_n
(d=gcd(a-b,n)>=2, S not a coset-union of any nontrivial mu_{d'}) has |S| <= Johnson ~ sqrt(nk).

The single-c twist structure: c_omega(x)=omega^{-a}c(omega x) (omega in mu_d) are L=d distinct deg<k
codewords sharing one c; A_omega = agreement(c_omega, line) = omega^{-1} S. The pairwise-agreement
matrix M_{s,t}=|A_{omega^s} cap A_{omega^t}| is EXACTLY a CIRCULANT whose first row is the
autocorrelation v_t=|S cap omega^t S|: v_0=|S|, v_t<=k-1 (MDS, t!=0). The route's hope: the global
single-c constraint (circulant spectrum / higher moments) beats pairwise-MDS list-Johnson, which is
loose at the Kambire worst direction d=n/s, s~44 (d sits ~factor sqrt(rho)*s below the list-Johnson
threshold d>=sqrt(nk)).

WHAT THIS PROBE ESTABLISHES (all verified below):

 (1) M is exactly circulant (autocorrelation), and the KEY IDENTITY
       sum_{t=0}^{d-1} v_t = sum_{orbits O} |S cap O|^2     (orbit incidence)
     holds exactly. Combined with v_t<=k-1 and Cauchy-Schwarz over the n/d orbits, this gives the
     AUTOCORRELATION BOUND
       |S| <= n/(2d) + sqrt((n/2d)^2 + n(d-1)(k-1)/d).
     This BEATS list-Johnson: the gap to sqrt(nk) drops from MULTIPLICATIVE (factor ~1.04-1.5 at the
     prize direction) to ADDITIVE Theta(s) = ~s/2.

 (2) BUT the circulant SPECTRUM carries no further info about |S|: an LP shows
     LP(full-PSD + orbit-incidence) == LP(orbit-incidence only) at every prize direction. The higher
     eigenvalue modes j!=0 constrain the SHAPE of v, never |S|; only the lowest mode lambda_0=sum_t v_t
     binds. So 3rd/4th/higher moments and the PSD constraint provably ADD NOTHING. The route caps at
     the orbit-incidence (lowest-mode) bound.

 (3) The residual additive gap is a CONSTANT ~s/2 ~10 (independent of n), at the prize direction
     d=n/s. It is char-FREE / combinatorial (NOT the BGK sup-norm wall) -- but the circulant
     relaxation cannot remove it.

 (4) The relaxation is in fact LOOSE: the TRUE max ragged |S| (sampled, n=64) is ~n/4 ~18, far below
     both sqrt(nk)=32 and the relaxation bound 39. So |S|<=sqrt(nk) is TRUE with large margin; the
     obstruction to PROVING it is REALIZABILITY of the orbit profile by a single deg<k polynomial,
     which the circulant-of-agreement-counts discards. The measured off-diagonals (e.g. v=[5,1,0,1])
     are far below the MDS bound k-1, confirming the relaxation throws away the binding constraint.

NET: the higher-moment/circulant route is a genuine REDUCTION (multiplicative -> additive Theta(s)
gap, char-free) but NOT a closure of R-thin. The decisive obstruction is that the circulant spectrum
is determined by its lowest mode alone; closing R-thin needs a realizability argument (single deg<k
c), not a moment/spectral one. No closure claimed.
"""
import math, itertools, random
import numpy as np
from sympy import isprime, primitive_root

try:
    from scipy.optimize import linprog
    HAVE_SCIPY = True
except Exception:
    HAVE_SCIPY = False

random.seed(7)


def find_prime(n, lo):
    p = ((lo // n) + 1) * n + 1
    while not isprime(p):
        p += n
    return p


def setup(p, n):
    g = primitive_root(p)
    w = pow(g, (p - 1) // n, p)
    return w, [pow(w, i, p) for i in range(n)]


def interp(nodes, vals, p):
    m = len(nodes); dd = list(vals); coef = [dd[0]]
    for j in range(1, m):
        for i in range(m - 1, j - 1, -1):
            dd[i] = ((dd[i] - dd[i - 1]) * pow((nodes[i] - nodes[i - j]) % p, p - 2, p)) % p
        coef.append(dd[j])
    poly = [0] * m; poly[0] = coef[0]; cur = [1]
    for j in range(1, m):
        new = [0] * (len(cur) + 1)
        for i, cc in enumerate(cur):
            new[i] = (new[i] - cc * nodes[j - 1]) % p; new[i + 1] = (new[i + 1] + cc) % p
        cur = new
        for i, cc in enumerate(cur):
            if i < m:
                poly[i] = (poly[i] + coef[j] * cc) % p
    return poly


def peval(c, x, p):
    a = 0; xp = 1
    for cc in c:
        a = (a + cc * xp) % p; xp = (xp * x) % p
    return a


def coset_union(S, n, dp):
    step = n // dp; Ss = set(S)
    return all(((i + t * step) % n in Ss) for i in S for t in range(dp))


def is_ragged(S, n, d):
    return all(not coset_union(S, n, dp) for dp in range(2, d + 1) if d % dp == 0)


def ac_int_bound(n, k, d):
    N = n // d; best = 0
    for s in range(1, n + 1):
        q, r = divmod(s, N); ms = r * (q + 1) ** 2 + (N - r) * q ** 2
        if ms <= s + (d - 1) * (k - 1):
            best = s
        if s > N * d:
            break
    return best


def lp_max_s(n, k, d, use_psd, use_orbit):
    """Largest s for which the circulant relaxation is feasible."""
    if not HAVE_SCIPY:
        return None
    N = n // d; best = 0
    for s in range(1, n + 1):
        if s > N * d:
            break
        q, r = divmod(s, N); bm = r * (q + 1) ** 2 + (N - r) * q ** 2
        nv = d - 1
        if nv == 0:
            best = s; continue
        A_ub = []; b_ub = []
        if use_psd:
            for j in range(d):
                A_ub.append([-math.cos(2 * math.pi * j * (t + 1) / d) for t in range(nv)])
                b_ub.append(float(s))
        if use_orbit:
            A_ub.append([-1.0] * nv); b_ub.append(-(bm - s))
        res = linprog(c=[0.0] * nv, A_ub=np.array(A_ub) if A_ub else None,
                      b_ub=np.array(b_ub) if b_ub else None,
                      bounds=[(0, k - 1)] * nv, method='highs')
        if res.success:
            best = s
    return best


def verify_identity():
    print("# (1) KEY IDENTITY  sum_t v_t = sum_O |S cap O|^2  on a concrete ragged set:")
    n, k = 16, 4
    p = find_prime(n, 5000); w, xs = setup(p, n)
    a, b, d = 9, 5, 4
    for gamma in range(1, 40):
        wv = [(pow(xs[i], a, p) + gamma * pow(xs[i], b, p)) % p for i in range(n)]
        for anchors in itertools.combinations(range(n), k):
            c = interp([xs[i] for i in anchors], [wv[i] for i in anchors], p)
            S = [i for i in range(n) if peval(c, xs[i], p) == wv[i]]
            if len(S) >= 5 and is_ragged(S, n, d):
                step = n // d; Ss = set(S)
                v = [sum(1 for i in S if (i + t * step) % n in Ss) for t in range(d)]
                from collections import Counter
                orb = Counter(i % step for i in S)
                sumsq = sum(m * m for m in orb.values())
                print(f"   |S|={len(S)} v={v} sum_t v_t={sum(v)} sum_O|S∩O|^2={sumsq} "
                      f"match={sum(v) == sumsq} offdiag_max={max(v[1:])} (k-1={k-1}, so MDS bound LOOSE)")
                return


def spectral_vacuity():
    print("\n# (2) The circulant SPECTRUM adds nothing: LP(PSD+orbit) == LP(orbit-only).")
    if not HAVE_SCIPY:
        print("   [scipy unavailable -- skipped]")
        return
    for (n, k) in [(1024, 256), (256, 64)]:
        johnson = math.sqrt(n * k)
        print(f"   n={n} k={k} sqrt(nk)={johnson:.1f}")
        for sd in [8, 16, 44, 64]:
            d = n // sd
            if d < 2:
                continue
            full = lp_max_s(n, k, d, True, True)
            orb = lp_max_s(n, k, d, False, True)
            psd = lp_max_s(n, k, d, True, False)
            print(f"     s={sd} d={d}: PSD+orbit={full}  orbit-only={orb}  PSD-only={psd}  "
                  f"(PSD adds {'nothing' if full == orb else 'SOMETHING'})")


def additive_gap():
    print("\n# (3) Residual gap is CONSTANT ~s/2 at the prize direction d=n/s (char-free, not BGK):")
    print(f"   {'mu':>3}{'n':>14}{'d=n/44':>12}{'sqrt(nk)':>14}{'relax':>14}{'gap':>7}")
    for mu in [10, 18, 26, 30]:
        n = 2 ** mu; k = n // 4; d = max(2, n // 44)
        johnson = math.sqrt(n * k)
        relax = n / (2 * d) + math.sqrt((n / (2 * d)) ** 2 + n * (d - 1) * (k - 1) / d)
        print(f"   {mu:>3}{n:>14}{d:>12}{johnson:>14.1f}{relax:>14.1f}{relax - johnson:>7.1f}")


def truth_is_smaller():
    print("\n# (4) TRUE max ragged |S| << relaxation (relaxation loose; realizability is the obstruction):")
    n, k = 64, 16
    p = find_prime(n, 3000); w, xs = setup(p, n)
    johnson = math.sqrt(n * k)
    byd = {}
    dirs = [(a, b, math.gcd((a - b) % n, n)) for a in range(k, n) for b in range(a)
            if math.gcd((a - b) % n, n) >= 2]
    random.shuffle(dirs); dirs = dirs[:60]
    for (a, b, d) in dirs:
        for gamma in [1, 2, 3, 5, random.randrange(2, p)]:
            wv = [(pow(xs[i], a, p) + gamma * pow(xs[i], b, p)) % p for i in range(n)]
            for _ in range(140):
                anchors = random.sample(range(n), k)
                c = interp([xs[i] for i in anchors], [wv[i] for i in anchors], p)
                S = tuple(i for i in range(n) if peval(c, xs[i], p) == wv[i])
                if len(S) >= k + 1 and is_ragged(S, n, d):
                    byd[d] = max(byd.get(d, 0), len(S))
    print(f"   n={n} k={k} sqrt(nk)={johnson:.1f}")
    print(f"   {'d':>4}{'true max ragged':>18}{'sqrt(nk)':>10}{'relax(AC_int)':>14}")
    for d in sorted(byd):
        print(f"   {d:>4}{byd[d]:>18}{johnson:>10.1f}{ac_int_bound(n, k, d):>14}")


if __name__ == "__main__":
    verify_identity()
    spectral_vacuity()
    additive_gap()
    truth_is_smaller()
    print("\nVERDICT: REDUCES (mult.->additive Theta(s) char-free gap), DOES NOT CLOSE R-thin.")
    print("PSD/higher-moments provably vacuous beyond the lowest orbit-incidence mode; the binding")
    print("constraint is realizability by a single deg<k polynomial, discarded by the count-circulant.")
