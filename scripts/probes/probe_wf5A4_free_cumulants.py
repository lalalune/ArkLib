#!/usr/bin/env python3
"""
#444 wf-A4 (ALIEN, candidate d): FREE-PROBABILITY deterministic CLT pre-screen.

THE ALIEN MECHANISM.  The Gauss periods {eta_b : b != 0} are the EIGENVALUES of the
Cayley adjacency operator A = sum_{x in mu_n} P_x on F_p (P_x = translation by x).  When
-1 in mu_n (4 | n), they are REAL.  So  M(n) = max_{b!=0} |eta_b| = the SPECTRAL RADIUS
(of the nonprincipal part) = the EDGE of the empirical spectral distribution (ESD)

    nu := (1/(q-1)) sum_{b!=0} delta_{eta_b}.

FREE-PROBABILITY CLAIM (manifesto E24).  If the FREE cumulants  kappa_r(nu)  satisfy
    kappa_2 = n + o(n),   kappa_r = O(n^{r/2} * defect_r)  with sum of defects -> 0,
then nu -> semicircle of radius 2 sqrt(kappa_2) = 2 sqrt(n), and the EDGE (hence M(n)) is
2 sqrt(n) (1 + o(1)).  Semicircle <=> kappa_r = 0 for all r >= 3.  The deterministic input
we MUST supply: the free cumulants computed from the EXACT moments

    m_r = (1/(q-1)) sum_{b!=0} eta_b^r = (q*W_r - n^r)/(q-1),
    W_r = #{(y_1..y_r) in mu_n^r : sum y_i = 0 mod p}   (zero-sum census).

FREE CUMULANTS via non-crossing-partition Moebius inversion (Speicher).  With
m_r = sum_{pi in NC(r)} prod_{block} kappa_{|block|}, invert by:
    kappa_r = sum_{pi in NC(r)} mu(pi,1) prod m_{|block|},  mu = NC Moebius = prod (-1)^{|V|-1} Cat(|V|-1).
We compute kappa_r directly from m_r by the standard recursion on free cumulants.

DELIVERABLES.
  (D1) verify eta_b real (4|n), m_2 = n - n^2/q exactly (Parseval).
  (D2) compute FREE cumulants kappa_r, r=1..R, EXACTLY (rational moments via census).
       Report kappa_r / n^{r/2} (the "free defect" -- 0 iff semicircle past 2).
  (D3) compute the FREE EDGE = max of support of the measure whose free cumulants are
       (kappa_1..kappa_R, 0,0,..) via the R-transform / numerical free-edge, compare to M(n).
  (D4) the SUFFICIENT LEMMA pre-screen: does  |kappa_r| <= n^{r/2}  hold for all r (the
       "no free cumulant beats semicircle scale")?  And does the free edge track 2 sqrt(n)
       NOT C sqrt(n log(q/n))?  (i.e. is semicircle the WRONG number -> route fails, OR
       does the THIN regime push the edge up?)
"""
import math
import numpy as np
from sympy import primerange
from fractions import Fraction
from functools import lru_cache

# ---------- subgroup + census ----------
def setup_mu(n, p):
    for a in range(2, p):
        z = pow(a, (p-1)//n, p)
        if pow(z, n, p) == 1 and pow(z, n//2, p) == p-1:
            return [pow(z, j, p) for j in range(n)]
    raise RuntimeError("no zeta")

def eta_all(n, p):
    mu = setup_mu(n, p)
    ind = np.zeros(p)
    for x in mu:
        ind[x] = 1.0
    F = np.fft.fft(ind)
    return np.conj(F)  # eta_b = sum_x e^{+2pi i b x/p}

def census_W(n, p, rmax):
    """W_r = #{r-tuples in mu_n summing to 0 mod p}, r=0..rmax, EXACT via DP over Z/p counts."""
    mu = setup_mu(n, p)
    # distribution of a single uniform-over-mu coordinate (counts, not prob)
    base = np.zeros(p, dtype=object)
    for x in mu:
        base[x] += 1
    # convolve r times (cyclic), read coefficient at 0
    cur = np.zeros(p, dtype=object); cur[0] = 1  # r=0
    W = [int(cur[0])]
    for _ in range(rmax):
        nxt = np.zeros(p, dtype=object)
        # cyclic convolution cur * base  (object dtype -> exact ints)
        # do it as: for each shift x in mu add cur shifted
        for x in mu:
            nxt += np.roll(cur, x)
        cur = nxt
        W.append(int(cur[0]))
    return W  # W[r]

# ---------- free cumulants from moments ----------
@lru_cache(maxsize=None)
def noncrossing_partitions(n):
    """Generate all non-crossing partitions of {0..n-1} as tuple of frozenset blocks."""
    if n == 0:
        return [()]
    res = []
    # the block containing 0: choose where it 'closes'. Standard recursion: 0 is grouped with
    # some subset {0=i_0<i_1<...<i_k} such that the arcs are non-crossing. Use: pick the next
    # element after 0 that is NOT in 0's block boundary... easier: brute force via known method.
    # Use recursion: block of 0 = {0, j1, ..., jk}; between consecutive chosen indices and after,
    # the gaps are independent NC partitions.
    elems = list(range(n))
    # choose the block of the last element n-1 connecting back; use classic: partition by the
    # element paired so that interval splits. We implement via: the block containing 0 splits
    # the rest into intervals.
    def rec(points):
        # points: sorted tuple of available labels
        if not points:
            yield ()
            return
        first = points[0]
        rest = points[1:]
        # choose subset S of rest to join 'first', such that S together with first forms a block
        # and the complementary arcs are NC. The NC condition: the block {first}+S, when we look at
        # gaps between consecutive block members (in cyclic/linear order over `points`), each gap is
        # filled by an independent NC partition of that contiguous interval.
        m = len(rest)
        for mask in range(1 << m):
            chosen = [rest[i] for i in range(m) if (mask >> i) & 1]
            block = (first,) + tuple(chosen)
            # gaps: between first and chosen[0], chosen[i],chosen[i+1], chosen[-1] and end
            boundaries = list(block)
            ok = True
            sub_intervals = []
            allpts = list(points)
            # positions in allpts
            pos = {v: i for i, v in enumerate(allpts)}
            bp = sorted(pos[v] for v in block)
            prev = bp[0]
            # interval after each block member up to next block member (exclusive)
            for k in range(len(bp)):
                start = bp[k] + 1
                end = bp[k+1] if k+1 < len(bp) else len(allpts)
                interval = tuple(allpts[start:end])
                if interval:
                    sub_intervals.append(interval)
            # recurse on each interval independently
            from itertools import product as iproduct
            sub_choices = [list(rec(iv)) for iv in sub_intervals]
            for combo in iproduct(*sub_choices) if sub_choices else [()]:
                blocks = [frozenset(block)]
                for c in combo:
                    blocks.extend(c)
                yield tuple(blocks)
    seen = set()
    out = []
    for part in rec(tuple(elems)):
        key = frozenset(part)
        if key not in seen:
            seen.add(key)
            out.append(part)
    return out

def catalan(k):
    return math.comb(2*k, k)//(k+1)

def free_cumulants_from_moments(m):
    """m[1..R] free moments -> kappa[1..R] free cumulants via NC-Moebius inversion.
       Uses kappa_r = sum_{pi in NC(r)} mu(0,pi)... we use the direct moment-cumulant:
       m_r = sum_{pi in NC(r)} prod_block kappa_{|block|}. Solve triangularly for kappa_r."""
    R = len(m) - 1
    kappa = [Fraction(0)] * (R+1)
    for r in range(1, R+1):
        nc = noncrossing_partitions(r)
        # m_r = kappa_r + (terms with all blocks size<r involving lower kappas)
        rhs = Fraction(m[r])
        contrib = Fraction(0)
        for part in nc:
            sizes = [len(b) for b in part]
            if len(part) == 1 and sizes[0] == r:
                continue  # this is the kappa_r term, coeff 1
            prod = Fraction(1)
            for s in sizes:
                prod *= kappa[s]
            contrib += prod
        kappa[r] = rhs - contrib
    return kappa

def free_edge_from_cumulants(kappa, R):
    """Numerically estimate the right edge of the measure with free cumulants kappa[1..R]
       (truncated, higher=0) via the R-transform: R(z)=sum kappa_{r} z^{r-1}, Cauchy transform
       G satisfies K(G)=z where K(w)=1/w + R(w). The edge = max x s.t. x is a critical value:
       x = K(w) with K'(w)=0, w real small. We solve K'(w)=0 for the largest valid x."""
    # K(w) = 1/w + sum_{r>=1} kappa_r w^{r-1}
    # K'(w) = -1/w^2 + sum_{r>=2} (r-1) kappa_r w^{r-2}
    ks = [float(k) for k in kappa]
    def K(w):
        return 1.0/w + sum(ks[r]*w**(r-1) for r in range(1, R+1))
    def Kp(w):
        return -1.0/w**2 + sum((r-1)*ks[r]*w**(r-2) for r in range(2, R+1))
    # scan w in (0, w_max) for sign change of Kp; edge = max K(w*) over real critical pts w>0
    best = None
    ws = np.linspace(1e-4, 2.0/math.sqrt(max(ks[2],1e-9)) if len(ks)>2 and ks[2]>0 else 5.0, 200000)
    prev = None; prevw = None
    crit = []
    for w in ws:
        val = Kp(w)
        if prev is not None and np.isfinite(val) and np.isfinite(prev) and prev*val < 0:
            crit.append(0.5*(w+prevw))
        prev = val; prevw = w
    edges = []
    for w in crit:
        try:
            edges.append(K(w))
        except Exception:
            pass
    if edges:
        return max(edges)
    return float('nan')

def run(n, p, R):
    eta = eta_all(n, p)
    q = p
    # real check
    imag_max = float(np.max(np.abs(eta.imag)))
    etareal = eta.real
    # nonzero freqs b!=0
    nz = etareal[1:]
    # exact moments via census
    W = census_W(n, p, R)
    # m_r over b!=0 : (1/(q-1)) (sum_b eta_b^r - eta_0^r) = (q*W_r - n^r)/(q-1)
    m = [Fraction(0)]*(R+1)
    for r in range(1, R+1):
        m[r] = Fraction(q*W[r] - n**r, q-1)
    # sanity vs numeric
    num_m2 = float(np.mean(nz**2))
    kappa = free_cumulants_from_moments(m)
    sqrtn = math.sqrt(n)
    M = float(np.max(np.abs(nz)))
    free_edge = free_edge_from_cumulants(kappa, R)
    print(f"\n=== n={n}  p={p}  beta=log_n(p)={math.log(p)/math.log(n):.2f}  q-1={q-1}  R={R} ===")
    print(f"  imag_max={imag_max:.2e} (real check)  m2 exact={float(m[2]):.4f} numeric={num_m2:.4f}  n-n^2/q={n-n*n/q:.4f}")
    print(f"  M(n)={M:.4f}  2*sqrt(n)={2*sqrtn:.4f}  sqrt(2 n ln(q/n))={math.sqrt(2*n*math.log(q/n)):.4f}")
    print(f"  free edge (truncated R={R}) = {free_edge:.4f}")
    print(f"  r : kappa_r            kappa_r/n^(r/2)  (free defect; 0=>semicircle)")
    for r in range(1, R+1):
        kr = float(kappa[r])
        print(f"  {r:2d}: {kr:>18.4f}   {kr/ (sqrtn**r):>12.5f}")
    # sufficient-lemma checks
    defects = [abs(float(kappa[r]))/(sqrtn**r) for r in range(3, R+1)]
    print(f"  SUFFICIENT-LEMMA |kappa_r| <= n^(r/2) for r>=3 ? "
          f"{'HOLDS' if all(d<=1.0 for d in defects) else 'FAILS'}  max defect={max(defects) if defects else 0:.4f}")
    return M, free_edge, kappa, sqrtn

if __name__ == "__main__":
    R = 8
    # thin 2-power subgroups
    cases = []
    for n in [4, 8, 16, 32]:
        ps = [p for p in primerange(2, 60000) if (p-1) % n == 0]
        # pick increasing beta = log_n p
        targets = []
        for p in ps:
            beta = math.log(p)/math.log(n)
            targets.append((beta, p))
        # pick a few betas spread out
        chosen = []
        for want in [2.5, 3.0, 3.5, 4.0]:
            best = min(targets, key=lambda t: abs(t[0]-want))
            if best[1] not in [c[1] for c in chosen]:
                chosen.append(best)
        for beta, p in chosen:
            cases.append((n, p))
    for n, p in cases:
        try:
            run(n, p, R)
        except Exception as e:
            print(f"n={n} p={p} ERR {e}")
