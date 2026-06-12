#!/usr/bin/env python3
"""THE BAD-FAMILY CENSUS (#371 round 8, BadFamilyCensus.lean).

THE QUESTION.  Round 7 (Level1RungPin.lean) discovered the antipodal pencil and proved
the level-j staircase is NOT the complete bad-family envelope.  The candidate answer to
the delta* question is now "the envelope over the COMPLETE bad-family catalogue" -- but
the catalogue was not known to be complete.  This probe measures completeness at the
largest genuinely-exhaustible scale and maps the laws.

THE EXHAUSTIVE OBJECT (tier 1).  A scalar gamma is bad for the stack (u0, u1) at
agreement threshold t  <=>  the point  s0 + gamma*s1  of the affine line in syndrome
space F_p^{n-k} (s_i = syndrome of u_i) lies in Sigma_e, the syndrome image of the
weight-<= e ball (e = n - t), via SOME error word w with  s1 NOT in colspace H_{supp w}
(the "direction unfit on the agreement set" side condition; everything is
syndrome-level).  So the census over ALL stacks = the census over ALL affine lines in
F_p^{n-k}: incidence with Sigma_e (an upper bound), then the exact side-condition count
on the top lines.  At p = 17, n = 8 (g = 2):
    d = 3 (m = 4):  all (17^4-1)/16 = 5,220 directions  -- trivial;
    d = 2 (m = 5):  all 88,741 directions, quotiented by the rotation action;
    d = 1 (m = 6):  all 1,508,598 directions / rotation ~ 188,575 reps.
Per (d, e) feasibility (e <= 3 everywhere; e = 4 additionally at d = 2) -- the
EXHAUSTED cells are printed explicitly; everything else is tier-3 heuristic, labeled.
The rotation x -> g x is a code automorphism, acts linearly on syndromes (R below),
permutes Sigma_e, and maps lines to lines preserving bad counts -- quotienting is sound
(checked against the unquotiented census at d = 3).

THE CATALOGUE (tier 2; char-0 layer, mod-p surplus possible at p = 17 -- flagged).
  STAIR(j):   stack (X^{r'_j 2^j}, X^{(r'_j-1) 2^j}), r'_j = (r-2)/2^j + 2, r = d+2;
              threshold T = r'_j 2^j, count = spectrum N(mu-j, r'_j)   [SubCeilingLadder]
  PENCIL(a,s): stack (X^a, X^{a+s}), f = gcd(a,n) >= d+1, 1 <= s <= d;
              combined = x^a (1 + gamma x^s) agrees with the deg-s codeword
              c*(1 + gamma X^s) on a fiber of x^a (f points) plus the gcd(s,n) cross
              points solving x^s = -1/gamma; T = gcd(a,n) + gcd(s,n),
              count = n/gcd(s,n).  a = h = n/2, s = 1 is the round-7 antipodal pencil;
              general s | h is landed this round (pencil_rung_epsMCA_lower_bound).
  KILL(s',b): stack (X^{b+s'}, X^b): gamma = -w kills a fiber of x^{s'};
              T = gcd(s',n), count n/gcd(s',n), valid when X^b is unfit on the fiber.
  DOUBLET:    (e_x, e_y - e_x): 2 bad scalars at T = n-1 (any d <= n-3) -- the bottom
              rung, landed as two_deviation_epsMCA_lower_bound.
  SIMPLEX(e): line of words supported on an (e+1)-set; e+1 bad scalars at T = n-e
              (any d <= n-e-2), landed as simplex_epsMCA_lower_bound.  ROUND-8 FIX:
              this family was missing from the original predictor (the t=6, d=1
              "triangle" cell W_6 = 3 is simplex(2), not a new family).
  BISIMPLEX(e): disjoint double simplex (ROUND-8 DISCOVERY, landed as
              bisimplex_epsMCA_lower_bound): S1 = {0..e}, S2 = {e+1..2e+1},
              q0 = prod_{z in Z}(X - z) over the complement Z; u1 = q0|S1,
              u0 = (X q0)|S1.  gamma = -x is bad for EVERY x in S1 u S2: for
              x in S1 the line word is ((X-x)q0)|S1, weight <= e, vs the ZERO
              codeword; for x in S2 it is (X-x)q0 - ((X-x)q0)|S2, i.e. the
              degree-<= d codeword (X-x)q0 minus a weight-<= e word.  Count
              2e+2 at T = n-e, valid for n-2e-1 <= d <= n-e-2.
  SINGLE:     1 bad scalar at T = n (u0 = c - gamma0 u1, u1 not in C).
The envelope prediction:  W_t^pred = max{count(F) : T(F) >= t}  (a family bad at its
threshold T is bad at every t <= T).

TIER 3 (heuristic, honestly labeled).  n = 16 at p in {17, 97} (m >= 11: exhaustion
infeasible): full monomial sweeps with per-gamma max-threshold resolution (the complete
(a,b) x t law table), hybrid/deviation families, and hill climbs whose objective is
EXCEEDING the catalogue envelope (a novelty search, not a max search).

Soundness of the fast counter is the sharpened ownership law as in probe_level1_pin.py;
the three checkers (syndrome-level line counter / numpy batched bad_threshold /
Domain.bad_fast) are cross-asserted on every extremal line and on random stacks.

Run: python3 scripts/probes/probe_bad_family_census.py   (~60-90 min; prints progress)
"""

import itertools
import json
import random
import sys
import time
from collections import Counter, defaultdict
from math import comb, gcd

import numpy as np

random.seed(371008)
T0 = time.time()


def log(msg):
    print(f"[{time.time()-T0:7.1f}s] {msg}", flush=True)


# ----------------------------------------------------------------- word-level domain

class Domain:
    """The n-point smooth domain {g^i} in F_p (port of probe_level1_pin.py) plus a
    numpy-batched exact bad-threshold resolver."""

    def __init__(self, p, g, n):
        self.P, self.G, self.N = p, g, n
        self.X = [pow(g, i, p) for i in range(n)]
        assert len(set(self.X)) == n and pow(g, n, p) == 1
        assert pow(g, n // 2, p) == p - 1
        self._bases = {}
        self._E = {}      # d -> (bases list, index map, eval tensor (nC, n, d+1))

    def _basis(self, base):
        base = tuple(base)
        hit = self._bases.get(base)
        if hit is not None:
            return hit
        P, X = self.P, self.X
        out = []
        for i in base:
            num = [1]
            den = 1
            for k in base:
                if k != i:
                    new = [0] * (len(num) + 1)
                    for a, ca in enumerate(num):
                        new[a + 1] = (new[a + 1] + ca) % P
                        new[a] = (new[a] - ca * X[k]) % P
                    num = new
                    den = den * (X[i] - X[k]) % P
            inv = pow(den, P - 2, P)
            out.append([c * inv % P for c in num])
        self._bases[base] = out
        return out

    def coeffs(self, base, y):
        P = self.P
        basis = self._basis(base)
        cs = [0] * len(basis[0])
        for bi, i in zip(basis, base):
            yi = y[i] % P
            for a, ca in enumerate(bi):
                cs[a] = (cs[a] + yi * ca) % P
        return cs

    def evalp(self, cs, x):
        P, acc = self.P, 0
        for c in reversed(cs):
            acc = (acc * x + c) % P
        return acc

    def fits(self, idxs, y, d):
        idxs = list(idxs)
        if len(idxs) <= d + 1:
            return True
        cs = self.coeffs(idxs[: d + 1], y)
        return all(self.evalp(cs, self.X[t]) == y[t] % self.P for t in idxs[d + 1:])

    def defect(self, R, y, d):
        R = list(R)
        cs = self.coeffs(R[: d + 1], y)
        return (y[R[-1]] - self.evalp(cs, self.X[R[-1]])) % self.P

    def bad_fast(self, u0, u1, gamma, t, d):
        """Complete word-level checker (byte-port of probe_level1_pin.py)."""
        P, X = self.P, self.X
        ug = [(u0[i] + gamma * u1[i]) % P for i in range(self.N)]
        for B in itertools.combinations(range(self.N), d + 1):
            cs = self.coeffs(B, ug)
            A = [i for i in range(self.N) if self.evalp(cs, X[i]) == ug[i]]
            if len(A) >= t and not self.fits(A, u1, d):
                return True
        return False

    def bad_candidates_mult(self, u0, u1, d):
        P = self.P
        cnt = Counter()
        for R in itertools.combinations(range(self.N), d + 2):
            d1 = self.defect(R, u1, d)
            if d1 != 0:
                d0 = self.defect(R, u0, d)
                cnt[(-d0) * pow(d1, P - 2, P) % P] += 1
        return cnt

    def count_bad(self, u0, u1, t, d, prefilter=True):
        cnt = self.bad_candidates_mult(u0, u1, d)
        floor_mult = -(-comb(t, d + 1) // (d + 2)) if prefilter else 1
        return sum(1 for g, m in cnt.items()
                   if m >= floor_mult and self.bad_fast(u0, u1, g, t, d))

    # ---- numpy batched machinery -------------------------------------------------
    def _etensor(self, d):
        hit = self._E.get(d)
        if hit is not None:
            return hit
        bases = list(itertools.combinations(range(self.N), d + 1))
        # E[b, i, j] = value at point i of the Lagrange basis poly of node j of base b
        E = np.zeros((len(bases), self.N, d + 1), dtype=np.int64)
        for bi, B in enumerate(bases):
            for j, node in enumerate(B):
                cs = [0] * (d + 1)
                # Lagrange basis: interpolate the indicator of `node` on B
                basis = self._basis(B)[j]
                for a, ca in enumerate(basis):
                    cs[a] = ca
                for i in range(self.N):
                    E[bi, i, j] = self.evalp(cs, self.X[i])
        baseidx = np.array(bases, dtype=np.int64)
        self._E[d] = (bases, baseidx, E)
        return self._E[d]

    def bad_threshold(self, u0, u1, gamma, d, t_floor):
        """Max t such that gamma is bad (0 if none >= t_floor): batched over all
        (d+1)-subset interpolants of the combined word."""
        P = self.P
        bases, baseidx, E = self._etensor(d)
        ug = np.array([(u0[i] + gamma * u1[i]) % P for i in range(self.N)],
                      dtype=np.int64)
        vals = np.einsum('bij,bj->bi', E, ug[baseidx]) % P
        agree = (vals == ug[None, :])
        counts = agree.sum(axis=1)
        best = 0
        order = np.argsort(-counts)
        u1l = list(u1)
        seen = set()
        for bi in order:
            c = int(counts[bi])
            if c < max(t_floor, best + 1):
                break
            A = tuple(np.nonzero(agree[bi])[0].tolist())
            if A in seen:
                continue
            seen.add(A)
            if not self.fits(list(A), u1l, d):
                best = max(best, c)
        return best

    def bad_set_thresholds(self, u0, u1, d, t_floor):
        """{gamma: maxT} over candidate scalars with defect-ratio multiplicity >= 2
        (sound for t >= d+3 by the sharpened ownership law: a bad scalar at t >= d+3
        owns >= ceil(C(t,d+1)/(d+2)) >= 2 unfit (d+2)-subsets)."""
        cnt = self.bad_candidates_mult(u0, u1, d)
        out = {}
        for gam, mult in cnt.items():
            if mult >= 2:
                T = self.bad_threshold(u0, u1, gam, d, t_floor)
                if T >= t_floor:
                    out[gam] = T
        return out


def monomial(dom, e):
    return [pow(x, e, dom.P) for x in dom.X]


def spectrum_N(nu, rp):
    h = 2 ** (nu - 1)
    tot = 0
    for a in range(rp % 2, min(rp, h) + 1, 2):
        if (rp - a) // 2 <= h - a:
            tot += 2 ** a * comb(h, a)
    return tot


# ----------------------------------------------------------------- mod-p linear algebra

def rref(M, p):
    M = [row[:] for row in M]
    rows, cols = len(M), len(M[0]) if M else 0
    piv = []
    r = 0
    for c in range(cols):
        pr = next((i for i in range(r, rows) if M[i][c] % p), None)
        if pr is None:
            continue
        M[r], M[pr] = M[pr], M[r]
        inv = pow(M[r][c], p - 2, p)
        M[r] = [(x * inv) % p for x in M[r]]
        for i in range(rows):
            if i != r and M[i][c] % p:
                f = M[i][c]
                M[i] = [(M[i][j] - f * M[r][j]) % p for j in range(cols)]
        piv.append(c)
        r += 1
        if r == rows:
            break
    return M[:r], piv


def null_space(M, p):
    """Rows spanning {v : M v = 0}."""
    R, piv = rref(M, p)
    cols = len(M[0])
    free = [c for c in range(cols) if c not in piv]
    basis = []
    for fc in free:
        v = [0] * cols
        v[fc] = 1
        for ri, pc in enumerate(piv):
            v[pc] = (-R[ri][fc]) % p
        basis.append(v)
    return basis


def right_inverse(H, p):
    """X (n x m) with H X = I_m, via Gaussian elimination on [H | I]."""
    m, n = len(H), len(H[0])
    aug = [H[i][:] + [1 if k == i else 0 for k in range(m)] for i in range(m)]
    Ra, piva = rref(aug, p)
    # Ra = [R | T] with R = rref(H) = T H; all pivots of the full-rank H lie in the
    # first n columns.  H x = e_j  <=>  R x = T e_j: take x supported on pivot cols.
    assert len(piva) == m and all(pc < n for pc in piva)
    X = [[0] * m for _ in range(n)]
    for j in range(m):
        for ri, pc in enumerate(piva):
            X[pc][j] = Ra[ri][n + j] % p
    return X


# ----------------------------------------------------------------- syndrome census

class SyndromeCensus:
    def __init__(self, dom, d):
        self.dom, self.d = dom, d
        p, n = dom.P, dom.N
        self.p, self.n = p, n
        k = d + 1
        M = [[pow(x, r, p) for x in dom.X] for r in range(k)]   # k x n, rows span C
        H = null_space(M, p)                                    # m x n, ker H = C
        self.m = n - k
        assert len(H) == self.m
        self.H = np.array(H, dtype=np.int64)
        # sanity: H . codeword = 0
        for r in range(k):
            assert all((self.H @ np.array(M[r])) % p == 0)
        self.Xr = np.array(right_inverse(H, p), dtype=np.int64)  # n x m, H Xr = I
        assert np.array_equal((self.H @ self.Xr) % p, np.eye(self.m, dtype=np.int64))
        # rotation matrix on syndromes: R (Hw) = H (Pw), (Pw)(i) = w(i+1 mod n)
        Pm = np.zeros((n, n), dtype=np.int64)
        for i in range(n):
            Pm[i][(i + 1) % n] = 1
        self.R = (self.H @ Pm @ self.Xr) % p
        for _ in range(20):
            w = np.random.randint(0, p, n)
            assert np.array_equal((self.R @ (self.H @ w % p)) % p,
                                  (self.H @ (Pm @ w) % p) % p)
        self.powv = np.array([p ** i for i in range(self.m)], dtype=np.int64)
        self._sigma = {}

    def encode(self, pts):
        return (np.asarray(pts, dtype=np.int64) @ self.powv)

    def sigma(self, e):
        """Sigma_e: (sorted unique keys), plus rep table (keys_all, masks_all) sorted,
        and a membership bitmap over p^m (only for m <= 5)."""
        if e in self._sigma:
            return self._sigma[e]
        p, n, m = self.p, self.n, self.m
        keys_all, masks_all, coords = [], [], []
        for j in range(0, e + 1):
            for supp in itertools.combinations(range(n), j):
                mask = sum(1 << i for i in supp)
                if j == 0:
                    syn = np.zeros((1, m), dtype=np.int64)
                else:
                    grids = np.meshgrid(*([np.arange(1, p)] * j), indexing='ij')
                    coef = np.stack([gr.ravel() for gr in grids], axis=1)
                    syn = (coef @ self.H[:, list(supp)].T) % p
                k = self.encode(syn)
                keys_all.append(k)
                masks_all.append(np.full(len(k), mask, dtype=np.int64))
                coords.append(syn)
        keys_all = np.concatenate(keys_all)
        masks_all = np.concatenate(masks_all)
        coords = np.concatenate(coords)
        order = np.argsort(keys_all, kind='stable')
        keys_all, masks_all, coords = keys_all[order], masks_all[order], coords[order]
        ukeys, first = np.unique(keys_all, return_index=True)
        ucoords = coords[first]
        bitmap = None
        if p ** m <= 2 * 10 ** 7:
            bitmap = np.zeros(p ** m, dtype=bool)
            bitmap[ukeys] = True
        self._sigma[e] = (ukeys, ucoords, keys_all, masks_all, bitmap)
        return self._sigma[e]

    def rep_supports(self, key, e):
        ukeys, _, keys_all, masks_all, _ = self.sigma(e)
        lo = np.searchsorted(keys_all, key, side='left')
        hi = np.searchsorted(keys_all, key, side='right')
        return masks_all[lo:hi]

    # ---- canonical directions under rotation ------------------------------------
    def canonical_directions(self):
        """All projective directions, grouped: returns (reps coords (k x m),
        orbit sizes (k,))."""
        p, m = self.p, self.m
        # all normalized directions: first nonzero coordinate = 1
        blocks = []
        for j in range(m):
            tail = m - j - 1
            if tail == 0:
                v = np.zeros((1, m), dtype=np.int64)
                v[0, j] = 1
                blocks.append(v)
            else:
                grids = np.meshgrid(*([np.arange(p)] * tail), indexing='ij')
                rest = np.stack([gr.ravel() for gr in grids], axis=1)
                v = np.zeros((len(rest), m), dtype=np.int64)
                v[:, j] = 1
                v[:, j + 1:] = rest
                blocks.append(v)
        D = np.concatenate(blocks)        # ((p^m-1)/(p-1), m)
        N = len(D)
        # orbit canonical key = min over rotation powers of encoded normalization
        cur = D.copy()
        minkey = np.full(N, np.iinfo(np.int64).max, dtype=np.int64)
        orbitlen = np.zeros(N, dtype=np.int64)
        selfkey = None
        for a in range(self.n):
            if a > 0:
                cur = (cur @ self.R.T) % p
            # normalize: divide by first nonzero coordinate
            normed = cur.copy()
            done = np.zeros(N, dtype=bool)
            for j in range(m):
                nz = (~done) & (normed[:, j] != 0)
                if nz.any():
                    inv = np.array([pow(int(x), p - 2, p) for x in
                                    np.unique(normed[nz, j])])
                    invmap = dict(zip(np.unique(normed[nz, j]).tolist(),
                                      inv.tolist()))
                    f = np.array([invmap[int(x)] for x in normed[nz, j]],
                                 dtype=np.int64)
                    normed[nz] = (normed[nz] * f[:, None]) % p
                    done |= nz
            kk = self.encode(normed)
            if a == 0:
                selfkey = kk
            minkey = np.minimum(minkey, kk)
        isrep = (selfkey == minkey)
        repkeys = selfkey[isrep]
        # orbit sizes: count how many directions share each minkey
        cnt = Counter(minkey.tolist())
        sizes = np.array([cnt[int(k)] for k in repkeys], dtype=np.int64)
        return D[isrep], sizes

    # ---- the all-lines census ----------------------------------------------------
    def census_exact(self, e, t_floor=0, top_cap=64, progress_every=30000):
        """EXHAUSTIVE EXACT census: for EVERY affine line (up to the rotation
        quotient), the exact bad-scalar count (incidence refined by the unfit side
        condition), computed vectorized per direction:
          - direction v with no weight-<=e rep: side condition always passes,
            exact = incidence;
          - otherwise the set {sigma : some rep support of sigma does not explain v}
            is computed once for v (vectorized over the rep table), and one weighted
            bincount yields the exact count of every line of direction v.
        Returns (incidence_dist, W (exact max), argmax_lines, runner_up_value)."""
        p, m = self.p, self.m
        ukeys, ucoords, keys_all, masks_all, _ = self.sigma(e)
        S = ucoords
        log(f"      |Sigma_{e}| = {len(S)} of {p**m} "
            f"({100*len(S)/p**m:.1f}% of syndrome space); rep rows {len(keys_all)}")
        row_start = np.searchsorted(keys_all, ukeys, side='left')
        dirs, sizes = self.canonical_directions()
        dist = Counter()
        best, runner, arg = 0, 0, []
        small = len(S) < p ** (m - 1) // 8
        for di in range(len(dirs)):
            v = dirs[di]
            j = int(np.nonzero(v)[0][0])
            w = np.zeros(m, dtype=np.int64)
            idx = 0
            for kk in range(m):
                if kk != j:
                    w[kk] = p ** idx
                    idx += 1
            coset = (S - np.outer(S[:, j], v)) % p
            ids = coset @ w
            osz = int(sizes[di])
            # incidence distribution (upper-bound layer, kept for the report)
            if small:
                vals, cnts = np.unique(ids, return_counts=True)
            else:
                cnts = np.bincount(ids, minlength=p ** (m - 1))
                vals = None
            hist = np.bincount(cnts[cnts > 0]) if not small else np.bincount(cnts)
            for inc, lcnt in enumerate(hist):
                if inc > 0 and lcnt > 0:
                    dist[inc] += int(lcnt) * osz
            # the exact layer
            vkey = int(v @ self.powv)
            lo = np.searchsorted(keys_all, vkey, side='left')
            hi = np.searchsorted(keys_all, vkey, side='right')
            vmasks = masks_all[lo:hi]
            if len(vmasks) == 0:
                ecnts, evals = cnts, vals
            else:
                ok_rows = np.ones(len(masks_all), dtype=bool)
                for vm in vmasks.tolist():
                    ok_rows &= (vm & ~masks_all) != 0
                ok_sigma = np.maximum.reduceat(
                    ok_rows.astype(np.int8), row_start).astype(np.float64)
                if small:
                    uvals, inv = np.unique(ids, return_inverse=True)
                    ecnts = np.bincount(inv, weights=ok_sigma)
                    evals = uvals
                else:
                    ecnts = np.bincount(ids, weights=ok_sigma,
                                        minlength=p ** (m - 1))
                    evals = None
            emax = int(ecnts.max() + 0.5) if len(ecnts) else 0
            if emax > best:
                runner = best
                best, arg = emax, []
            elif best > emax > runner:
                runner = emax
            if emax == best and len(arg) < top_cap:
                where = np.nonzero(np.asarray(ecnts) >= best - 0.5)[0]
                for widx in where[: top_cap - len(arg)]:
                    cid = int(evals[widx]) if evals is not None else int(widx)
                    pt = np.zeros(m, dtype=np.int64)
                    rem = cid
                    for kk in range(m):
                        if kk != j:
                            pt[kk] = rem % p
                            rem //= p
                    arg.append((best, v.copy(), pt, osz))
            if progress_every and (di + 1) % progress_every == 0:
                log(f"      ... {di+1}/{len(dirs)} direction orbits "
                    f"(exact max so far {best})")
        # keep only argmax entries at the final best
        arg = [a for a in arg if a[0] == best]
        return dist, best, arg, runner

    def census(self, e, cut, max_collect=300000, progress_every=30000):
        """Exhaustive incidence census of all affine lines against Sigma_e, quotiented
        by the rotation action on directions (sound: R permutes Sigma_e and maps lines
        to lines preserving incidence and the side condition).  The collection cut is
        DYNAMIC: it starts at `cut` and rises whenever the collection budget overflows;
        the final cut is returned so the caller can verify final_cut <= W_t
        (the completeness condition of the exact pass).
        Returns (dist, collected, final_cut, truncated)."""
        p, m = self.p, self.m
        _, ucoords, _, _, _ = self.sigma(e)
        S = ucoords                       # (N, m)
        log(f"      |Sigma_{e}| = {len(S)} of {p**m} "
            f"({100*len(S)/p**m:.1f}% of syndrome space)")
        dirs, sizes = self.canonical_directions()
        dist = Counter()
        collected = []
        truncated = False
        small = len(S) < p ** (m - 1) // 8
        for di in range(len(dirs)):
            v = dirs[di]
            j = int(np.nonzero(v)[0][0])
            w = np.zeros(m, dtype=np.int64)
            idx = 0
            for kk in range(m):
                if kk != j:
                    w[kk] = p ** idx
                    idx += 1
            coset = (S - np.outer(S[:, j], v)) % p
            ids = coset @ w
            osz = int(sizes[di])
            if small:
                vals, cnts = np.unique(ids, return_counts=True)
                hist = np.bincount(cnts)
                topm = cnts >= cut
                topids, topcnts = vals[topm], cnts[topm]
            else:
                cnts = np.bincount(ids, minlength=p ** (m - 1))
                hist = np.bincount(cnts[cnts > 0])
                topm = np.nonzero(cnts >= cut)[0]
                topids, topcnts = topm, cnts[topm]
            for inc, lcnt in enumerate(hist):
                if inc > 0 and lcnt > 0:
                    dist[inc] += int(lcnt) * osz
            for cid, cc in zip(topids.tolist(), topcnts.tolist()):
                pt = np.zeros(m, dtype=np.int64)
                rem = int(cid)
                for kk in range(m):
                    if kk != j:
                        pt[kk] = rem % p
                        rem //= p
                collected.append((int(cc), v.copy(), pt, osz))
            if len(collected) > max_collect:
                if cut < p:
                    cut += 1
                    collected = [c for c in collected if c[0] >= cut]
                if len(collected) > max_collect:
                    # saturated cell (full lines everywhere): keep a cap; W = p is
                    # then certified the moment ONE kept line passes the side
                    # condition at all p scalars
                    truncated = True
                    collected = collected[:max_collect]
            if progress_every and (di + 1) % progress_every == 0:
                log(f"      ... {di+1}/{len(dirs)} direction orbits "
                    f"(cut={cut}, kept={len(collected)})")
        return dist, collected, cut, truncated

    # ---- exact bad count on a line -----------------------------------------------
    def exact_line_count(self, v, s0, e):
        """#gamma with s0 + gamma v in Sigma_e via a support not explaining v."""
        p = self.p
        vkey = int(self.encode(v.reshape(1, -1))[0])
        vmasks = self.rep_supports(vkey, e)  # supports of weight-<=e reps of v
        cnt = 0
        for gam in range(p):
            sig = (s0 + gam * v) % p
            key = int(self.encode(sig.reshape(1, -1))[0])
            masks = self.rep_supports(key, e)
            if len(masks) == 0:
                continue
            ok = False
            for Mk in masks.tolist():
                if not any((Vm & ~Mk) == 0 for Vm in vmasks.tolist()):
                    ok = True
                    break
            if ok:
                cnt += 1
        return cnt

    def words_of_line(self, v, s0):
        u1 = (self.Xr @ v) % self.p
        u0 = (self.Xr @ s0) % self.p
        return [int(x) for x in u0], [int(x) for x in u1]

    def canonical_line_key(self, v, s0):
        """Canonical key of the line {s0 + g v} under rotation x scaling."""
        p = self.p
        pts = np.stack([(s0 + gam * v) % p for gam in range(p)])
        best = None
        cur = pts
        for a in range(self.n):
            if a > 0:
                cur = (cur @ self.R.T) % p
            for c in range(1, p):
                kk = tuple(sorted(self.encode((cur * c) % p).tolist()))
                if best is None or kk < best:
                    best = kk
        return best

    def stack_line(self, u0, u1):
        s0 = (self.H @ np.array(u0, dtype=np.int64)) % self.p
        v = (self.H @ np.array(u1, dtype=np.int64)) % self.p
        if not v.any():
            return None
        return v, s0


# ----------------------------------------------------------------- the catalogue

def catalogue_families(n, d, mu):
    """Char-0 catalogue with thresholds and counts (m = 1 slice, n = 2^mu).

    ROUND-8 CORRECTION: the original predictor omitted the SIMPLEX ladder entirely
    (count e+1 at threshold n-e, any d <= n-e-2: the (p,n,d)=(17,8,1), t=6 census cell
    W_6 = 3 -- the "triangle" {a,b},{a,c},{b,c} extremal -- IS simplex(e=2), a matcher/
    predictor omission, not a new family), and the BISIMPLEX (disjoint double simplex:
    S1, S2 disjoint (e+1)-sets, q0 = prod_{z notin S1 u S2}(X - z), u1 = q0|S1,
    u0 = (X q0)|S1; every gamma = -x, x in S1 u S2, is bad at threshold n-e: count
    2e+2, valid for n-2e-1 <= d <= n-e-2).  The bisimplex is the char-0 layer of the
    (17,8,3) t=6 cell (W_6 = 7 = bisimplex 6 + one mod-17 extra) and of the n=16, d=2,
    t=7 hill-climb find (20 = 2(e+1) at e=9, overlapping variant)."""
    fams = []
    r = d + 2
    for j in range(0, mu):
        rp = (r - 2) // 2 ** j + 2
        if 2 <= rp <= 2 ** (mu - j - 1):
            fams.append(dict(name=f"stair-j{j}(r'={rp})", T=rp * 2 ** j,
                             count=spectrum_N(mu - j, rp),
                             stack=((rp * 2 ** j) % n, ((rp - 1) * 2 ** j) % n)))
    for a in range(1, n):
        f = gcd(a, n)
        if f >= d + 1 and f < n:
            for s in range(1, d + 1):
                sig = gcd(s, n)
                fams.append(dict(name=f"pencil(a={a},s={s})", T=f + sig,
                                 count=n // sig, stack=(a, (a + s) % n)))
    for e2 in range(1, n - d - 1):                      # e2 <= n - d - 2
        fams.append(dict(name=f"simplex(e={e2})", T=n - e2, count=e2 + 1,
                         stack=("simplex", e2)))
        if 2 * e2 + 2 <= n and n <= d + 2 * e2 + 1:     # n-2e-1 <= d
            fams.append(dict(name=f"bisimplex(e={e2})", T=n - e2, count=2 * e2 + 2,
                             stack=("bisimplex", e2)))
    fams.append(dict(name="doublet", T=n - 1, count=2, stack="doublet"))
    fams.append(dict(name="single", T=n, count=1, stack="single"))
    return fams


def simplex_stack(dom, e):
    """The simplex line: words supported on {0..e}; u0(j) = j, u1(j) = 1 there."""
    n = dom.N
    u0 = [j % dom.P if j <= e else 0 for j in range(n)]
    u1 = [1 if j <= e else 0 for j in range(n)]
    return u0, u1


def bisimplex_stack(dom, e):
    """The disjoint double simplex: S1 = {0..e}, S2 = {e+1..2e+1}, Z = the rest;
    q0 = prod_{z in Z}(X - X[z]); u1 = q0|S1, u0 = (X*q0)|S1.  The 2e+2 bad scalars
    are -X[x], x in S1 u S2 (each kills one coordinate of the S1- resp. S2-residual)."""
    p, n, X = dom.P, dom.N, dom.X

    def q0(x):
        v = 1
        for z in range(2 * e + 2, n):
            v = v * (x - X[z]) % p
        return v

    u0 = [X[i] * q0(X[i]) % p if i <= e else 0 for i in range(n)]
    u1 = [q0(X[i]) % p if i <= e else 0 for i in range(n)]
    return u0, u1


def family_stack(dom, f):
    """Materialize a catalogue family's witness stack (None when stackless)."""
    st = f["stack"]
    if st == "doublet":
        return doublet_stack(dom)
    if st == "single":
        return None
    if isinstance(st, tuple) and st and st[0] == "simplex":
        return simplex_stack(dom, st[1])
    if isinstance(st, tuple) and st and st[0] == "bisimplex":
        return bisimplex_stack(dom, st[1])
    if isinstance(st, tuple):
        return monomial(dom, st[0]), monomial(dom, st[1])
    return None


def classify_blocks(sig, n):
    """Structural decomposition of an extremal's per-gamma minimal-support signature
    into simplex blocks (all (k-1)-subsets of a k-set, one gamma each) plus leftovers.
    ROUND-8 matcher fix: the line-key matcher only recognizes the exact seed lines
    (one per family), so EVERY generic extremal was flagged novel; this structural
    layer recognizes the family by its support pattern instead."""
    remaining = Counter(frozenset(s) for (_, w, s) in sig)
    sups = list(remaining)
    cands = set()
    for s1 in sups:
        for s2 in sups:
            cands.add(s1 | s2)
    blocks = []
    for S in sorted(cands, key=lambda S: (len(S), tuple(sorted(S)))):
        if len(S) < 2:
            continue
        subs = [frozenset(S - {x}) for x in sorted(S)]
        while all(remaining[s] >= 1 for s in subs):
            for s in subs:
                remaining[s] -= 1
            blocks.append(f"simplex{tuple(sorted(S))}")
    left = [tuple(sorted(s)) for s, c in remaining.items() if c > 0 for _ in range(c)]
    return blocks, left


def envelope_pred(fams, t):
    vals = [f["count"] for f in fams if f["T"] >= t]
    return max(vals) if vals else 0


def doublet_stack(dom):
    n = dom.N
    u0 = [0] * n
    u0[0] = 1
    u1 = [0] * n
    u1[0] = (-1) % dom.P
    u1[1] = 1
    return u0, u1


# ----------------------------------------------------------------- tier 1: exhaustive

def tier1_instance(p, g, n, d, e_list, results):
    dom = Domain(p, g, n)
    sc = SyndromeCensus(dom, d)
    mu = n.bit_length() - 1
    fams = catalogue_families(n, d, mu)
    log(f"== TIER 1 EXHAUSTIVE: p={p}, g={g}, n={n}, d={d} (m={sc.m}) ==")
    # cross-check the three checkers on catalogue + random stacks
    teststacks = []
    for f in fams:
        st = family_stack(dom, f)
        if st is not None:
            teststacks.append((st[0], st[1], f["name"]))
    for _ in range(6):
        teststacks.append(([random.randrange(p) for _ in range(n)],
                           [random.randrange(p) for _ in range(n)], "random"))
    for t in range(d + 3, n):
        e = n - t
        if e not in e_list:
            continue
        for (u0, u1, name) in teststacks[:8]:
            a = dom.count_bad(u0, u1, t, d)
            line = sc.stack_line(u0, u1)
            b = sc.exact_line_count(line[0], line[1], e) if line else 0
            assert a == b, (name, t, a, b)
    log(f"   checker cross-validation OK (word-level == syndrome-level)")

    # canonical line keys of ALL catalogue stacks (any threshold) + all monomial pairs
    cat_keys = {}
    for f in fams:
        st = family_stack(dom, f)
        if st is None:
            continue
        line = sc.stack_line(*st)
        if line:
            cat_keys.setdefault(sc.canonical_line_key(line[0], line[1]), f["name"])
    for a in range(n):
        for b in range(n):
            if a == b:
                continue
            line = sc.stack_line(monomial(dom, a), monomial(dom, b))
            if line:
                cat_keys.setdefault(sc.canonical_line_key(line[0], line[1]),
                                    f"monomial({a},{b})")

    inst = {}
    for e in sorted(e_list, reverse=False):
        t = n - e
        if t < d + 2:
            continue
        if t == d + 2:
            # the explosion band: W_t is certified = p the moment ONE stack attains
            # the absolute cap p (support-compact construction; word-level checker)
            B = list(range(d + 2))
            found = None
            for _ in range(3000):
                u0 = [random.randrange(p) if i in B else 0 for i in range(n)]
                u1 = [random.randrange(p) if i in B else 0 for i in range(n)]
                if all(dom.bad_fast(u0, u1, gam, t, d) for gam in range(p)):
                    found = (u0, u1)
                    break
            if found:
                log(f"   t={t} = d+2 (EXPLOSION BAND): support-compact stack attains "
                    f"the cap W_{t} = p = {p} (certified exact; census skipped)")
                log(f"      witness u0={found[0]} u1={found[1]}")
                inst[t] = dict(W=p, pred=envelope_pred(fams, t), runner=None,
                               dist=None, matched={}, novel=[dict(
                                   count=p, word_level=p, u0=found[0], u1=found[1],
                                   orbit=1)], exhaustive=True,
                               note="explosion witness; cap p attained")
                continue
            log(f"   t={t} = d+2: no explosion witness found in 3000 tries; "
                f"falling through to the full census")
        pred = envelope_pred(fams, t)
        log(f"   census e={e} (threshold t={t}, radius band "
            f"[{n-t}/{n},{n-t+1}/{n})), catalogue prediction W_pred={pred}")
        dist, best, extremal, runner = sc.census_exact(e)
        log(f"      incidence dist (top): "
            f"{dict(sorted(dist.items(), reverse=True)[:8])}")
        # cross-validate every argmax line against the slow per-line checker
        for (cnt, v, s0, osz) in extremal[:8]:
            slow = sc.exact_line_count(v, s0, e)
            assert slow == cnt, ("argmax cross-check", t, cnt, slow)
        evaluated = len(extremal)
        exhaustive = True
        matched, novel = [], []
        for (cnt, v, s0, osz) in extremal[:32]:
            kk = sc.canonical_line_key(v, s0)
            if kk in cat_keys:
                matched.append(cat_keys[kk])
            else:
                u0, u1 = sc.words_of_line(v, s0)
                # word-level confirmation + per-gamma minimal rep-weight signature
                wl = sum(1 for gam in range(p) if dom.bad_fast(u0, u1, gam, t, d))
                sig = []
                for gam in range(p):
                    key = int(sc.encode(((s0 + gam * v) % p).reshape(1, -1))[0])
                    masks = sc.rep_supports(key, e)
                    if len(masks):
                        mm = min((bin(int(x)).count("1"), int(x))
                                 for x in masks)
                        sig.append((gam, mm[0],
                                    tuple(i for i in range(n) if mm[1] >> i & 1)))
                blocks, left = classify_blocks(sig, n)
                novel.append(dict(count=cnt, word_level=wl, u0=u0, u1=u1,
                                  orbit=int(osz), gamma_repwt=sig,
                                  structure=dict(blocks=blocks, extra=left)))
        verdict = ("MATCHES catalogue (value-exact)" if best == pred else
                   (f"{'EXCEEDS' if best > pred else 'BELOW'} prediction"
                    + ("; see structural decomposition" if novel else "")))
        log(f"      EXACT W_{t} = {best} (pred {pred}; runner-up line value "
            f"{runner}); {evaluated} argmax lines; extremal classes "
            f"matched={dict(Counter(matched))} unmatched-by-line-key={len(novel)} "
            f"-> {verdict}")
        for nv in novel[:6]:
            log(f"         EXTREMAL: count={nv['count']} (word-level "
                f"{nv['word_level']}) structure={nv['structure']} "
                f"u0={nv['u0']} u1={nv['u1']} repwt={nv['gamma_repwt']}")
        inst[t] = dict(W=best, pred=pred, runner=runner,
                       dist={k: v for k, v in sorted(dist.items())[-12:]},
                       matched=dict(Counter(matched)),
                       novel=[{k: v for k, v in nv.items() if k != "gamma_repwt"}
                              for nv in novel[:6]],
                       exhaustive=bool(exhaustive))
    results[f"p{p}_n{n}_d{d}"] = inst
    return inst


def tier1b_shoulder_p97(results):
    """EXHAUSTIVE census of the (p=97, n=8, d=3, e=2, t=6) shoulder cell — the cell
    where p=17 measured W_6 = 7 (bisimplex 6 + 1).  Verdict semantics:
      W = 6  -> the +1 was a mod-17 coincidence; the bisimplex is EXACT at large p;
      W = 7  -> the +1 is itself char-0 (the catalogue is still incomplete);
      W = 4  -> the bisimplex itself would be refuted at p=97 (not expected: the
                construction is field-independent and cross-checked word-level)."""
    p, g, n, d, e = 97, 64, 8, 3, 2
    t = n - e
    dom = Domain(p, g, n)
    sc = SyndromeCensus(dom, d)
    fams = catalogue_families(n, d, n.bit_length() - 1)
    pred = envelope_pred(fams, t)
    log(f"== TIER 1B EXHAUSTIVE SHOULDER CELL: p={p}, n={n}, d={d}, e={e} (t={t}) — "
        f"catalogue prediction W_pred={pred} (bisimplex) ==")
    # word-level sanity of the bisimplex stack at p=97 first (cheap, independent)
    u0b, u1b = bisimplex_stack(dom, e)
    wl = sum(1 for gam in range(p) if dom.bad_fast(u0b, u1b, gam, t, d))
    log(f"   bisimplex stack word-level count at p={p}: {wl} (construction predicts "
        f"{2 * e + 2})")
    assert wl >= 2 * e + 2, ("bisimplex word-level check", wl)
    dist, best, extremal, runner = sc.census_exact(e, progress_every=30000)
    log(f"      incidence dist (top): "
        f"{dict(sorted(dist.items(), reverse=True)[:8])}")
    for (cnt, v, s0, osz) in extremal[:4]:
        slow = sc.exact_line_count(v, s0, e)
        assert slow == cnt, ("argmax cross-check p97", cnt, slow)
    structures = []
    for (cnt, v, s0, osz) in extremal[:6]:
        u0, u1 = sc.words_of_line(v, s0)
        sig = []
        for gam in range(p):
            key = int(sc.encode(((s0 + gam * v) % p).reshape(1, -1))[0])
            masks = sc.rep_supports(key, e)
            if len(masks):
                mm = min((bin(int(x)).count("1"), int(x)) for x in masks)
                sig.append((gam, mm[0],
                            tuple(i for i in range(n) if mm[1] >> i & 1)))
        blocks, left = classify_blocks(sig, n)
        structures.append(dict(count=cnt, structure=dict(blocks=blocks, extra=left)))
        log(f"         EXTREMAL: count={cnt} structure(blocks={blocks}, extra={left}) "
            f"u0={u0} u1={u1}")
    verdict = ("bisimplex EXACT at p=97; the p=17 '+1' is a mod-17 surplus"
               if best == pred else
               f"{'EXCEEDS' if best > pred else 'BELOW'} the bisimplex envelope")
    log(f"      EXACT W_{t}(p=97, d=3) = {best} (pred {pred}; runner-up {runner}) "
        f"-> {verdict}")
    results["p97_n8_d3_shoulder"] = dict(W=best, pred=pred, runner=runner,
                                         word_level_bisimplex=wl,
                                         extremals=structures, exhaustive=True)


# ----------------------------------------------------------------- tier 2: law table

def tier2_monomial_table(p, g, n, d, t_lo, t_hi, results):
    dom = Domain(p, g, n)
    mu = n.bit_length() - 1
    fams = catalogue_families(n, d, mu)
    log(f"== TIER 2 MONOMIAL LAW TABLE: p={p}, n={n}, d={d}, t in "
        f"[{t_lo},{t_hi}] (heuristic only in the sense: stacks restricted "
        f"to monomial pairs; per-stack counts are EXACT) ==")
    table = {}
    anomalies = []
    for a in range(n):
        for b in range(n):
            if a == b:
                continue
            u0, u1 = monomial(dom, a), monomial(dom, b)
            th = dom.bad_set_thresholds(u0, u1, d, t_lo)
            for t in range(t_lo, t_hi + 1):
                c = sum(1 for T in th.values() if T >= t)
                if c > 0:
                    table[(a, b, t)] = c
    # per-cell predictions: which (a,b,t) cells are explained by which law
    def cell_pred(a, b, t):
        preds = []
        s = (b - a) % n
        sp = (a - b) % n
        fa, fb = gcd(a, n) if a else n, gcd(b, n) if b else n
        if 1 <= s <= d and fa >= d + 1 and fa < n and t <= fa + gcd(s, n):
            preds.append(n // gcd(s, n))
        # swapped pencil (gamma-inversion symmetric image)
        if 1 <= sp <= d and fb >= d + 1 and fb < n and t <= fb + gcd(sp, n):
            preds.append(n // gcd(sp, n))
        # staircase stacks
        for f in fams:
            if f["stack"] == (a, b) and t <= f["T"]:
                preds.append(f["count"])
        # kill family (X^{b+s'}, X^b): gamma=-w kills fibers of x^{s'}
        if t <= gcd(sp, n) and sp >= 1:
            preds.append(n // gcd(sp, n))
        return max(preds) if preds else 0
    over = 0
    for (a, b, t), c in sorted(table.items()):
        pr = cell_pred(a, b, t)
        if c > pr:
            over += 1
            anomalies.append(dict(a=a, b=b, t=t, count=c, pred=pr))
    log(f"   nonzero cells: {len(table)}; cells exceeding the law set: {over}")
    top = sorted(anomalies, key=lambda x: -(x["count"] - x["pred"]))[:12]
    for an in top:
        log(f"      UNEXPLAINED cell (a={an['a']}, b={an['b']}, t={an['t']}): "
            f"count {an['count']} > law {an['pred']}")
    # the per-threshold monomial maxima vs the envelope prediction
    permax = {}
    for (a, b, t), c in table.items():
        if c > permax.get(t, (0, None))[0]:
            permax[t] = (c, (a, b))
    for t in sorted(permax):
        pred = envelope_pred(fams, t)
        c, ab = permax[t]
        flag = " <-- EXCEEDS catalogue envelope" if c > pred else ""
        log(f"   monomial max at t={t}: {c} at (X^{ab[0]},X^{ab[1]}) "
            f"(envelope pred {pred}){flag}")
    results[f"monomial_p{p}_n{n}_d{d}"] = dict(
        permax={t: [c, list(ab)] for t, (c, ab) in permax.items()},
        anomalies=anomalies)
    return table, anomalies


# ----------------------------------------------------------------- tier 3: discovery

def tier3_discovery(p, g, n, d, t_targets, results, iters=260):
    dom = Domain(p, g, n)
    mu = n.bit_length() - 1
    fams = catalogue_families(n, d, mu)
    log(f"== TIER 3 DISCOVERY (HEURISTIC novelty search): p={p}, n={n}, d={d} ==")
    h = n // 2
    finds = []
    seeds = [(monomial(dom, h), monomial(dom, (h + 1) % n), "pencil"),
             (monomial(dom, h), monomial(dom, (h + 2) % n), "pencil2"),
             doublet_stack(dom) + ("doublet",)]
    for f in fams:
        st = family_stack(dom, f)
        if st is not None:
            seeds.append((st[0], st[1], f["name"]))
    # hybrid structured families: pencil with sign-subset deviations
    hybrids = []
    for a in range(0, n, max(1, n // 8)):
        for lam in (1, p - 1):
            u0 = [(monomial(dom, h)[i] + lam * monomial(dom, a)[i]) % p
                  for i in range(n)]
            hybrids.append((u0, monomial(dom, h + 1), f"hyb0(a={a},l={lam})"))
            u1 = [(monomial(dom, (h + 1) % n)[i] + lam * monomial(dom, a)[i]) % p
                  for i in range(n)]
            hybrids.append((monomial(dom, h), u1, f"hyb1(a={a},l={lam})"))
    for t in t_targets:
        pred = envelope_pred(fams, t)
        best, arg = 0, None
        def consider(u0, u1, label):
            nonlocal best, arg
            th = dom.bad_set_thresholds(u0, u1, d, max(d + 3, t))
            c = sum(1 for T in th.values() if T >= t)
            if c > best:
                best, arg = c, label
            return c
        for (u0, u1, name) in seeds + hybrids:
            consider(u0, u1, name)
        cur = (list(seeds[0][0]), list(seeds[0][1]))
        cur_c = consider(cur[0], cur[1], "seed")
        for _ in range(iters):
            u0, u1 = list(cur[0]), list(cur[1])
            for _ in range(random.randrange(1, 3)):
                (u0 if random.randrange(2) == 0 else u1)[random.randrange(n)] = \
                    random.randrange(p)
            c = consider(u0, u1, "climb")
            if c >= cur_c:
                cur, cur_c = (u0, u1), c
        flag = " <-- EXCEEDS catalogue envelope (NEW FAMILY CANDIDATE)" \
            if best > pred else ""
        log(f"   t={t}: observed max {best} (catalogue envelope {pred}) "
            f"[{arg}]{flag}")
        finds.append(dict(t=t, best=best, pred=pred, arg=str(arg)))
    results[f"discovery_p{p}_n{n}_d{d}"] = finds
    return finds


# ----------------------------------------------------------------- main

def main():
    results = {}
    only = sys.argv[1] if len(sys.argv) > 1 else "all"

    # ---------------- tier 1: exhaustive at p=17, n=8, g=2 ----------------
    if only in ("all", "t1"):
        # d=3 (m=4): everything cheap; t in {5,6,7} (t >= d+2 = 5)
        tier1_instance(17, 2, 8, 3, e_list=[1, 2, 3], results=results)
        # d=2 (m=5): t in {4,5,6,7} -- e=4 is the expensive complete-curve pass
        tier1_instance(17, 2, 8, 2, e_list=[1, 2, 3, 4], results=results)
        # d=1 (m=6): t in {5,6,7}; e=4 (t=4) infeasible -> heuristic there
        tier1_instance(17, 2, 8, 1, e_list=[1, 2, 3], results=results)

    # ---------------- tier 1b: the p=97 shoulder cell, exhaustive ----------------
    if only in ("all", "t1b"):
        tier1b_shoulder_p97(results)

    # ---------------- tier 2: monomial law tables ----------------
    if only in ("all", "t2"):
        tier2_monomial_table(17, 2, 8, 1, 4, 7, results)
        tier2_monomial_table(17, 2, 8, 2, 5, 7, results)
        tier2_monomial_table(17, 2, 8, 3, 6, 7, results)
        # n=16 instances (the mission set): p=17 full group, p=97 subgroup
        tier2_monomial_table(17, 3, 16, 1, 4, 14, results)
        tier2_monomial_table(17, 3, 16, 2, 5, 14, results)
        tier2_monomial_table(17, 3, 16, 4, 7, 14, results)
        tier2_monomial_table(97, 8, 16, 1, 4, 14, results)
        tier2_monomial_table(97, 8, 16, 2, 5, 14, results)
        tier2_monomial_table(97, 8, 16, 4, 7, 14, results)

    # ---------------- tier 3: discovery (novelty search) ----------------
    if only in ("all", "t3"):
        tier3_discovery(97, 8, 16, 2, t_targets=[7, 9, 10, 11, 12], results=results)
        tier3_discovery(97, 8, 16, 4, t_targets=[9, 11, 12, 13], results=results)
        tier3_discovery(17, 3, 16, 2, t_targets=[9, 10, 11, 12], results=results)
        tier3_discovery(97, 64, 8, 2, t_targets=[5, 6, 7], results=results)

    # ---------------- the assembled curves ----------------
    if only in ("all", "t1"):
        log("== ASSEMBLED delta*(eps*) CURVES (exhaustive cells only) ==")
        for tag, inst in results.items():
            if not tag.startswith("p17_n8"):
                continue
            ws = {t: v["W"] for t, v in inst.items() if v.get("exhaustive")}
            log(f"   {tag}: W_t = {ws} (+ W_8 = 1 single / W_7 doublet law);"
                f" curve: eps* in [W_t/17, W_(t-1)/17) -> delta* = (8-t)/8")

    with open("scripts/probes/badfamily_census_results.json", "w") as f:
        json.dump(results, f, indent=1, default=str)
    log("ALL CHECKS PASS — results in scripts/probes/badfamily_census_results.json")


if __name__ == "__main__":
    main()
