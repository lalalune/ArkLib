#!/usr/bin/env python3
"""
probe_strip_sup_exactness.py -- #357 closing-audit item 4: sub-Johnson sup-exactness.

PRE-REGISTERED HYPOTHESES (2026-06-11, registered before any computation; lane claim
posted on #357):

  H-A (strip law, sup side): at strip cells (2b <= d <= 3b-3, (b-1)|n, band b,
      e = b-1 errors), the EXACT max over all pencils of the bad-scalar count is
      n/(b-1) -- i.e. the landed MonomialStripExplosion certificate is extremal:
        cell A1 (n=6, k=1, q=7,  d=6, b=3, e=2): max N = 3
        cell A2 (n=6, k=1, q=13, d=6, b=3, e=2): max N = 3
        cell A3 (n=8, k=3, q=17, d=6, b=3, e=2): max N = 4
  H-B (validation): the syndrome criterion reproduces the known boundary values:
        cell B1 (n=6, k=2, q=7, d=5, boundary b=3, 3|6): max N = 6 (old exhaustive: 6)
  H-C (structure): every strip-cell maximizer has pairwise-disjoint error supports,
      each a fiber of x -> x^(b-1) (the telescoping family's signature), up to the
      affine/rotation/scaling symmetries of the pencil.

METHOD (all exact arithmetic mod p):
  * Syndrome reduction: mcaEvent badness of gamma depends on (u0,u1) only through
    syndromes (s0,s1) [everything is modulo the code]. Syndromes: s_r(w) =
    sum_j w_j x_j^r, r = 1..n-k, for the RS code {p(x) : deg p < k} on mu_n.
  * Unique-representation regime: throughout, 2e < d, so each syndrome in the
    weight-<=e ball has a UNIQUE weight-<=e representation err (two reps would differ
    by a codeword of weight <= 2e < d).
  * Badness criterion (derived from mcaEvent, ABF26 Def 4.3, Errors.lean:216):
      gamma bad  <=>  t := s0 + gamma*s1 is in the weight-<=e ball, with unique rep
      support E = supp(err), and NOT (s0 in S(E) and s1 in S(E)),
    where S(E) = syndromes of words supported on E.
      Proof sketch: explanations w on a witness set S (|S| >= n-e) correspond to
      error words err' = line - w vanishing on S, i.e. supp(err') <= S^c, |S^c| <= e;
      by unique decoding err' = err. For fixed w, not-pairJointAgreesOn is monotone
      increasing in S, so the adversarial existential over S is decided at the maximal
      witness S = zeroset(err); joint agreement there says both u0,u1 agree with
      codewords off supp(err), i.e. both syndromes lie in S(supp(err)).
    This is CROSS-VALIDATED below against a direct word-level mcaEvent implementation.
  * Exhaustiveness: bad gamma => line point in ball, so any pencil with >= 2 bad
    scalars has >= 2 ball hits; the bad-count is invariant under affine
    reparametrization gamma -> a*gamma + c (a != 0) [the line set and the witness
    structure are unchanged, scalars are relabelled], and every >=2-hit line has a
    reparametrization with hits at gamma in {0,1}. Hence sweeping
    (t1, t2) in ball x ball, t1 != t2, with s0 = t1, s1 = t2 - t1 != 0 visits every
    pencil with max-relevant bad count, exactly once up to symmetry.

Output: per-cell verdict (max N + count of maximizing lines + support structure of a
sample of maximizers), cross-validation pass/fail, and JSON dump.
"""

import itertools
import json
import sys
import time

import numpy as np


# ---------------------------------------------------------------- field/code setup

def find_generator_of_order(p, n):
    """An element of multiplicative order exactly n in F_p (requires n | p-1)."""
    assert (p - 1) % n == 0
    for g in range(2, p):
        # candidate: g^((p-1)/n) has order dividing n; check exact order n
        h = pow(g, (p - 1) // n, p)
        ok = h != 1
        if not ok:
            continue
        # order of h divides n; exact iff h^(n/ell) != 1 for every prime ell | n
        m, ell, good = n, 2, True
        primes = set()
        while ell * ell <= m:
            if m % ell == 0:
                primes.add(ell)
                while m % ell == 0:
                    m //= ell
            ell += 1
        if m > 1:
            primes.add(m)
        for ell in primes:
            if pow(h, n // ell, p) == 1:
                good = False
                break
        if good:
            return h
    raise RuntimeError("no generator found")


class Cell:
    """RS[F_p, mu_n, k] at error budget e (band b = e+1), syndrome machinery."""

    def __init__(self, n, k, p, e):
        self.n, self.k, self.p, self.e = n, k, p, e
        self.r = n - k                      # number of syndrome rows
        self.d = n - k + 1
        assert 2 * e < self.d, "unique-representation regime required"
        g = find_generator_of_order(p, n)
        self.dom = [pow(g, j, p) for j in range(n)]
        # syndrome rows: s_r(w) = sum_j w_j * x_j^(r+1), r = 0..n-k-1
        self.H = np.array([[pow(x, rr + 1, p) for x in self.dom]
                           for rr in range(self.r)], dtype=np.int64)
        self.pw = np.array([p ** i for i in range(self.r)], dtype=np.int64)
        self.size = p ** self.r
        # digits table D: index -> syndrome vector (size, r)
        idx = np.arange(self.size, dtype=np.int64)
        self.D = np.empty((self.size, self.r), dtype=np.int64)
        for i in range(self.r):
            self.D[:, i] = (idx // (p ** i)) % p

    def syn_idx(self, vec):
        return int(np.dot(np.mod(vec, self.p), self.pw))

    def build_ball(self):
        """Weight-<=e ball: rep map (index -> support id, -1 outside), support list,
        and S(E) membership tables for every support of size <= e."""
        n, p, e = self.n, self.p, self.e
        supports = [()]  # empty support first
        for size in range(1, e + 1):
            supports += [tuple(c) for c in itertools.combinations(range(n), size)]
        self.supports = supports
        sup_id = {E: i for i, E in enumerate(supports)}
        REP = np.full(self.size, -1, dtype=np.int16)
        REP[0] = sup_id[()]
        ball_points = [0]
        # enumerate weight-exactly-size words
        for size in range(1, e + 1):
            for E in itertools.combinations(range(n), size):
                cols = self.H[:, list(E)]              # (r, size)
                for vals in itertools.product(range(1, p), repeat=size):
                    s = np.mod(cols @ np.array(vals, dtype=np.int64), p)
                    ix = int(np.dot(s, self.pw))
                    if REP[ix] != -1:
                        raise RuntimeError("non-unique representation -- regime bug")
                    REP[ix] = sup_id[E]
                    ball_points.append(ix)
        self.REP = REP
        self.ball = np.array(sorted(ball_points), dtype=np.int64)
        # membership M[sup_id, idx]: idx in S(E) (any values incl. 0 on E)
        M = np.zeros((len(supports), self.size), dtype=bool)
        M[0, 0] = True
        for E, i in sup_id.items():
            if not E:
                continue
            cols = self.H[:, list(E)]
            for vals in itertools.product(range(p), repeat=len(E)):
                s = np.mod(cols @ np.array(vals, dtype=np.int64), p)
                M[i, int(np.dot(s, self.pw))] = True
        self.M = M

    # ------------------------------------------------------------ exhaustive sweep

    def sweep(self, report_at):
        """Sweep all lines with >=2 ball hits via (t1,t2) in ball^2; return
        (maxN, list of (t1,t2,badgammas) with N >= report_at)."""
        p = self.p
        ball = self.ball
        nb = len(ball)
        Dball = self.D[ball]                          # (nb, r)
        maxN = 0
        winners = []
        t0 = time.time()
        for a in range(nb):
            t1 = ball[a]
            d1 = self.D[t1]                           # (r,)
            # s1 candidates: t2 - t1 over the rest of the ball (skip t2 == t1)
            S1D = np.mod(Dball - d1, p)               # (nb, r)
            s1idx = S1D @ self.pw                     # (nb,)
            live = s1idx != 0                         # s1 = 0 -> degenerate
            badcount = np.zeros(nb, dtype=np.int16)
            badmask = np.zeros((nb, p), dtype=bool)
            for gamma in range(p):
                TD = np.mod(d1 + gamma * S1D, p)
                tix = TD @ self.pw
                rids = self.REP[tix]
                ok = rids >= 0
                rsafe = np.where(ok, rids, 0)
                joint = self.M[rsafe, t1] & self.M[rsafe, s1idx]
                bad = ok & ~joint & live
                badmask[:, gamma] = bad
                badcount += bad.astype(np.int16)
            mn = int(badcount.max()) if nb else 0
            if mn > maxN:
                maxN = mn
            hits = np.nonzero(badcount >= report_at)[0]
            for h in hits:
                gs = [g for g in range(p) if badmask[h, g]]
                winners.append((int(t1), int(ball[h]), gs))
            if a % 500 == 0 and a:
                el = time.time() - t0
                print(f"    .. {a}/{nb} t1 done, {el:.0f}s, maxN so far {maxN}",
                      flush=True)
        return maxN, winners

    # ----------------------------------------------------- structure of maximizers

    def describe(self, t1, t2, gammas):
        """Error supports of each bad gamma for the line s0=t1, s1=t2-t1."""
        p = self.p
        d1, d2 = self.D[t1], self.D[t2]
        s1d = np.mod(d2 - d1, p)
        out = []
        for g in gammas:
            tix = int(np.dot(np.mod(d1 + g * s1d, p), self.pw))
            rid = int(self.REP[tix])
            E = self.supports[rid]
            s0in = bool(self.M[rid, t1])
            s1in = bool(self.M[rid, int(np.dot(s1d, self.pw))])
            out.append({"gamma": g, "support": list(E),
                        "s0_in_SE": s0in, "s1_in_SE": s1in})
        return out


# ----------------------------------------------------- word-level cross-validation

def word_level_bad(cell, u0, u1, gamma):
    """Direct mcaEvent (ABF26 Def 4.3): exists S, |S| >= n-e, with a codeword
    agreeing with u0+gamma*u1 on S and no joint pair on S."""
    n, k, p, e = cell.n, cell.k, cell.p, cell.e
    dom = cell.dom
    line = [(u0[j] + gamma * u1[j]) % p for j in range(n)]
    # all codewords (p^k), as evaluation vectors
    cws = []
    for coeffs in itertools.product(range(p), repeat=k):
        cws.append([sum(c * pow(x, i, p) for i, c in enumerate(coeffs)) % p
                    for x in dom])

    def explainable(vec, S):
        return any(all(w[j] == vec[j] for j in S) for w in cws)

    for size in range(n - e, n + 1):
        for S in itertools.combinations(range(n), size):
            if explainable(line, S) and not (explainable(u0, S) and
                                             explainable(u1, S)):
                return True
    return False


def cross_validate(cell, samples, rng):
    n, p = cell.n, cell.p
    for _ in range(samples):
        u0 = [int(rng.integers(p)) for _ in range(n)]
        u1 = [int(rng.integers(p)) for _ in range(n)]
        s0 = cell.syn_idx(cell.H @ np.array(u0))
        s1v = np.mod(cell.H @ np.array(u1), p)
        s1 = int(np.dot(s1v, cell.pw))
        for gamma in range(p):
            tix = int(np.dot(np.mod(cell.D[s0] + gamma * cell.D[s1], p), cell.pw))
            rid = int(cell.REP[tix])
            if rid < 0:
                syn_bad = False
            else:
                syn_bad = not (bool(cell.M[rid, s0]) and bool(cell.M[rid, s1]))
            word_bad = word_level_bad(cell, u0, u1, gamma)
            if syn_bad != word_bad:
                return False, (u0, u1, gamma, syn_bad, word_bad)
    return True, None


# ------------------------------------------------------------------------- driver

def run_cell(name, n, k, p, e, expected, samples=0, report_at=None):
    print(f"== cell {name}: RS[F_{p}, mu_{n}, k={k}], d={n-k+1}, e={e} "
          f"(band {e+1}) -- expected max N = {expected}")
    cell = Cell(n, k, p, e)
    cell.build_ball()
    print(f"   ball size {len(cell.ball)}, syndrome space {cell.size}")
    if samples:
        rng = np.random.default_rng(357)
        ok, witness = cross_validate(cell, samples, rng)
        print(f"   cross-validation ({samples} random word-level instances): "
              f"{'PASS' if ok else 'FAIL ' + repr(witness)}")
        if not ok:
            sys.exit(1)
    ra = report_at if report_at is not None else expected
    maxN, winners = cell.sweep(ra)
    verdict = "CONFIRMED" if maxN == expected else "REFUTED"
    print(f"   max N over all pencils = {maxN}  [{verdict}: hypothesis {expected}]")
    print(f"   lines with N >= {ra}: {len(winners)}")
    sample_desc = []
    for (t1, t2, gs) in winners[:8]:
        desc = cell.describe(t1, t2, gs)
        sample_desc.append({"t1": t1, "t2": t2, "bad": desc})
        sups = [tuple(x["support"]) for x in desc]
        flat = [j for E in sups for j in E]
        disjoint = len(flat) == len(set(flat))
        print(f"     line (t1={t1}, t2={t2}): gammas {gs}, supports {sups}, "
              f"disjoint={disjoint}")
    return {"cell": name, "n": n, "k": k, "p": p, "e": e,
            "expected": expected, "maxN": maxN, "n_winners": len(winners),
            "samples": sample_desc}


def main():
    results = []
    # B1 validation first (known boundary value 6)
    results.append(run_cell("B1", 6, 2, 7, 2, expected=6, samples=60))
    # A1 strip
    results.append(run_cell("A1", 6, 1, 7, 2, expected=3, samples=60))
    # A2 strip, bigger field
    results.append(run_cell("A2", 6, 1, 13, 2, expected=3))
    # A3 strip, n=8 (the discriminating cell: n/(b-1)=4 > e+1=3)
    if "--full" in sys.argv:
        results.append(run_cell("A3", 8, 3, 17, 2, expected=4, samples=20))
    with open("scripts/probes/strip_sup_exactness_results.json", "w") as f:
        json.dump(results, f, indent=1)
    print("done.")


if __name__ == "__main__":
    main()
