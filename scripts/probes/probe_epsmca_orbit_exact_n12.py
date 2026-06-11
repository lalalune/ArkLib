#!/usr/bin/env python3
"""EXACT eps_mca at n = 12 via affine-orbit reduction (issue #334, hypothesis A5).

Goal: turn the SAMPLED n = 12 rungs (probe_epsmca_sampled_rungs.py; issue #334
comments: at (n,k) = (12,6), p = 13 the sampled lower bounds were
delta 0/0.083/0.167 -> 1, delta 0.25 -> 12/13, delta 1/3 -> 13/13) into an
EXACT computation, by quotienting the syndrome-pair space by the symmetry group
of mcaEvent (ArkLib/Data/CodingTheory/ProximityGap/Errors.lean, ABF26 Def 4.3).

Symmetries used (C linear, smooth domain H = <g>, |H| = n | p-1):

  (a) domain rotation x -> g.x: a cyclic index shift P on words; the RS code is
      P-stable (f(x) -> f(gx) preserves degree), so P induces a linear map R on
      syndromes (H.P = R.H, R^n = I).  ext masks are equivariant (subsets of
      equal size permute), the line maps pointwise: bad-gamma SET invariant
      under (s0, s1) -> (R s0, R s1).
  (b) (u0,u1) -> (c u0, c u1), c != 0: line scales by c, ext is
      scale-invariant (linearity): bad-gamma SET invariant.
  (c) (u0,u1) -> (u0 + g0 u1, u1): line reparametrizes gamma -> gamma + g0.
      The not-jointly-explained clause is ALSO invariant: for linear C,
        ext(u0 + g0 u1, S) and ext(u1, S)  <=>  ext(u0, S) and ext(u1, S)
      (shear v0 by -g0 v1 / +g0 v1 between witnesses).  Hence bitwise
      E(s0 + g0 s1) & E(s1) == E(s0) & E(s1) per subset S, and the bad-gamma
      set SHIFTS by -g0: bad-COUNT invariant.
  (d) (u0,u1) -> (u0, c u1): bad-gamma set scales by 1/c: COUNT invariant.
  (e) Frobenius: trivial for prime p.

Group G: (s0, s1) -> (a R^t s0 + b R^t s1, c R^t s1), a,c in F*, b in F,
t in Z_n; |G| = n.p.(p-1)^2.  The per-threshold bad-gamma COUNT is G-invariant,
so the sup in epsMCA is attained on orbit representatives:

  * s1 ranges over orbit reps of nonzero syndromes under s -> a R^t s
    (canonical = min encoded value over the n(p-1) transforms);
  * for fixed s1-rep with pivot coordinate j (first nonzero), s0 ranges over
    {0} + {v : v_j = 0, first nonzero coordinate = 1}: a transversal of
    F^d / (span{s1} x scaling).  (Completeness: move s1 to its rep by some
    (c,t) acting diagonally, then b zeroes coordinate j of s0 -- s1_j != 0 --
    and a normalizes the first nonzero.  Uniqueness: b is forced to 0 by the
    j-th coordinate, then a = 1.)

Syndrome ext machinery (exact, no unique-decoding shortcuts): for each witness
size s in {k+1..n}, ext(synd, S) <=> the coset contains a vector vanishing on S
<=> some coset vector v with supp(v) subset S^c, wt(v) <= n - s.  We enumerate
ALL vectors of weight <= n-(k+1) (grouped by support; within one support group
syndromes are distinct since 2(n-k-1) < d_min would fail only via a codeword of
weight <= n-k-1 < n-k+1), and scatter subset-bits per size into per-syndrome
bitset tables (numpy uint64, one table per witness size).

Two sound speedups in the search itself:
  * saturation dropping: the bad-gamma count is at most p; once some threshold
    m attains count = p its row is EXACT (max possible), and since the profile
    is monotone the saturated thresholds form a suffix of small m -- their
    bitset tables (the wide ones) are dropped from all later gathers;
  * fork-parallelism over s1-reps (read-only shared tables); each worker
    re-derives saturation locally, so dropping never affects exactness.

Witness discipline:
  * the rotation matrix R is verified on random words and R^n = I;
  * the ext tables are spot-checked against the ladder probe's Lagrange
    `ext_from` on random syndromes (including at n = 12);
  * the orbit-reduced profile is validated EXACTLY against (i) the full
    enumeration with the same machinery and (ii) the independent
    `eps_profile_syndrome` of probe_exact_epsmca_ladder.py, on
    RS[F_5,4,2], RS[F_13,4,2], RS[F_7,6,3] (ladder cross-check) and
    RS[F_13,6,3] (full-vs-reps; the pure-python ladder run there is slow);
  * at n = 12 the exact counts must dominate the recorded sampled lower
    bounds (sampling can only under-report).

Exit 0 iff all assertions pass.
"""

import argparse
import importlib.util
import os
import random
import sys
import time
from itertools import combinations, product
from math import sqrt

import numpy as np

_here = os.path.dirname(os.path.abspath(__file__))
_spec = importlib.util.spec_from_file_location(
    "ladder", os.path.join(_here, "probe_exact_epsmca_ladder.py"))
ladder = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(ladder)


# --------------------------------------------------------------- instance core

class Instance:
    """RS[F_p, n, k] on the smooth domain, syndrome-side ext bitset machinery."""

    def __init__(self, p, n, k, min_size=None):
        self.p, self.n, self.k = p, n, k
        self.d = n - k
        self.xs = ladder.smooth_domain(p, n)
        G = [[pow(x, j, p) for x in self.xs] for j in range(k)]
        self.H = ladder.nullspace(G, p)
        assert len(self.H) == self.d
        self.npH = np.array(self.H, dtype=np.int64) % p
        self.powv = np.array([p ** i for i in range(self.d)], dtype=np.int64)
        self.nsyn = p ** self.d
        lo = (k + 1) if min_size is None else min_size
        assert lo >= k + 1
        self.sizes = list(range(n, lo - 1, -1))            # descending n..lo
        self.subidx, self.nwords, self.offset = {}, {}, {}
        off = 0
        for size in self.sizes:                            # big sizes first:
            subs = list(combinations(range(n), size))      # active prefix
            self.subidx[size] = {S: i for i, S in enumerate(subs)}
            self.nwords[size] = (len(subs) + 63) // 64
            self.offset[size] = off
            off += self.nwords[size]
        self.total_words = off

    def digits(self, idx_arr):
        out = np.empty((len(idx_arr), self.d), dtype=np.int64)
        for i in range(self.d):
            out[:, i] = (idx_arr // self.p ** i) % self.p
        return out

    def enc(self, vecs):
        return (np.asarray(vecs, dtype=np.int64) % self.p) @ self.powv

    # ----- ext bitsets: one concatenated row per syndrome, sizes descending,
    # so the still-active sizes always occupy a contiguous prefix of columns
    def build_E(self, verbose=False):
        p, n = self.p, self.n
        E_all = np.zeros((self.nsyn, self.total_words), dtype=np.uint64)
        E = {s: E_all[:, self.offset[s]:self.offset[s] + self.nwords[s]]
             for s in self.sizes}
        maxw = n - self.sizes[-1]                          # n - min_size
        t0 = time.time()
        for w in range(maxw + 1):
            if w == 0:
                vals = np.zeros((1, 0), dtype=np.int64)
            else:
                vals = np.array(list(product(range(1, p), repeat=w)),
                                dtype=np.int64)
            for supp in combinations(range(n), w):
                if w:
                    syn = (vals @ self.npH[:, list(supp)].T) % p
                    idx = syn @ self.powv
                else:
                    idx = np.zeros(1, dtype=np.int64)
                Z = tuple(sorted(set(range(n)) - set(supp)))
                for size in self.sizes:
                    if size > len(Z):
                        continue
                    wordbits = {}
                    for S in combinations(Z, size):
                        b = self.subidx[size][S]
                        wordbits[b >> 6] = wordbits.get(b >> 6, 0) | (1 << (b & 63))
                    V = E[size]
                    for wpos, mask in wordbits.items():
                        V[idx, wpos] |= np.uint64(mask)
            if verbose:
                print(f"    E build: weight {w} done ({time.time() - t0:.1f}s)",
                      flush=True)
        return E_all, E

    def spot_check_E(self, E, samples, seed=334):
        """E bits vs the ladder probe's independent Lagrange ext_from."""
        rng = random.Random(seed)
        for _ in range(samples):
            s = [rng.randrange(self.p) for _ in range(self.d)]
            idx = int(self.enc(np.array([s]))[0])
            w = ladder.solve_particular(self.H, s, self.p)
            for size in self.sizes:
                V = E[size]
                for S, b in self.subidx[size].items():
                    expect = ladder.ext_from(w, list(S), self.xs, self.k, self.p)
                    got = bool((int(V[idx, b >> 6]) >> (b & 63)) & 1)
                    assert got == expect, \
                        f"E bit mismatch p={self.p} n={self.n} synd={s} S={S}"

    # ----- rotation matrix on syndromes (domain x -> g.x  <=>  index shift +1)
    def rotation(self):
        p, n, d = self.p, self.n, self.d
        R = np.zeros((d, d), dtype=np.int64)
        for i in range(d):
            e = [0] * d
            e[i] = 1
            w = ladder.solve_particular(self.H, e, p)
            wr = [w[(a + 1) % n] for a in range(n)]
            R[:, i] = [sum(h[j] * wr[j] for j in range(n)) % p for h in self.H]
        rng = random.Random(self.p * 1000 + n)
        for _ in range(64):
            w = [rng.randrange(p) for _ in range(n)]
            s = np.array([sum(h[j] * w[j] for j in range(n)) % p
                          for h in self.H], dtype=np.int64)
            wr = [w[(a + 1) % n] for a in range(n)]
            sr = np.array([sum(h[j] * wr[j] for j in range(n)) % p
                           for h in self.H], dtype=np.int64)
            assert np.array_equal((R @ s) % p, sr), "rotation matrix mismatch"
        M = np.eye(d, dtype=np.int64)
        for _ in range(n):
            M = (R @ M) % p
        assert np.array_equal(M % p, np.eye(d, dtype=np.int64)), "R^n != I"
        return R


# ------------------------------------------------------------ orbit transversal

def s1_orbit_reps(inst, R, chunk=1 << 20, verbose=False):
    """Indices of canonical (min-encoded) reps of nonzero syndromes under
    s -> a R^t s, a in F*, t in Z_n."""
    p, N = inst.p, inst.nsyn
    canon = np.arange(N, dtype=np.int64)
    Mt = np.eye(inst.d, dtype=np.int64)
    t0 = time.time()
    for t in range(inst.n):
        if t > 0:
            Mt = (R @ Mt) % p
        for lo in range(0, N, chunk):
            hi = min(N, lo + chunk)
            V = inst.digits(np.arange(lo, hi, dtype=np.int64))
            S = (V @ Mt.T) % p
            for a in range(1, p):
                idx = ((a * S) % p) @ inst.powv
                np.minimum(canon[lo:hi], idx, out=canon[lo:hi])
        if verbose:
            print(f"    s1 canon: rotation power {t} done "
                  f"({time.time() - t0:.1f}s)", flush=True)
    reps = np.where(canon == np.arange(N, dtype=np.int64))[0]
    return reps[reps != 0]


def s0_reps_for_pivot(inst, j):
    """{0} + {v in F^d : v_j = 0, first nonzero coord = 1}: transversal of
    F^d modulo (v -> a v + b s1) for any s1 with pivot j."""
    p, d = inst.p, inst.d
    Nq = p ** (d - 1)
    ar = np.arange(Nq, dtype=np.int64)
    Vq = np.empty((Nq, d - 1), dtype=np.int64)
    for i in range(d - 1):
        Vq[:, i] = (ar // p ** i) % p
    nz = Vq != 0
    has = nz.any(axis=1)
    first = nz.argmax(axis=1)
    fval = Vq[np.arange(Nq), first]
    Vn = Vq[has & (fval == 1)]
    out = np.zeros((1 + Vn.shape[0], d), dtype=np.int64)
    cols = [c for c in range(d) if c != j]
    out[1:, cols] = Vn
    expected = 1 + (p ** (d - 1) - 1) // (p - 1)
    assert out.shape[0] == expected, (out.shape[0], expected)
    return out


# -------------------------------------------------------------- profile kernel

def _pregather(inst, E_all, s0sets):
    return {key: (s0v, E_all[inst.enc(s0v)]) for key, s0v in s0sets.items()}


def run_profile(inst, E_all, s1vecs, s0sets, pivot_of, label,
                checkpoint=0, pre=None):
    """Max bad-gamma count per threshold m over pairs (s0 in s0sets[pivot(s1)],
    s1 in s1vecs), all gamma in F_p.  Returns (best dict, witness dict).

    Saturation dropping: once best[m] == p (the max possible count), threshold
    m is exact; by monotonicity the saturated m form a suffix of small sizes,
    so all sizes < active_min can be skipped without affecting exactness.
    Sizes are laid out big-first in E_all, so the active sizes are a column
    prefix and each gamma costs ONE prefix-width row gather."""
    p, sizes = inst.p, inst.sizes
    best = {m: 0 for m in sizes}
    wit = {m: None for m in sizes}
    if pre is None:
        pre = _pregather(inst, E_all, s0sets)
    active_min = sizes[-1]
    total = len(s1vecs)
    t0 = time.time()
    for ci in range(total):
        s1v = s1vecs[ci]
        s1row = E_all[int(inst.enc(s1v[None, :])[0])]
        s0v, rows0 = pre[pivot_of(s1v)]
        W = inst.offset[active_min] + inst.nwords[active_min]
        notp = ~(rows0[:, :W] & s1row[:W])
        N0 = s0v.shape[0]
        counts = np.zeros((N0, len(sizes)), dtype=np.uint8)
        for g in range(p):
            idx = ((s0v + g * s1v) % p) @ inst.powv
            x = E_all[idx, :W]
            x &= notp
            badcum = np.zeros(N0, dtype=bool)
            for si, size in enumerate(sizes):
                if size < active_min:
                    break
                lo = inst.offset[size]
                xs = x[:, lo:lo + inst.nwords[size]]
                badcum |= np.bitwise_or.reduce(xs, axis=1) != 0
                counts[:, si] += badcum
        for si, m in enumerate(sizes):
            if m < active_min:
                break
            c = int(counts[:, si].max())
            if c > best[m]:
                best[m] = c
                a = int(counts[:, si].argmax())
                wit[m] = (tuple(int(v) for v in s1v),
                          tuple(int(v) for v in s0v[a]))
        unsat = [m for m in sizes if best[m] < p]
        if not unsat:
            break
        active_min = min(unsat)
        if checkpoint and (ci + 1) % checkpoint == 0:
            el = time.time() - t0
            eta = el / (ci + 1) * (total - ci - 1)
            print(f"    [{label}] {ci + 1}/{total} s1-reps  "
                  f"elapsed {el:.0f}s  eta {eta:.0f}s  best={best}", flush=True)
    return best, wit


# ---------------------------------------------------- fork-parallel driver

_G = {}


def _pivot_first_nonzero(v):
    return int(np.argmax(v != 0))


def _worker(bounds):
    a, b = bounds
    best, wit = run_profile(_G["inst"], _G["E_all"], _G["s1reps"][a:b],
                            _G["s0sets"], _pivot_first_nonzero,
                            f"worker[{a}:{b}]", checkpoint=0, pre=_G["pre"])
    return best, wit, b - a


def run_parallel(inst, E_all, s1reps, s0sets, workers, label,
                 chunk=256, checkpoint_tasks=8):
    import multiprocessing as mp
    _G.update(inst=inst, E_all=E_all, s1reps=s1reps, s0sets=s0sets,
              pre=_pregather(inst, E_all, s0sets))
    tasks = [(a, min(a + chunk, len(s1reps)))
             for a in range(0, len(s1reps), chunk)]
    best = {m: 0 for m in inst.sizes}
    wit = {m: None for m in inst.sizes}
    done, t0 = 0, time.time()
    ctx = mp.get_context("fork")
    with ctx.Pool(workers) as pool:
        for ti, (lb, lw, cnt) in enumerate(
                pool.imap_unordered(_worker, tasks)):
            done += cnt
            for m in inst.sizes:
                if lb[m] > best[m]:
                    best[m] = lb[m]
                    wit[m] = lw[m]
            if (ti + 1) % checkpoint_tasks == 0 or done == len(s1reps):
                el = time.time() - t0
                eta = el / done * (len(s1reps) - done)
                print(f"    [{label}] {done}/{len(s1reps)} s1-reps  "
                      f"elapsed {el:.0f}s  eta {eta:.0f}s  best={best}",
                      flush=True)
    return best, wit


# ------------------------------------------------------------------ validation

def fmt_profile(best, p, n, name):
    keys = sorted(best, reverse=True)
    cells = " ".join(f"m={m}:{best[m]}" for m in keys)
    return f"    {name:<28} {cells}   (counts /{p})"


def validate(p, n, k, with_ladder, verbose=False):
    print(f"\n== validation: RS[F_{p}, n={n}, k={k}] ==", flush=True)
    inst = Instance(p, n, k)
    E_all, E = inst.build_E(verbose=verbose)
    inst.spot_check_E(E, samples=20)
    print("    ext-bitset spot check vs ladder ext_from (20 syndromes)  [OK]")
    R = inst.rotation()
    print("    rotation matrix R verified (64 random words, R^n = I)    [OK]")

    allv = inst.digits(np.arange(inst.nsyn, dtype=np.int64))
    bestF, _ = run_profile(inst, E_all, allv[1:], {"all": allv},
                           lambda v: "all", f"full {p},{n},{k}")

    reps = s1_orbit_reps(inst, R)
    s1reps = inst.digits(reps)
    s0sets = {j: s0_reps_for_pivot(inst, j) for j in range(inst.d)}
    bestO, _ = run_profile(inst, E_all, s1reps,
                           s0sets, _pivot_first_nonzero,
                           f"orbit {p},{n},{k}")
    nz = inst.nsyn - 1
    n0 = s0sets[0].shape[0]
    print(f"    orbit stats: {nz} nonzero s1 -> {len(reps)} reps; "
          f"s0: {inst.nsyn} -> {n0}; pairs {nz * inst.nsyn} -> {len(reps) * n0}")
    print(fmt_profile(bestF, p, n, "full enumeration (this probe)"))
    print(fmt_profile(bestO, p, n, "orbit-reduced (this probe)"))
    assert bestF == bestO, f"orbit reduction mismatch: {bestF} vs {bestO}"
    print("    orbit-reduced == full enumeration  [OK]")
    if with_ladder:
        lad, _ = ladder.eps_profile_syndrome(p, n, k)
        print(fmt_profile(lad, p, n, "ladder eps_profile_syndrome"))
        assert lad == bestF, f"ladder mismatch: {lad} vs {bestF}"
        print("    matches ladder probe EXACTLY  [OK]")
    return bestF


# --------------------------------------------------------------------- n = 12

SAMPLED_P13 = {12: 1, 11: 1, 10: 1, 9: 12, 8: 13, 7: None}
# issue #334: sampled lower bounds at (n,k)=(12,6), p=13 (monomial+250 random):
# delta 0 / 0.083 / 0.167 -> 1, delta 0.25 -> 12/13, delta 1/3 -> 13/13.
# delta 0.417 (m=7) was not reported in the issue table.


def estimate_p37():
    p, n, k = 37, 12, 6
    d = n - k
    nsyn = p ** d
    e_bytes = nsyn * 29 * 8
    s1reps = (nsyn - 1) // (n * (p - 1))
    n0 = 1 + (p ** (d - 1) - 1) // (p - 1)
    pairs = s1reps * n0
    print(f"\n== p = 37 feasibility estimate (target iii) ==")
    print(f"    syndrome space 37^6 = {nsyn:,}")
    print(f"    ext-bitset table would need ~{e_bytes / 1e9:.0f} GB "
          f"(29 uint64 words x 37^6 rows) -- exceeds RAM by ~2 orders")
    print(f"    orbit-reduced pairs >= {s1reps:,} x {n0:,} ~ {pairs:.2e}")
    print(f"    (~10^4 x the p=13 reduced workload; ~months at the p=13 rate)")
    print(f"    VERDICT: p = 37 exact is INFEASIBLE for this probe; "
          f"skipped honestly (sampled 12/37 at delta=0.25 stands as lower bound).")


def main_n12(args):
    p, n, k = 13, 12, 6
    min_size = 8 if args.skip_m7 else 7
    print(f"\n== EXACT run: RS[F_{p}, n={n}, k={k}], thresholds m = {n}..{min_size} ==",
          flush=True)
    rho = k / n
    print(f"    rate={rho:.3f}  UDR={(1 - rho) / 2:.3f}  "
          f"Johnson={1 - sqrt(rho):.3f}  capacity={1 - rho:.3f}")

    inst = Instance(p, n, k, min_size=min_size)
    print(f"    work estimate: raw syndrome pairs p^(2(n-k)) = 13^12 = "
          f"{p ** (2 * inst.d):,}")
    t0 = time.time()
    E_all, E = inst.build_E(verbose=True)
    nbytes = E_all.nbytes
    print(f"    E tables built: {inst.nsyn:,} syndromes x {inst.total_words} "
          f"uint64 words ({nbytes / 1e9:.2f} GB) in {time.time() - t0:.0f}s",
          flush=True)
    inst.spot_check_E(E, samples=5)
    print("    ext-bitset spot check vs ladder ext_from (5 syndromes)  [OK]",
          flush=True)
    R = inst.rotation()
    print("    rotation matrix R verified  [OK]", flush=True)

    t0 = time.time()
    reps = s1_orbit_reps(inst, R, verbose=True)
    s1reps = inst.digits(reps)
    s0sets = {j: s0_reps_for_pivot(inst, j) for j in range(inst.d)}
    n0 = s0sets[0].shape[0]
    pairs = len(reps) * n0
    print(f"    s1 orbit reps: {len(reps):,} (of {inst.nsyn - 1:,} nonzero; "
          f"group order n(p-1) = {inst.n * (p - 1)})")
    print(f"    s0 transversal per rep: {n0:,}")
    print(f"    reduced pairs: {pairs:,}  "
          f"(reduction x{p ** (2 * inst.d) / pairs:,.0f} vs raw syndrome pairs)",
          flush=True)

    if args.pilot is not None:
        s1reps = s1reps[:args.pilot]
    best, wit = run_parallel(inst, E_all, s1reps, s0sets, args.workers, "n12")
    if args.pilot is not None:
        print(f"\n    PILOT MODE ({args.pilot} s1-reps): partial lower bounds "
              f"only, no exactness claim: {best}")
        return None
    return best, wit


def report_n12(best, wit, min_size):
    p, n = 13, 12
    print(f"\n== final table: RS[F_13, 12, 6], EXACT (full orbit transversal) ==")
    print(f"    {'m':>3} {'delta':>7} {'exact':>6} {'sampled':>8}  verdict")
    for m in sorted(best, reverse=True):
        s = SAMPLED_P13.get(m)
        e = best[m]
        if s is None:
            verdict = "NEW (no sampled value existed)"
        elif e == s:
            verdict = "CONFIRMED EXACT"
        else:
            verdict = f"RAISED {s} -> {e}"
        print(f"    {m:>3} {1 - m / n:>7.3f} {e:>4}/{p} {('-' if s is None else f'{s}/{p}'):>8}  {verdict}")
    print("\n    witnesses (syndrome pairs (s1, s0), base-13 digit vectors):")
    for m in sorted(best, reverse=True):
        if wit[m] is not None:
            print(f"      m={m}: s1={wit[m][0]} s0={wit[m][1]} -> {best[m]} bad gammas")

    # sampling is a lower bound: exact must dominate every sampled number
    for m, s in SAMPLED_P13.items():
        if s is not None and m in best:
            assert best[m] >= s, f"exact below sampled lower bound at m={m}!"
    assert best[12] == 1, "m=n row must be exactly 1 (single root of s0+g*s1=0)"
    ms = sorted(best, reverse=True)
    for a, b in zip(ms, ms[1:]):
        assert best[b] >= best[a], "monotonicity in delta violated"
    print("    sanity: exact >= sampled lower bounds, m=12 row = 1, monotone  [OK]")


if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("--validate-only", action="store_true")
    ap.add_argument("--skip-n12", action="store_true",
                    help="alias of --validate-only")
    ap.add_argument("--pilot", type=int, default=None,
                    help="process only N s1-reps at n=12 (timing pilot)")
    ap.add_argument("--skip-m7", action="store_true",
                    help="drop the m=7 (delta=0.417) row: 16 instead of 29 "
                         "bitset words per syndrome")
    ap.add_argument("--checkpoint", type=int, default=1000)
    ap.add_argument("--workers", type=int,
                    default=max(1, min(6, (os.cpu_count() or 2) - 2)))
    args = ap.parse_args()

    print("eps_mca affine-orbit exact probe (issue #334 / A5)")
    print("reductions: (a) domain rotation, (b)(d) independent scalings, "
          "(c) shear s0 += b*s1")

    # ---- stage 1: validate machinery + orbit reduction on small instances
    validate(5, 4, 2, with_ladder=True)
    validate(13, 4, 2, with_ladder=True)
    validate(7, 6, 3, with_ladder=True)
    validate(13, 6, 3, with_ladder=False)   # ladder pure-python too slow here;
                                            # full-vs-orbit is the reduction check
    print("\nall small-instance validations passed (orbit reduction is "
          "lossless on every tested instance)", flush=True)

    if args.validate_only or args.skip_n12:
        print("\nall assertions passed")
        sys.exit(0)

    # ---- stage 2: n = 12 exact
    out = main_n12(args)
    if out is not None:
        best, wit = out
        report_n12(best, wit, 8 if args.skip_m7 else 7)

    # ---- stage 3: p = 37 honesty block
    estimate_p37()

    print("\nall assertions passed")
