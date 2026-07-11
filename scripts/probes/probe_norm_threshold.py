#!/usr/bin/env python3
"""
probe_norm_threshold.py — verification suite for the *effective per-prime exactness*
sharpening of the P-A lower-half chain (issue #232, lane: nubs/issue232-effective-pa).

Claims under test (see EffectivePerPrimeExactness.md):

  T1 (orthogonality):  for m = 2^k and alpha = sum_{j<m/2} c_j zeta_m^j,
        sum_{i in (Z/m)^x} |sigma_i(alpha)|^2  ==  (m/2) * sum_j c_j^2          (exact)
  T2 (norm bound):     |N_{K/Q}(alpha)| <= (sum_j c_j^2)^{m/4}                  (AM-GM)
  T3 (threshold):      a modular collision of the e1-image on r-subsets of the
        order-m subgroup of F_p^* forces p <= T(m,r) := (4*min(r, m-r))^{m/4}.
        Hence for p > T(m,r), p ≡ 1 (mod m): image is EXACTLY N0(m,r).
  T4 (predictions):    Goldilocks m=32: image(r=17) == 21_523_360 == N0(32,17),
                                        image(r=16) == 21_523_361 == N0(32,16).
                       BabyBear m=32 is below threshold: measure (no prediction).

Method: exact enumeration. Layers are parametrized by admissible sign patterns
eps in {-1,0,1}^{m/2} (s := |supp eps| with s ≡ r (mod 2), s <= min(r, m-r));
the e1-image equals { sum eps_j g^j } over admissible eps (pairing g^{j+m/2} = -g^j).
For m=32 a meet-in-the-middle over the two halves of the basis gives the exact
image size in ~21.5M uint64 values. Everything is deterministic.

Run: python3 scripts/probes/probe_norm_threshold.py        (~2-4 min, <2 GB RAM)
Exit code 0 iff all PASS.
"""

import itertools
import math
import sys
import time

import numpy as np

FAILURES = []


def check(name, ok, detail=""):
    tag = "PASS" if ok else "FAIL"
    print(f"[{tag}] {name}" + (f" — {detail}" if detail else ""))
    if not ok:
        FAILURES.append(name)


# ---------- basic number theory ----------

_MR_BASES = (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37)  # deterministic < 3.18e23 (psi_12); inputs here are < 2^60


def is_prime(n: int) -> bool:
    if n < 2:
        return False
    for q in _MR_BASES:
        if n % q == 0:
            return n == q
    d, s = n - 1, 0
    while d % 2 == 0:
        d //= 2
        s += 1
    for a in _MR_BASES:
        x = pow(a, d, n)
        if x in (1, n - 1):
            continue
        for _ in range(s - 1):
            x = x * x % n
            if x == n - 1:
                break
        else:
            return False
    return True


def order_m_gen(p: int, m: int) -> int:
    """Element of exact (2-power) order m in F_p^*; requires m | p-1."""
    assert (p - 1) % m == 0
    x = 3
    while True:
        g = pow(x, (p - 1) // m, p)
        if g != 1 and pow(g, m // 2, p) != 1:
            return g
        x += 1


def smallest_prime_1mod(m: int, lo: int) -> int:
    c = ((lo + m - 1) // m) * m + 1
    while not is_prime(c):
        c += m
    return c


# ---------- the combinatorial side ----------

def s_range(m: int, r: int):
    smax = min(r, m - r)
    return range(r % 2, smax + 1, 2)


def N0(m: int, r: int) -> int:
    """Characteristic-0 image size (Entry-5 / Theorem-A formula)."""
    return sum(math.comb(m // 2, s) * 2 ** s for s in s_range(m, r))


def T_threshold(m: int, r: int) -> int:
    """T(m,r) = (4*min(r, m-r))^{m/4}."""
    return (4 * min(r, m - r)) ** (m // 4)


def patterns(m: int, r: int) -> np.ndarray:
    """All admissible eps in {-1,0,1}^{m/2} for layer r, as int8 (N, m/2)."""
    half = m // 2
    out = []
    for s in s_range(m, r):
        for supp in itertools.combinations(range(half), s):
            for signs in itertools.product((1, -1), repeat=s):
                e = np.zeros(half, dtype=np.int8)
                e[list(supp)] = signs
                out.append(e)
    if not out:
        return np.zeros((0, half), dtype=np.int8)
    return np.stack(out)


def image_small(p: int, m: int, r: int, P: np.ndarray) -> int:
    """Exact e1-image size via the pattern matrix (for m <= 16, p < 2^31)."""
    g = order_m_gen(p, m)
    pows = np.array([pow(g, j, p) for j in range(m // 2)], dtype=np.int64)
    vals = (P.astype(np.int64) @ pows) % p
    return len(np.unique(vals))


def image_brute(p: int, m: int, r: int) -> int:
    """Exact e1-image by direct enumeration of r-subsets of the subgroup."""
    g = order_m_gen(p, m)
    G = [pow(g, j, p) for j in range(m)]
    return len({sum(S) % p for S in itertools.combinations(G, r)})


def image_mitm(p: int, m: int, r: int) -> int:
    """Exact e1-image via meet-in-the-middle over basis halves (m = 32)."""
    half = m // 2
    hh = half // 2
    g = order_m_gen(p, m)
    pows = [pow(g, j, p) for j in range(half)]

    def half_values(js):
        by_s = {}
        for eps in itertools.product((-1, 0, 1), repeat=len(js)):
            s = sum(1 for e in eps if e)
            v = 0
            for j, e in zip(js, eps):
                if e == 1:
                    v += pows[j]
                elif e == -1:
                    v += p - pows[j]
            by_s.setdefault(s, []).append(v % p)
        return {s: np.unique(np.array(v, dtype=np.uint64)) for s, v in by_s.items()}

    L = half_values(range(hh))
    R = half_values(range(hh, half))
    smax = min(r, m - r)
    par = r % 2
    pp = np.uint64(p)
    corr = np.uint64((1 << 64) % p)
    chunks = []
    for sL, Lv in L.items():
        for sR, Rv in R.items():
            s = sL + sR
            if s % 2 != par or s > smax:
                continue
            for i0 in range(0, len(Lv), 2048):
                a = Lv[i0:i0 + 2048][:, None]
                t = a + Rv[None, :]
                wrap = t < a  # uint64 carry
                t = t + corr * wrap.astype(np.uint64)
                t = np.where(t >= pp, t - pp, t)
                chunks.append(t.ravel())
    allv = np.concatenate(chunks)
    return len(np.unique(allv))


# ---------- T1/T2: the analytic identities (numerical, high precision) ----------

def part1_identities():
    print("\n== Part 1: orthogonality identity + AM-GM norm bound (numeric) ==")
    rng = np.random.default_rng(232)
    for m in (8, 16, 32, 64):
        half = m // 2
        zeta = np.exp(2j * np.pi / m)
        embeds = [i for i in range(m) if i % 2 == 1]  # (Z/m)^x for m = 2^k
        ok_orth, ok_amgm = True, True
        for _ in range(40):
            c = rng.integers(-2, 3, size=half)
            if not c.any():
                continue
            sig = np.array([sum(int(c[j]) * zeta ** (i * j) for j in range(half))
                            for i in embeds])
            lhs = float(np.sum(np.abs(sig) ** 2))
            rhs = float(half * np.sum(c.astype(float) ** 2))
            if abs(lhs - rhs) > 1e-6 * max(1.0, rhs):
                ok_orth = False
            normabs = float(np.prod(np.abs(sig)))
            bound = float(np.sum(c.astype(float) ** 2)) ** (m / 4)
            if normabs > bound * (1 + 1e-9):
                ok_amgm = False
        check(f"T1 orthogonality m={m}", ok_orth)
        check(f"T2 AM-GM norm bound m={m}", ok_amgm)


# ---------- cross-validation: pattern method == brute subsets ----------

def part2_crossvalidation():
    print("\n== Part 2: pattern parametrization == brute-force subset enumeration ==")
    for (m, p, rs) in ((8, 257, (3, 4, 5)), (16, 786433, (5, 8, 9))):
        for r in rs:
            P = patterns(m, r)
            a = image_small(p, m, r, P)
            b = image_brute(p, m, r)
            check(f"cross-val m={m} p={p} r={r}", a == b, f"pattern={a} brute={b}")
            check(f"pattern count == N0 admissible m={m} r={r}", len(P) == N0(m, r),
                  f"|patterns|={len(P)} N0={N0(m, r)}")


# ---------- T3: collision-onset scans (exhaustive below ~2.2M) ----------

def primes_upto(n: int) -> np.ndarray:
    sieve = np.ones(n + 1, dtype=bool)
    sieve[:2] = False
    for i in range(2, int(n ** 0.5) + 1):
        if sieve[i]:
            sieve[i * i::i] = False
    return np.flatnonzero(sieve)


def part3_onset():
    print("\n== Part 3: exhaustive collision-onset scan vs threshold T(m,r) ==")
    results = {}
    pr = primes_upto(2_200_000)
    for m, rs, bound in ((8, (3, 4, 5), 1100), (16, (5, 8, 9), 2_200_000)):
        ps = [int(p) for p in pr[(pr % m == 1) & (pr <= bound)]]
        for r in rs:
            P = patterns(m, r)
            n0 = N0(m, r)
            T = T_threshold(m, r)
            deficient = []
            for p in ps:
                if image_small(p, m, r, P) != n0:
                    deficient.append(p)
            worst = max(deficient) if deficient else None
            results[(m, r)] = (worst, T)
            ok = (worst is None) or (worst <= T)
            tight = f"{worst}/{T} = {worst / T:.3f}" if worst else f"none/{T}"
            check(f"T3 onset m={m} r={r}: no deficient prime > T", ok,
                  f"largest deficient p (1 mod {m}) = {worst}, T(m,r) = {T}, "
                  f"tightness {tight}; #deficient={len(deficient)}; scanned p<= {bound}")
    return results


# ---------- T4: m=32 exact images (MITM) — predictions + transition map ----------

GOLDILOCKS = (1 << 64) - (1 << 32) + 1
BABYBEAR = 15 * (1 << 27) + 1


def part4_m32():
    print("\n== Part 4: m=32 exact images — Goldilocks prediction + transition map ==")
    m = 32
    for r, pred in ((17, 21_523_360), (16, 21_523_361)):
        assert N0(m, r) == pred, (r, N0(m, r))
        t0 = time.time()
        img = image_mitm(GOLDILOCKS, m, r)
        check(f"T4 Goldilocks m=32 r={r} image == N0 == {pred}", img == pred,
              f"image={img} ({time.time() - t0:.1f}s)  [T(32,{r})={T_threshold(m, r)} "
              f"≈ 2^{math.log2(T_threshold(m, r)):.2f} < p ≈ 2^64 — covered]")
    print("\n-- transition map (m=32, r=17): exact image vs prime size --")
    print(f"   N0 = {N0(32, 17)};  T(32,17) = {T_threshold(32, 17)} ≈ 2^{math.log2(T_threshold(32, 17)):.2f}")
    samples = []
    for k in (26, 28, 31, 34, 38, 42, 45, 47, 48, 50, 56):
        p = BABYBEAR if k == 31 else smallest_prime_1mod(32, 1 << k)
        t0 = time.time()
        img = image_mitm(p, 32, 17)
        frac = img / N0(32, 17)
        name = " (BabyBear)" if p == BABYBEAR else ""
        samples.append((p, img))
        print(f"   p ≈ 2^{math.log2(p):6.2f}{name:12s} image = {img:>10,}  "
              f"= {frac:7.4%} of N0   ({time.time() - t0:.1f}s)")
    bb_img = dict(samples).get(BABYBEAR)
    print(f"   BabyBear exact m=32 r=17 image: {bb_img:,} "
          f"({bb_img / N0(32, 17):.4%} of N0) — refines the earlier sampled ≈5.6M estimate")
    above_T_bad = [p for p, img in samples if p > T_threshold(32, 17) and img != N0(32, 17)]
    check("T3/T4 m=32: every sampled p > T(32,17) is exact", not above_T_bad,
          f"violations: {above_T_bad}")
    emp_bad = [p for p, img in samples if p >= (1 << 34) and img != N0(32, 17)]
    check("EMPIRICAL regression lock (data, not a consequence of E2): "
          "ladder rows p >= 2^34 all exact", not emp_bad, f"violations: {emp_bad}")


# ---------- summary tables for the note ----------

def part5_tables():
    print("\n== Part 5: threshold / breach-window tables (for the note) ==")
    print("   NOTE: raw exactness/breach windows (log2 T, 128+log2 N0). The delta*-existence")
    print("   clamp (lower end max(T, 2^129)) is applied note-side; sub-2^129 rows are")
    print("   eps_mca-floor statements only, not delta* pins.")
    print(f"{'rho':>6} {'m':>4} {'r':>4} {'log2 N0':>8} {'log2 T':>8} {'log2 ceil':>9}  window (per-prime, unconditional)")
    for rho_num, rho_den in ((1, 2), (1, 4), (1, 8), (1, 16)):
        for m in (8, 16, 32, 64, 128):
            if (m * rho_num) % rho_den:
                continue
            r = m * rho_num // rho_den + 1
            if r < 2 or r > m - 1:
                continue
            n0 = N0(m, r)
            T = T_threshold(m, r)
            ceil_log = 128 + math.log2(n0)
            lo, hi = math.log2(T), ceil_log
            window = f"2^{lo:.1f} < p < 2^{hi:.1f}" if hi > lo else "EMPTY (averaged-only)"
            print(f"{rho_num}/{rho_den:>4} {m:>4} {r:>4} {math.log2(n0):8.2f} {lo:8.2f} {hi:9.2f}  {window}")


if __name__ == "__main__":
    t0 = time.time()
    part1_identities()
    part2_crossvalidation()
    part3_onset()
    part4_m32()
    part5_tables()
    print(f"\nTotal: {time.time() - t0:.1f}s; failures: {FAILURES or 'none'}")
    sys.exit(1 if FAILURES else 0)
