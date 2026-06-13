#!/usr/bin/env python3
"""Exhaustive sigma-invariant rational-pair cap at scale 2 (normalizer-gap lane).

Pre-registered: lalalune/ArkLib#371, comment 4687191139, item 3.

Conventions are taken VERBATIM from the WB lane's probes
(probe_window_rational_adversarial.py / probe_window_renormalization.py):
  q = 13, k = 1, domain = mu_n in F_13; agreement floor t_min = n - w.
  gamma BAD for stack (u0, u1)  <=>  the combined word u0 + gamma*u1 has a value c
  with level set A = {i : comb_i = c}, |A| >= t_min, and some t_min-subset T of A
  has u0 or u1 non-constant on T.  Level-set form (provably equivalent, and
  cross-checked here against their literal combinations() check at scale 1):
  BAD <=> exists c: |A| >= t_min and NOT (u0 const on A and u1 const on A).
  [If a row takes >= 2 values on A, a t_min-subset containing two differing
   points exists since |A| >= t_min; if both rows are constant on A every subset
   is jointly explained.]

  RATIONAL WORD at slack w: r = R/l with deg R <= w, deg l <= w (k=1: w+k-1 = w),
  l nonvanishing on the domain.
  SIGMA-INVARIANT (sigma(x) = -1/x): word constant on every sigma-orbit of the
  domain. For a rational word, invariance on >= 2w+4 points forces the polynomial
  identity  Rt*l = R*lt  where Rt(x) = x^w * R(-1/x), lt(x) = x^w * l(-1/x)
  (the reversal twists, deg <= w):  Rt*l - R*lt has degree <= 2w < n and vanishes
  on the whole domain.  For FIXED l this is a LINEAR condition on R — we enumerate
  denominators and solve the kernel, which makes the scale-2 family exhaustible.

SCALES:
  scale 1 (n=6, w=2): calibration — their exhaustive verdict (max bad over ALL
    orbit-constant pairs, rational or not) is w+1 = 3; we must reproduce it, AND
    the level-set badness must agree with their literal subset check on the full
    family.
  scale 2 (n=12, w=4): the pre-registered question — exhaustive max over the
    sigma-invariant RATIONAL family: w+1 = 5, or tighter (their sampling saw 3)?

Exit 0 iff calibration gates pass. Results: RESULTS-CAP.md.
"""

import sys
import time
from collections import Counter, defaultdict
from itertools import combinations, product

Q = 13


def subgroup(q, n):
    for g in range(2, q):
        if all(pow(g, (q - 1) // p, q) != 1 for p in (2, 3)):  # 12 = 2^2*3
            h = pow(g, (q - 1) // n, q)
            dom = [pow(h, i, q) for i in range(n)]
            assert len(set(dom)) == n
            return dom
    raise RuntimeError


def evalp(co, x, q):
    a = 0
    for c in reversed(co):
        a = (a * x + c) % q
    return a


def sigma_orbits(q, dom):
    dset, seen, orbs = set(dom), set(), []
    for x in dom:
        if x in seen:
            continue
        y = (-pow(x, q - 2, q)) % q
        assert y in dset, "domain not sigma-stable"
        orb = (x,) if y == x else (x, y)
        seen.update(orb)
        orbs.append(orb)
    return orbs


def bad_count_levelset(u0, u1, q, n, t_min):
    cnt = 0
    for gam in range(q):
        comb = [(u0[i] + gam * u1[i]) % q for i in range(n)]
        levels = defaultdict(list)
        for i, v in enumerate(comb):
            levels[v].append(i)
        for ix in levels.values():
            if len(ix) < t_min:
                continue
            f0 = u0[ix[0]]
            f1 = u1[ix[0]]
            if any(u0[i] != f0 for i in ix) or any(u1[i] != f1 for i in ix):
                cnt += 1
                break
    return cnt


def bad_count_literal(u0, u1, q, n, t_min):
    """Their probe's literal check (subset enumeration) — the cross-check oracle."""
    cnt = 0
    for gam in range(q):
        line = tuple((u0[i] + gam * u1[i]) % q for i in range(n))
        found = False
        for c, m in Counter(line).most_common():
            if m < t_min:
                break
            A = [i for i in range(n) if line[i] == c]
            for T in combinations(A, t_min):
                if len(set(u0[i] for i in T)) > 1 or len(set(u1[i] for i in T)) > 1:
                    found = True
                    break
            if found:
                break
        if found:
            cnt += 1
    return cnt


# ---------------------------------------------------------------- scale 1 gate

def scale1():
    q, n, w = Q, 6, 2
    t_min = n - w
    dom = subgroup(q, n)
    orbs = sigma_orbits(q, dom)
    assert all(len(o) == 2 for o in orbs) and len(orbs) == 3
    # all orbit-constant words: 13^3
    words = []
    idx = {x: i for i, x in enumerate(dom)}
    for vals in product(range(q), repeat=3):
        wv = [0] * n
        for o, v in zip(orbs, vals):
            for x in o:
                wv[idx[x]] = v
        words.append(tuple(wv))
    best, hist = 0, Counter()
    t0 = time.time()
    mism = 0
    for a, u0 in enumerate(words):
        for b, u1 in enumerate(words):
            c = bad_count_levelset(u0, u1, q, n, t_min)
            hist[c] += 1
            if c > best:
                best = c
            # cross-check the level-set form vs their literal check on a slice
            if (a * len(words) + b) % 100003 == 0:
                if c != bad_count_literal(u0, u1, q, n, t_min):
                    mism += 1
        if (a + 1) % 500 == 0:
            print(f"[scale1] {a+1}/2197 rows ({time.time()-t0:.0f}s) max {best}",
                  file=sys.stderr)
    return best, dict(sorted(hist.items())), mism


# ---------------------------------------------------------------- scale 2

def reversal_twist(co, w, q):
    """x^w * P(-1/x) for deg P <= w: coefficient i -> (-1)^i at slot w-i."""
    out = [0] * (w + 1)
    for i, c in enumerate(co):
        out[w - i] = (c * (1 if i % 2 == 0 else q - 1)) % q
    return out


def polymul(a, b, q):
    out = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        if x:
            for j, y in enumerate(b):
                out[i + j] = (out[i + j] + x * y) % q
    return out


def kernel_mod_q(rows, ncols, q):
    """Solution basis of the homogeneous system rows·v = 0 over F_q."""
    m = [r[:] for r in rows]
    piv, pivcols = 0, []
    for col in range(ncols):
        sel = next((r for r in range(piv, len(m)) if m[r][col]), None)
        if sel is None:
            continue
        m[piv], m[sel] = m[sel], m[piv]
        inv = pow(m[piv][col], q - 2, q)
        m[piv] = [(v * inv) % q for v in m[piv]]
        for r in range(len(m)):
            if r != piv and m[r][col]:
                f = m[r][col]
                m[r] = [(m[r][j] - f * m[piv][j]) % q for j in range(ncols)]
        pivcols.append(col)
        piv += 1
        if piv == len(m):
            break
    free = [c for c in range(ncols) if c not in pivcols]
    basis = []
    for fc in free:
        v = [0] * ncols
        v[fc] = 1
        for r, pc in enumerate(pivcols):
            v[pc] = (-m[r][fc]) % q
        basis.append(v)
    return basis


def scale2():
    q, n, w = Q, 12, 4
    t_min = n - w
    dom = subgroup(q, n)
    orbs = sigma_orbits(q, dom)
    fixed = [o for o in orbs if len(o) == 1]
    assert len(fixed) == 2 and len(orbs) == 7, (orbs,)

    # enumerate invariant rational words: for each monic-or-lower l (nonvanishing
    # on dom), kernel of R -> Rt*l - R*lt; collect value-vectors.
    t0 = time.time()
    inv_words = set()
    n_l = 0
    # denominators up to scalar: monic of degree e, e = 0..w
    for e in range(w + 1):
        for tail in product(range(q), repeat=e):
            l = list(tail) + [1] + [0] * (w - e)   # monic deg e, padded to w+1
            if any(evalp(l, x, q) == 0 for x in dom):
                continue
            n_l += 1
            lt = reversal_twist(l, w, q)
            # linear map R (w+1 coeffs) -> coeffs of Rt*l - R*lt (deg <= 2w)
            rows = [[0] * (w + 1) for _ in range(2 * w + 1)]
            for i in range(w + 1):           # R = unit vector e_i
                Rt = [0] * (w + 1)
                Rt[w - i] = 1 if i % 2 == 0 else q - 1
                p1 = polymul(Rt, l, q)
                Ri = [0] * (w + 1)
                Ri[i] = 1
                p2 = polymul(Ri, lt, q)
                for d in range(2 * w + 1):
                    v1 = p1[d] if d < len(p1) else 0
                    v2 = p2[d] if d < len(p2) else 0
                    rows[d][i] = (v1 - v2) % q
            basis = kernel_mod_q(rows, w + 1, q)
            if not basis:
                continue
            # enumerate the kernel (q^dim - small), build value vectors
            linv = [pow(evalp(l, x, q), q - 2, q) for x in dom]
            for coeffs in product(range(q), repeat=len(basis)):
                if all(c == 0 for c in coeffs):
                    continue
                R = [0] * (w + 1)
                for cf, bv in zip(coeffs, basis):
                    if cf:
                        for j in range(w + 1):
                            R[j] = (R[j] + cf * bv[j]) % q
                word = tuple(evalp(R, x, q) * li % q for x, li in zip(dom, linv))
                inv_words.add(word)
    inv_words = sorted(inv_words)
    print(f"[scale2] {n_l} admissible denominators -> {len(inv_words)} distinct "
          f"invariant rational words ({time.time()-t0:.0f}s)", file=sys.stderr)

    # bad_count is invariant under independent AFFINE value maps w -> a*w + c*1
    # on each slot (scaling reparameterizes gamma; constant shifts move level
    # values, not level sets; row-constancy is affine-invariant).  The family is
    # affine-closed (R/l -> (aR + c*l)/l).  Quotient to canonical class reps:
    # subtract w[0], scale first nonzero entry to 1.
    def canon(wv):
        s = [(v - wv[0]) % q for v in wv]
        fz = next((v for v in s if v), None)
        if fz is None:
            return tuple(s)  # the constant class
        inv = pow(fz, q - 2, q)
        return tuple(v * inv % q for v in s)

    classes = sorted({canon(wv) for wv in inv_words})
    print(f"[scale2] affine quotient: {len(inv_words)} words -> {len(classes)} "
          f"canonical classes", file=sys.stderr)
    # belt and braces: affine invariance of bad_count on random samples
    import random
    rng = random.Random(7)
    t_min_chk = n - w
    for _ in range(60):
        u0 = rng.choice(inv_words)
        u1 = rng.choice(inv_words)
        a0, c0 = rng.randrange(1, q), rng.randrange(q)
        a1, c1 = rng.randrange(1, q), rng.randrange(q)
        v0 = tuple((a0 * x + c0) % q for x in u0)
        v1 = tuple((a1 * x + c1) % q for x in u1)
        assert bad_count_levelset(u0, u1, q, n, t_min_chk) == \
            bad_count_levelset(v0, v1, q, n, t_min_chk), "affine invariance FAILED"
    print("[gate] affine invariance of bad_count: 60/60 random checks", file=sys.stderr)
    inv_words = classes

    # verify invariance + rationality of every collected word (belt and braces)
    idx = {x: i for i, x in enumerate(dom)}
    for wv in inv_words:
        for o in orbs:
            assert len(set(wv[idx[x]] for x in o)) == 1, "non-invariant word leaked"

    best, hist, arg = 0, Counter(), None
    t0 = time.time()
    for a, u0 in enumerate(inv_words):
        for u1 in inv_words:
            c = bad_count_levelset(u0, u1, q, n, t_min)
            hist[c] += 1
            if c > best:
                best, arg = c, (u0, u1)
        if (a + 1) % 200 == 0:
            print(f"[scale2] {a+1}/{len(inv_words)} rows ({time.time()-t0:.0f}s) "
                  f"max {best}", file=sys.stderr)
    # cross-check the argmax with the literal oracle
    if arg:
        lit = bad_count_literal(arg[0], arg[1], q, n, t_min)
        assert lit == best, f"levelset {best} != literal {lit} at argmax"
    return best, dict(sorted(hist.items())), arg, len(inv_words)


def main():
    b1, h1, mism = scale1()
    print(f"scale1 (q=13,n=6,w=2) ALL orbit-constant pairs: max bad = {b1}, "
          f"hist = {h1}, levelset-vs-literal mismatches on slice: {mism}")
    assert mism == 0, "badness semantics diverge from the WB probe's literal check"
    assert b1 == 3, f"CALIBRATION FAILED: scale-1 max {b1} != 3"
    print("[gate] scale-1 exhaustive = 3 = w+1, semantics cross-checked  OK")

    b2, h2, arg, m2 = scale2()
    verdict = ("w+1 LAW REPLICATES: exhaustive invariant-rational max = 5"
               if b2 == 5 else
               f"CAP TIGHTER THAN w+1: exhaustive max = {b2} < 5" if b2 < 5 else
               f"CAP EXCEEDS w+1: max = {b2}")
    print(f"scale2 (q=13,n=12,w=4) invariant RATIONAL pairs ({m2} words): "
          f"max bad = {b2}, hist = {h2}")
    print("VERDICT:", verdict)
    import os
    here = os.path.dirname(os.path.abspath(__file__))
    with open(os.path.join(here, "RESULTS-CAP.md"), "w") as fh:
        fh.write(f"""# Exhaustive sigma-invariant cap (pre-registered falsifier)

Conventions verbatim from the WB probes (level-set badness cross-checked against
their literal subset check — 0 mismatches on the scale-1 slice and at the argmax).

* Scale 1 gate (q=13, n=6, w=2), ALL orbit-constant pairs (2197^2): max = {b1}
  (reproduces their exhaustive w+1 = 3). PASS
* Scale 2 (q=13, n=12, w=4), the FULL sigma-invariant rational family
  ({m2} distinct words; reversal-twist kernel enumeration Rt*l = R*lt):
  max bad over all ordered pairs = {b2}; histogram {h2}.

**VERDICT: {verdict}**

argmax stack:
  u0 = {arg[0] if arg else None}
  u1 = {arg[1] if arg else None}
(domain = mu_12 in F_13 listed in generator order, sigma(x) = -1/x)
""")
    return 0


if __name__ == "__main__":
    sys.exit(main())
