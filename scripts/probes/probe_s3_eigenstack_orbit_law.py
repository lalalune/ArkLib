#!/usr/bin/env python3
"""S3 probe v2 (#357): the rotation-power eigenstack orbit law for exact MCA profiles.

CONTEXT. The exact bad-gamma profile of RS[F_13,12,6] (orbit-reduced probe, #334 A5)
is m=12 -> 1, 11 -> 2, 10 -> 3, 9 -> 12, 8 -> 13 (m = witness-size threshold,
delta = 1 - m/n), with the m=9 numerator equal to n = 12 at p = 13, 37, 61 (the
"flat numerator"). No existing theory explains the climb 1,2,3 or the flat 12.

THE LAW (v2; v1's pure-frequency form was PARTIALLY FALSIFIED, see below).
Domain rotation x -> hx induces a linear map R on syndromes with eigenvalue h^j on
the frequency-j component. For t | n, the power R^t has eigenvalue h^{tj}, so its
eigenspaces GROUP frequencies into classes {j : tj equal mod n}: higher powers have
multi-dimensional syndrome eigenspaces. A stack (s0, s1) is a sigma^t-EIGENSTACK if
    R^t s1 = c s1   and   R^t s0 = a s0 + b s1   (a, c nonzero).
For such a stack the affine line maps to itself under sigma^t reparametrized by
    T(gamma) = a^{-1} b + gamma * (a^{-1} c),
so the bad-gamma set is T-invariant: a union of T-orbits -- of size d = ord(a^{-1}c)
off the fixed point -- plus possibly the fixed point itself:

    count = eps + (#orbits) * d,   eps in {0,1},   d | n.

V1 RESULT (kept as regression): pure-frequency (t=1) eigenstacks ATTAIN the exact
max at the delta=0 rung (1 = fixed point), the plateau rung (12 = ONE full order-12
orbit, attainer (j0,j1)=(9,8)) and the breakdown rungs (13 = fixed + orbits), but
NOT the intermediate rungs (m=11 -> 2, m=10 -> 3; eig-max 1). Same gap at
(7,6,3)/(13,6,3) m=5.

V2 HYPOTHESES (pre-registered):
  H1' (rotation-power extremality): every rung max is attained by a sigma^t-
      eigenstack for some t | n. Specifically at (13,12,6): m=11 by a sigma^6-
      eigenstack (alpha = -1, bad set an ANTIPODAL PAIR {g0, -g0}); m=10 by a
      sigma^4-eigenstack (alpha = omega of order 3, bad set an omega-TRIPLE).
      At (p,6,3): m=5 by a sigma^3-eigenstack (alpha = -1, antipodal pair).
  H2 (orbit structure): every sigma^t-eigenstack bad set decomposes exactly as
      eps*{fixed} + union of d-orbits (asserted on every tested eigenstack).
  H3 (field-independence): the (12,6) m=9 ONE-ORBIT attainer reproduces count
      12 = one order-12 coset at p = 37 and p = 61 (where F* has 36/60 elements,
      so 12 is a proper subgroup coset, not F* itself).
  H5 (maximizer census at (13,6,3) m=5): among ALL exact maximizers (count-2
      stacks from full enumeration), sigma^3-eigenstacks occur; report the
      structured fraction.

Witness discipline: ext semantics identical to probe_exact_epsmca_ladder
(imported); small instances cross-checked against full enumeration; the
(13,12,6) reference profile is the recorded A5 exact output. Exit 0 iff all
assertions pass.
"""

import importlib.util
import os
import sys
from itertools import combinations, product
from math import gcd, sqrt

_here = os.path.dirname(os.path.abspath(__file__))
_spec = importlib.util.spec_from_file_location(
    "ladder", os.path.join(_here, "probe_exact_epsmca_ladder.py"))
ladder = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(ladder)


# ------------------------------------------------------------------ instance

class Inst:
    def __init__(self, p, n, k, min_size=None):
        self.p, self.n, self.k = p, n, k
        self.xs = ladder.smooth_domain(p, n)           # xs[i] = h^i
        self.h = self.xs[1]
        G = [[pow(x, j, p) for x in self.xs] for j in range(k)]
        self.H = ladder.nullspace(G, p)
        assert len(self.H) == n - k
        lo = (k + 1) if min_size is None else min_size
        self.subsets = []
        for size in range(lo, n + 1):
            self.subsets.extend(combinations(range(n), size))
        self.adm = {m: ladder.admissible_mask(self.subsets, m)
                    for m in range(lo, n + 1)}
        self._ext = {}
        self.R = self._rotation()

    def freq_word(self, j):
        return [pow(x, j, self.p) for x in self.xs]

    def syndrome(self, w):
        return tuple(sum(hr[i] * w[i] for i in range(self.n)) % self.p
                     for hr in self.H)

    def _rotation(self):
        """Matrix R on syndromes induced by w -> w o sigma, sigma(i) = i+1."""
        p, n, d = self.p, self.n, self.n - self.k
        R = []
        for i in range(d):
            e = [0] * d
            e[i] = 1
            w = ladder.solve_particular(self.H, e, p)
            wr = [w[(a + 1) % n] for a in range(n)]
            R.append([sum(hr[j] * wr[j] for j in range(n)) % p for hr in self.H])
        # R as column-action: R[i] is image of basis syndrome e_i; transpose to act
        Rt = [[R[c][r] for c in range(d)] for r in range(d)]
        # verify on a few random words
        import random
        rng = random.Random(p * 100 + n)
        for _ in range(16):
            w = [rng.randrange(p) for _ in range(n)]
            s = self.syndrome(w)
            wr = [w[(a + 1) % n] for a in range(n)]
            sr = self.syndrome(wr)
            got = tuple(sum(Rt[r][c] * s[c] for c in range(d)) % p for r in range(d))
            assert got == sr, "rotation matrix mismatch"
        return Rt

    def rot_pow(self, s, t):
        """R^t applied to syndrome s."""
        d = self.n - self.k
        v = list(s)
        for _ in range(t % self.n):
            v = [sum(self.R[r][c] * v[c] for c in range(d)) % self.p
                 for r in range(d)]
        return tuple(v)

    def ext_mask(self, s):
        if s not in self._ext:
            w = ladder.solve_particular(self.H, list(s), self.p)
            mask = 0
            for bit, S in enumerate(self.subsets):
                if ladder.ext_from(w, list(S), self.xs, self.k, self.p):
                    mask |= 1 << bit
            self._ext[s] = mask
        return self._ext[s]

    def bad_set(self, s0, s1, m):
        am = self.adm[m]
        notpair = ~(self.ext_mask(s0) & self.ext_mask(s1))
        out = []
        for g in range(self.p):
            line = tuple((a + g * b) % self.p for a, b in zip(s0, s1))
            if self.ext_mask(line) & notpair & am:
                out.append(g)
        return out


def coset_decompose(bad, alpha, beta, p):
    """Decompose bad as union of orbits of T(g) = alpha*g + beta.
    Returns (eps, d, ncosets) with eps = 1 iff the fixed point is in bad
    (alpha != 1: unique fixed point; alpha = 1, beta = 0: T = id, treat as
    d = 1, eps = 0, ncosets = len(bad)); None if bad is not T-invariant."""
    a, b = alpha % p, beta % p
    if a == 1 and b == 0:
        return 0, 1, len(bad)
    if a == 1:  # no fixed point; orbits all of size ord_add(beta) = p
        d = p
    else:
        fix = (b * pow(1 - a, p - 2, p)) % p
        d = 1
        x = a
        while x != 1:
            x = x * a % p
            d += 1
    s = set(bad)
    eps = 0
    if a != 1 and fix in s:
        eps = 1
        s.discard(fix)
    seen = set()
    nc = 0
    for x in sorted(s):
        if x in seen:
            continue
        orb = set()
        y = x
        while y not in orb:
            orb.add(y)
            y = (a * y + b) % p
        if not orb <= s:
            return None
        assert len(orb) == d, (orb, d)
        seen |= orb
        nc += 1
    return eps, d, nc


def eigen_data(inst, s0, s1, t):
    """If (s0,s1) is a sigma^t-eigenstack, return (a, b, c) with
    R^t s1 = c s1, R^t s0 = a s0 + b s1, a,c != 0; else None."""
    p = inst.p
    d = inst.n - inst.k
    r1 = inst.rot_pow(s1, t)
    # c: collinearity r1 = c s1
    c = None
    for i in range(d):
        if s1[i] % p:
            c = (r1[i] * pow(s1[i], p - 2, p)) % p
            break
    if c is None or c == 0:
        return None
    if any((c * s1[i] - r1[i]) % p for i in range(d)):
        return None
    if not any(s0):                      # s0 = 0: relation holds with a = 1, b = 0
        return 1, 0, c
    r0 = inst.rot_pow(s0, t)
    # solve r0 = a s0 + b s1 (2 unknowns, d equations) over F_p
    rows = [[s0[i], s1[i], r0[i]] for i in range(d)]
    red, piv = ladder.rref(rows, p)
    if 2 in piv:  # inconsistent
        return None
    a = b = 0
    for r, cidx in enumerate(piv):
        if cidx == 0:
            a = red[r][2]
        elif cidx == 1:
            b = red[r][2]
    if a == 0:
        return None
    if any((a * s0[i] + b * s1[i] - r0[i]) % p for i in range(d)):
        return None
    return a, b, c


def tmap_params(inst, a, b, c):
    """alpha, beta of T(g) = a^{-1} b + g a^{-1} c."""
    p = inst.p
    ainv = pow(a, p - 2, p)
    return (ainv * c) % p, (ainv * b) % p


# --------------------------------------------------- pure-frequency grid (v1)

def freq_grid_max(inst, rungs=None):
    """Max bad count per rung over (0|e_{j0}, e_{j1}) pure-frequency stacks,
    with H2 asserted on each. Returns best, attain (with orbit data)."""
    p, n, k = inst.p, inst.n, inst.k
    rungs = rungs or list(inst.adm)
    zero = tuple([0] * (n - k))
    best = {m: 0 for m in rungs}
    attain = {m: [] for m in rungs}
    freqs = list(range(k, n))
    for j1 in freqs:
        s1 = inst.syndrome(inst.freq_word(j1))
        for j0 in [None] + freqs:
            if j0 == j1:
                continue
            s0 = zero if j0 is None else inst.syndrome(inst.freq_word(j0))
            ed = eigen_data(inst, s0, s1, 1)
            assert ed is not None, f"pure pair (j0={j0},j1={j1}) not eigen?!"
            alpha, beta = tmap_params(inst, *ed)
            for m in rungs:
                bad = inst.bad_set(s0, s1, m)
                dec = coset_decompose(bad, alpha, beta, p)
                assert dec is not None, \
                    f"H2 FALSIFIED: t=1 stack (j0={j0},j1={j1}) m={m}: {bad}"
                eps, d, nc = dec
                if len(bad) > best[m]:
                    best[m] = len(bad)
                    attain[m] = []
                if len(bad) == best[m] and len(attain[m]) < 4:
                    attain[m].append(((j0, j1), eps, d, nc))
    return best, attain


# ------------------------------------------- sigma^t eigenclass search (v2)

def class_vectors(inst, freqs_in_class, cap=None):
    """All nonzero syndrome vectors in span{e_j : j in class}, mod scaling
    (first nonzero coefficient normalized to 1)."""
    p = inst.p
    base = [inst.syndrome(inst.freq_word(j)) for j in freqs_in_class]
    dcl = len(base)
    out = []
    for coeffs in product(range(p), repeat=dcl):
        nz = next((i for i, c in enumerate(coeffs) if c), None)
        if nz is None or coeffs[nz] != 1:
            continue
        v = tuple(sum(coeffs[i] * base[i][r] for i in range(dcl)) % p
                  for r in range(inst.n - inst.k))
        out.append((coeffs, v))
        if cap and len(out) >= cap:
            break
    return out


def class_search(inst, t, class1, class0, m, want, label, include_zero_s0=True):
    """Search sigma^t-eigenstacks with s1 in span(class1)\\0 (mod scale),
    s0 in span(class0) (full), at rung m. Returns hits with orbit decomposition.
    class0/class1: frequency lists."""
    p = inst.p
    s1v = class_vectors(inst, class1)
    s0v = class_vectors(inst, class0)
    s0all = [tuple([0] * (inst.n - inst.k))] if include_zero_s0 else []
    # include scalar multiples of class0 reps (s0 not mod scale: all multiples)
    for _, v in s0v:
        for lam in range(1, p):
            s0all.append(tuple(lam * x % p for x in v))
    hits = []
    checked = 0
    for _, s1 in s1v:
        ed1 = eigen_data(inst, s0all[0], s1, t)  # c from s1 alone via s0=0
        for s0 in s0all:
            ed = eigen_data(inst, s0, s1, t)
            if ed is None:
                continue
            checked += 1
            alpha, beta = tmap_params(inst, *ed)
            bad = inst.bad_set(s0, s1, m)
            dec = coset_decompose(bad, alpha, beta, p)
            assert dec is not None, \
                f"H2 FALSIFIED: sigma^{t} stack s0={s0} s1={s1} m={m}: {bad}"
            if len(bad) == want:
                hits.append((s0, s1, bad, dec))
                if len(hits) >= 3:
                    print(f"     [{label}] {checked} eigenstacks checked, "
                          f"first hits: ", flush=True)
                    for s0h, s1h, badh, dech in hits:
                        print(f"       s0={s0h} s1={s1h} bad={badh} "
                              f"(eps,d,#orb)={dech}")
                    return hits
    print(f"     [{label}] {checked} eigenstacks checked, "
          f"{len(hits)} hits with count {want}", flush=True)
    for s0h, s1h, badh, dech in hits[:3]:
        print(f"       s0={s0h} s1={s1h} bad={badh} (eps,d,#orb)={dech}")
    return hits


# ------------------------------------ full-enumeration maximizer census (H5)

def census_maximizers(inst, m, cap=300):
    """Full enumeration at rung m: exact max count + (capped) maximizer list."""
    p = inst.p
    d = inst.n - inst.k
    syn = list(product(range(p), repeat=d))
    for s in syn:
        inst.ext_mask(s)
    am = inst.adm[m]
    best, wits = 0, []
    for s0 in syn:
        e0 = inst.ext_mask(s0)
        for s1 in syn:
            if not any(s1):
                continue
            notpair = ~(e0 & inst.ext_mask(s1))
            cnt = 0
            for g in range(p):
                line = tuple((a + g * b) % p for a, b in zip(s0, s1))
                if inst.ext_mask(line) & notpair & am:
                    cnt += 1
            if cnt > best:
                best, wits = cnt, []
            if cnt == best and len(wits) < cap:
                wits.append((s0, s1))
    return best, wits


def classify_stack(inst, s0, s1, divisors):
    """Smallest t in divisors for which (s0,s1) is a sigma^t-eigenstack."""
    for t in divisors:
        if eigen_data(inst, s0, s1, t) is not None:
            return t
    return None


# --------------------------------------------------------------------- main

if __name__ == "__main__":
    print("S3 eigenstack orbit-law probe v2 (#357)")

    # ---- stage A: n=4 regression (v1 result; H1 t=1 suffices there) -------
    print("\n== stage A: n=4 regression (t=1 grid attains everything) ==")
    for (p, n, k) in [(5, 4, 2), (13, 4, 2)]:
        inst = Inst(p, n, k)
        exact, _ = ladder.eps_profile_syndrome(p, n, k)
        best, attain = freq_grid_max(inst)
        print(f"   RS[F_{p},{n},{k}]: exact={exact}  t=1 eig-max={best}")
        assert best == {m: exact[m] for m in best}, "n=4 regression FAILED"
    print("   [OK] n=4: t=1 eigenstacks attain the full exact profile")

    # ---- stage B: (p,6,3) m=5 gap -> sigma^3 class + maximizer census -----
    print("\n== stage B: the m=5 count-2 rung at n=6 (v1 gap) ==")
    for p in (7, 13):
        inst = Inst(p, 6, 3)
        # sigma^3 eigenclasses: R^3 eigenvalue (-1)^j on freq j; syndrome
        # freqs {3,4,5}: odd {3,5} (-1), even {4} (+1)
        print(f"   RS[F_{p},6,3] sigma^3 class search at m=5, want count 2:")
        hits1 = class_search(inst, 3, [3, 5], [4], 5, 2, f"p={p} s1-odd/s0-even")
        hits2 = class_search(inst, 3, [4], [3, 5], 5, 2, f"p={p} s1-even/s0-odd")
        assert hits1 or hits2, \
            f"H1' FALSIFIED at (p={p},6,3) m=5: no sigma^3 eigenstack attains 2"
        for (s0, s1, bad, (eps, d, nc)) in (hits1 + hits2)[:3]:
            assert d == 2 and eps + 2 * nc == 2, f"unexpected decomposition"
            # antipodal-pair check: T(g) = alpha g + beta with ord(alpha)=2
        print(f"   [OK] (p={p}): count-2 attained by sigma^3 eigenstacks; "
              f"bad sets are single T-orbits (antipodal up to the T-map)")

    # H5 census at (13,6,3) m=5: how structured are ALL maximizers?
    print("\n   H5 maximizer census at RS[F_13,6,3], m=5 (full enumeration):")
    inst13 = Inst(13, 6, 3)
    best5, wits5 = census_maximizers(inst13, 5, cap=300)
    assert best5 == 2, f"expected exact max 2 at m=5, got {best5}"
    tally = {}
    for s0, s1 in wits5:
        t = classify_stack(inst13, s0, s1, [1, 2, 3, 6])
        tally[t] = tally.get(t, 0) + 1
    print(f"     max=2; first {len(wits5)} maximizers by minimal eigen power t: "
          f"{tally}")
    print(f"     (None = not a sigma^t-eigenstack for any t | 6 -- unstructured)")

    # ---- stage C: (13,12,6) pure grid regression (v1 result) --------------
    print("\n== stage C: (13,12,6) t=1 grid regression ==")
    A5 = {12: 1, 11: 2, 10: 3, 9: 12, 8: 13, 7: 13}
    inst12 = Inst(13, 12, 6)
    best12, attain12 = freq_grid_max(inst12)
    print(f"   t=1 eig-max: {best12}")
    for m, want in A5.items():
        ok = best12[m] == want
        print(f"     m={m:>2}: t=1 max {best12[m]:>2} vs exact {want:>2}  "
              f"{'ATTAINS' if ok else 'gap -> needs higher t'}")
    assert best12[9] == 12 and best12[12] == 1 and best12[8] == 13 and best12[7] == 13

    # ---- stage D: (13,12,6) sigma^6 / sigma^4 class searches at m=11,10 ---
    print("\n== stage D: the m=11 (count 2) and m=10 (count 3) rungs ==")
    inst12r = Inst(13, 12, 6, min_size=10)   # only need subsets of size >= 10
    # sigma^6: R^6 eigenvalue (-1)^j; syndrome freqs 6..11: even {6,8,10},
    # odd {7,9,11}
    print("   sigma^6 search at m=11, want count 2 (predict antipodal pair):")
    h11 = class_search(inst12r, 6, [7, 9, 11], [6, 8, 10], 11, 2, "s1-odd/s0-even")
    if not h11:
        h11 = class_search(inst12r, 6, [6, 8, 10], [7, 9, 11], 11, 2,
                           "s1-even/s0-odd")
    assert h11, "H1' FALSIFIED at (13,12,6) m=11: no sigma^6 eigenstack attains 2"
    for (s0, s1, bad, (eps, d, nc)) in h11[:3]:
        assert eps + d * nc == 2
    print("   [OK] m=11 count-2 attained by sigma^6 eigenstacks")

    # sigma^4: R^4 eigenvalue (h^4)^j of order 3; classes {6,9},{7,10},{8,11}
    print("   sigma^4 search at m=10, want count 3 (predict omega-triple):")
    h10 = []
    cls = [[6, 9], [7, 10], [8, 11]]
    for c1 in cls:
        for c0 in cls:
            if c1 == c0:
                continue
            h10 = class_search(inst12r, 4, c1, c0, 10, 3,
                               f"s1-{c1}/s0-{c0}")
            if h10:
                break
        if h10:
            break
    assert h10, "H1' FALSIFIED at (13,12,6) m=10: no sigma^4 eigenstack attains 3"
    for (s0, s1, bad, (eps, d, nc)) in h10[:3]:
        assert eps + d * nc == 3
    print("   [OK] m=10 count-3 attained by sigma^4 eigenstacks")

    # ---- stage E: field independence of the m=9 one-orbit law -------------
    print("\n== stage E: H3 field-independence of the m=9 plateau ==")
    for p in (37, 61):
        inst = Inst(p, 12, 6, min_size=9)
        best, attain = freq_grid_max(inst, rungs=[9])
        a9 = attain[9][0] if attain[9] else None
        print(f"   p={p}: m=9 t=1 eig-max = {best[9]}  attainer={a9}")
        assert best[9] == 12, f"H3 FALSIFIED at p={p}: m=9 max {best[9]} != 12"
        (j0, j1), eps, d, nc = a9
        assert eps == 0 and d == 12 and nc == 1, \
            f"H3 structure FALSIFIED at p={p}: not a single order-12 orbit: {a9}"
        print(f"     [OK] count 12 = ONE order-12 orbit (a proper coset: "
              f"|F*| = {p-1}), eps=0")

    print("\n== VERDICTS ==")
    print("  H1' rotation-power extremality: every rung of every tested instance")
    print("      attained by a sigma^t-eigenstack (t=1 except: m=11 via sigma^6,")
    print("      m=10 via sigma^4, n=6 m=5 via sigma^3)  [CONFIRMED]")
    print("  H2  orbit structure (eps + #orbits*d): asserted on every eigenstack")
    print("      tested, all rungs  [CONFIRMED]")
    print("  H3  the flat numerator = ONE order-12 orbit at p=13, 37, 61")
    print("      [CONFIRMED -- field-independence explained]")
    print("  H5  maximizer census: see tally above")
    print("\nall assertions passed")
