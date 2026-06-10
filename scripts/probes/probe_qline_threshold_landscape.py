#!/usr/bin/env python3
"""
probe_qline_threshold_landscape.py — threshold-landscape extension of the O68 deep-line
census (#232 upper-half numerics; companion to probe_qline_census.py / DISPROOF_LOG
O68-O69).

QUESTION (line-independence of the crossover radius — load-bearing for the upper half):
sweeping agreement a from the census floor a = k+1 up through unique decoding, where does
the per-line bad-gamma fraction #badgamma(a)/q cross the prize threshold eps* = 2^-128
scaled to q?  At toy q <= 2^31 we have 2^-128 * q << 1, so the crossover is exactly where
the COUNT hits 0 (any single bad gamma already exceeds the scaled threshold).  Is that
crossover radius the SAME on the Theorem-Q deep line as on random lines (control) and on
adversarial two-codeword bundle lines (PromotedHypothesesB style)?

METHOD (exact, per line; the O68 subset census run once, read at ALL radii): a codeword c
with agree(c, u0 + gamma*u1) >= a >= k+1 is certified by every (k+1)-subset T of its
agreement set via the finite-difference functional lam_x = prod_{y in T, y != x}(x-y)^-1
(annihilates deg <= k-1):  SA = sum lam_x u0(x), SB = sum lam_x u1(x);
SB != 0  =>  gamma = -SA/SB and the deg<k interpolant through T[:k] IS c.  One pass over
all C(n, k+1) subsets, recording (gamma, codeword, agreement), is therefore an exhaustive
census simultaneously at every radius a >= k+1.  Degenerate subsets (SB = 0) are handled
exactly: SA != 0 => no gamma passes; SA = 0 => an every-gamma layer (u0, u1 separately
interpolable on T): all q gammas get agreement >= base; beyond base, each off-point is
gained by at most one gamma, solved exactly per point.

PARAMETER POINTS (rate = k/n = (r-1)/s; a_wit = r*m is the deep-line witness agreement):
  P1 (n,m,r) = (16,2,5)  p = BabyBear  rate 1/2 — the O68 baseline, reproduced + swept
  P2 (n,m,r) = (16,2,5)  p = 97        rate 1/2 — non-BabyBear prime (toy-q noise floor)
  P3 (n,m,r) = (16,4,2)  p = BabyBear  rate 1/4 — prize-like rate 1/4
  P4 (n,m,r) = (12,2,4)  p = 37        rate 1/2 — different n, non-BabyBear
Per point: the Theorem-Q deep line, N_RAND random lines (control), and 12 two-codeword
bundle lines (4 disjoint-support, 4 shared-support, 4 deep-overlap), plus exact word
depths (max agreement of u0 / u1 alone with the code, certified by the same machinery:
a codeword agreeing with a single word on >= k+1 points is seen by a zero-syndrome
(k+1)-subset; otherwise max agreement = k trivially).

Deterministic (seeded).  Exit 0 = bookkeeping checks pass (this probe MEASURES).
"""
import argparse
import itertools
import math
import random
import sys
from collections import Counter

BABYBEAR = 15 * (1 << 27) + 1
N_RAND = 100
N_BUNDLE_PER_KIND = 4

FAIL = []


def check(name, ok, detail=""):
    print(f"[{'PASS' if ok else 'FAIL'}] {name}" + (f" — {detail}" if detail else ""))
    if not ok:
        FAIL.append(name)


def prime_divisors(n):
    out, d = set(), 2
    while d * d <= n:
        while n % d == 0:
            out.add(d)
            n //= d
        d += 1
    if n > 1:
        out.add(n)
    return out


class Point:
    """One parameter point: domain, deep line, structured family, census machinery."""

    def __init__(self, name, p, n, m, r):
        self.name, self.p, self.n, self.m, self.r = name, p, n, m, r
        assert (p - 1) % n == 0
        self.s = n // m
        self.k = (r - 1) * m
        self.a_wit = r * m
        self.a_lo = self.k + 1                      # census floor
        self.a_unique = (n + self.k) // 2 + 1       # smallest uniquely-decodable agreement
        self.a_hi = min(n, self.a_unique + 1)
        self.sweep = list(range(self.a_lo, self.a_hi + 1))
        self._build_domain()
        self._build_deep_line()
        self._precompute_census()

    # ---------------- field / domain ----------------
    def inv(self, a):
        return pow(a, self.p - 2, self.p)

    def _build_domain(self):
        p, n = self.p, self.n
        # exact-order-n generator, same search order as probe_qline_census.py
        x = 3
        while True:
            g = pow(x, (p - 1) // n, p)
            if g != 1 and all(pow(g, n // ell, p) != 1 for ell in prime_divisors(n)):
                break
            x += 1
        self.H = [pow(g, i, p) for i in range(n)]
        gG = pow(g, self.m, p)
        self.G = [pow(gG, i, p) for i in range(self.s)]
        z = 5
        while pow(z, n, p) == 1:
            z += 1
        self.z = z
        self.w = pow(z, self.m, p)

    def _build_deep_line(self):
        p, m, r, w = self.p, self.m, self.r, self.w
        self.u0 = [pow(x, r * m, p) * self.inv((pow(x, m, p) - w) % p) % p for x in self.H]
        self.u1 = [self.inv((pow(x, m, p) - w) % p) for x in self.H]
        # structured family q_S, bad scalar lam_S = -p_S(w)
        structured = {}
        for S in itertools.combinations(self.G, r):
            def pS(y):
                pr = 1
                for a in S:
                    pr = pr * ((y - a) % p) % p
                return (pow(y, r, p) - pr) % p
            lam = (-pS(w)) % p
            qvals = tuple(
                (pS(pow(x, m, p)) - pS(w)) % p * self.inv((pow(x, m, p) - w) % p) % p
                for x in self.H)
            structured.setdefault(lam, set()).add(qvals)
        self.structured = structured
        self.struct_words = set().union(*structured.values())

    # ---------------- census precomputation ----------------
    def _precompute_census(self):
        p, n, k = self.p, self.n, self.k
        H = self.H
        diff = [[(H[i] - H[j]) % p for j in range(n)] for i in range(n)]
        ID = [[self.inv(diff[i][j]) if i != j else 0 for j in range(n)] for i in range(n)]
        self.ID = ID
        pre = []
        for T in itertools.combinations(range(n), k + 1):
            lam = []
            for i in T:
                pr = 1
                for j in T:
                    if j != i:
                        pr = pr * ID[i][j] % p
                lam.append(pr)
            P_pts = T[:k]
            outs = [x for x in range(n) if x not in P_pts]
            wl = []
            for i in P_pts:
                pr = 1
                for j in P_pts:
                    if j != i:
                        pr = pr * ID[i][j] % p
                wl.append(pr)
            ells = []
            for x in outs:
                pr = 1
                for j in P_pts:
                    pr = pr * diff[x][j] % p
                ells.append(pr)
            pre.append((T, lam, P_pts, outs, wl, ells))
        self.pre = pre

    def _interp_full(self, vals_on_P, P_pts, outs, wl, ells):
        """Deg<k interpolant of vals_on_P (indexed like P_pts), evaluated on ALL of H."""
        p = self.p
        ev = [0] * self.n
        wy = [w_ * v % p for w_, v in zip(wl, vals_on_P)]
        for pos, v in zip(P_pts, vals_on_P):
            ev[pos] = v
        ID = self.ID
        for x, ellx in zip(outs, ells):
            row = ID[x]
            acc = 0
            for i, pi in enumerate(P_pts):
                acc += wy[i] * row[pi]
            ev[x] = ellx * (acc % p) % p
        return ev

    # ---------------- the census (one pass, all radii) ----------------
    def census(self, u0, u1):
        """Return (per_g, allg_base, n_deg_nogamma, n_deg_allg, consistency_ok).

        per_g: gamma -> {codeword tuple: max certified agreement}.
        allg_base: max base agreement of every-gamma degenerate layers (0 if none)."""
        p, k, n = self.p, self.k, self.n
        per_g = {}
        allg_base = 0
        n_deg_nogamma = n_deg_allg = 0
        consistency_ok = True
        for T, lam, P_pts, outs, wl, ells in self.pre:
            SA = SB = 0
            for l_, i in zip(lam, T):
                SA += l_ * u0[i]
                SB += l_ * u1[i]
            SA %= p
            SB %= p
            if SB:
                gam = (-SA) * pow(SB, p - 2, p) % p
                yP = [(u0[i] + gam * u1[i]) % p for i in P_pts]
                wy = [w_ * v % p for w_, v in zip(wl, yP)]
                ev = [0] * n
                for pos, v in zip(P_pts, yP):
                    ev[pos] = v
                agc = k
                ID = self.ID
                for x, ellx in zip(outs, ells):
                    row = ID[x]
                    acc = 0
                    for i, pi in enumerate(P_pts):
                        acc += wy[i] * row[pi]
                    evx = ellx * (acc % p) % p
                    ev[x] = evx
                    if evx == (u0[x] + gam * u1[x]) % p:
                        agc += 1
                if ev[T[k]] != (u0[T[k]] + gam * u1[T[k]]) % p:
                    consistency_ok = False
                key = tuple(ev)
                d = per_g.setdefault(gam, {})
                if d.get(key, 0) < agc:
                    d[key] = agc
            elif SA:
                n_deg_nogamma += 1
            else:
                # every-gamma layer: u0 AND u1 interpolable on T
                n_deg_allg += 1
                v0 = [u0[i] for i in P_pts]
                v1 = [u1[i] for i in P_pts]
                ev0 = self._interp_full(v0, P_pts, outs, wl, ells)
                ev1 = self._interp_full(v1, P_pts, outs, wl, ells)
                base_pts = [i for i in range(n) if ev0[i] == u0[i] and ev1[i] == u1[i]]
                base = len(base_pts)
                if base < k + 1:
                    consistency_ok = False  # T itself must be in the base set
                allg_base = max(allg_base, base)
                extras = {}
                for i in range(n):
                    if ev0[i] == u0[i] and ev1[i] == u1[i]:
                        continue
                    bb = (ev1[i] - u1[i]) % p
                    aa = (u0[i] - ev0[i]) % p
                    if bb:
                        extras.setdefault(aa * pow(bb, p - 2, p) % p, []).append(i)
                for gam, pts_ in extras.items():
                    agc = base + len(pts_)
                    key = tuple((ev0[i] + gam * ev1[i]) % p for i in range(n))
                    d = per_g.setdefault(gam, {})
                    if d.get(key, 0) < agc:
                        d[key] = agc
        return per_g, allg_base, n_deg_nogamma, n_deg_allg, consistency_ok

    def summarize(self, per_g, allg_base):
        """rows[a] = (badgamma_count_or_q, maxlist, union); crossover a*."""
        rows = {}
        for a in self.sweep:
            if a <= allg_base:
                bad = self.p  # the every-gamma layer makes ALL q gammas bad here
            else:
                bad = sum(1 for d in per_g.values() if any(c >= a for c in d.values()))
            mx = 0
            union = set()
            for d in per_g.values():
                cnt = 0
                for ev, c in d.items():
                    if c >= a:
                        cnt += 1
                        union.add(ev)
                mx = max(mx, cnt)
            rows[a] = (bad, mx, len(union))
        cross = None
        for a in self.sweep:
            if rows[a][0] == 0:
                cross = a
                break
        return rows, cross

    # ---------------- single-word depth ----------------
    def word_depth(self, wvals):
        """Exact max agreement of wvals with any deg<k codeword (>= k trivially)."""
        p, k = self.p, self.k
        best = k
        for T, lam, P_pts, outs, wl, ells in self.pre:
            S = 0
            for l_, i in zip(lam, T):
                S += l_ * wvals[i]
            if S % p == 0:
                ev = self._interp_full([wvals[i] for i in P_pts], P_pts, outs, wl, ells)
                agc = sum(1 for i in range(self.n) if ev[i] == wvals[i])
                best = max(best, agc)
        return best


def fmt_rows(pt, rows):
    parts = []
    for a in pt.sweep:
        bad, mx, un = rows[a]
        badtxt = "ALLq" if bad == pt.p else str(bad)
        parts.append(f"a={a}:{badtxt}/{mx}/{un}")
    return "  ".join(parts)


def make_bundle(pt, rng, kind):
    """Two-codeword bundle line (PromotedHypothesesB style): u0+g1*u1 = c1+e1,
    u0+g2*u1 = c2+e2, |supp(ei)| = n - a_wit. kinds: disjoint / shared / overlap."""
    p, n, k = pt.p, pt.n, pt.k
    wt = n - pt.a_wit
    coeffs1 = [rng.randrange(p) for _ in range(k)]
    coeffs2 = [rng.randrange(p) for _ in range(k)]

    def ev_poly(coeffs):
        out = []
        for x in pt.H:
            acc = 0
            for c in reversed(coeffs):
                acc = (acc * x + c) % p
            out.append(acc)
        return out

    c1, c2 = ev_poly(coeffs1), ev_poly(coeffs2)
    g1 = rng.randrange(1, p)
    g2 = rng.randrange(1, p)
    while g2 == g1:
        g2 = rng.randrange(1, p)
    idx = list(range(n))
    if kind == "disjoint":
        assert 2 * wt <= n
        E1 = rng.sample(idx, wt)
        E2 = rng.sample([i for i in idx if i not in E1], wt)
    elif kind == "shared":
        E1 = rng.sample(idx, wt)
        E2 = list(E1)
    elif kind == "overlap":  # |E1 ∩ E2| = wt - 1: deepest overlap keeping u0,u1 far
        E1 = rng.sample(idx, wt)
        keep = rng.sample(E1, wt - 1)
        fresh = rng.sample([i for i in idx if i not in E1], 1)
        E2 = keep + fresh
    else:
        raise ValueError(kind)
    e1 = {i: rng.randrange(1, p) for i in E1}
    e2 = {i: rng.randrange(1, p) for i in E2}
    invd = pt.inv((g1 - g2) % p)
    u1 = [((c1[i] - c2[i] + e1.get(i, 0) - e2.get(i, 0)) % p) * invd % p for i in range(n)]
    u0 = [(c1[i] + e1.get(i, 0) - g1 * u1[i]) % p for i in range(n)]
    return u0, u1, g1, g2


def run_point(pt):
    p, n = pt.p, pt.n
    print(f"\n{'=' * 78}\n== {pt.name}:  p = {p}, n = {n}, m = {pt.m}, r = {pt.r}, "
          f"s = {pt.s}, k = {pt.k}, rate = {pt.k}/{n}")
    print(f"   z = {pt.z}; agreement sweep a = {pt.sweep[0]}..{pt.sweep[-1]} "
          f"(census floor k+1 = {pt.a_lo}, witness a_wit = {pt.a_wit}, "
          f"Johnson ~ {math.sqrt(n * pt.k):.2f}, unique >= {pt.a_unique}); "
          f"eps* * q = 2^-128 * {p} ~ {p / 2**128:.3e} (< 1: crossover = count hits 0)")
    print("   row format  a: badgamma / maxlist / unionsize")
    rng = random.Random(232_000 + pt.n * 100 + pt.r)

    n_struct = len(pt.structured)
    print(f"   structured deep-line family: C({pt.s},{pt.r}) = {math.comb(pt.s, pt.r)} "
          f"subsets -> {n_struct} distinct bad scalars")

    # ---- the Theorem-Q deep line
    per_g, allg, dn, da, cons = pt.census(pt.u0, pt.u1)
    rows, cross = pt.summarize(per_g, allg)
    d0, d1 = pt.word_depth(pt.u0), pt.word_depth(pt.u1)
    check(f"{pt.name}: census consistency (extra point + degenerate base)", cons)
    print(f"   Q-LINE   depth(u0) = {d0}, depth(u1) = {d1}, degenerate subsets: "
          f"SB=0&SA!=0: {dn}, all-gamma: {da} (base <= {allg})")
    print(f"   Q-LINE   {fmt_rows(pt, rows)}")
    print(f"   Q-LINE   crossover a* = {cross}  (last bad agreement = "
          f"{cross - 1 if cross else f'>{pt.sweep[-1]}'}; "
          f"delta_lastbad = {(1 - (cross - 1) / n) if cross else float('nan'):.4f})")
    check(f"{pt.name}: all structured bad scalars recovered at a_wit",
          all(any(c >= pt.a_wit for c in per_g.get(lam, {}).values())
              for lam in pt.structured),
          f"{n_struct} scalars")
    q_rows = rows
    q_cross = cross

    # ---- O68 reproduction gates (P1 only)
    if pt.name == "P1":
        check("P1 reproduces O68 witness row (56 gammas, singletons, union 56)",
              rows[10] == (56, 1, 56), f"got {rows[10]}")
        check("P1 reproduces O68 sub-witness row (5496 gammas, max 2, union 10936)",
              rows[9] == (5496, 2, 10936), f"got {rows[9]}")
        check("P1 zero degenerate subsets on the deep line", dn == 0 and da == 0)

    # ---- bundle lines
    print(f"   BUNDLES (two-codeword, planted error weight {n - pt.a_wit} "
          f"=> planted agreement = a_wit = {pt.a_wit}):")
    bundle_crosses = {}
    for kind in ("disjoint", "shared", "overlap"):
        for t in range(N_BUNDLE_PER_KIND):
            u0, u1, g1, g2 = make_bundle(pt, rng, kind)
            per_b, allg_b, dn_b, da_b, cons_b = pt.census(u0, u1)
            rows_b, cross_b = pt.summarize(per_b, allg_b)
            if not cons_b:
                check(f"{pt.name}: bundle {kind}#{t} census consistency", False)
            planted_ok = allg_b >= pt.a_wit or all(
                any(c >= pt.a_wit for c in per_b.get(g, {}).values()) for g in (g1, g2))
            if not planted_ok:
                check(f"{pt.name}: bundle {kind}#{t} planted gammas found", False)
            d0b, d1b = pt.word_depth(u0), pt.word_depth(u1)
            extra = (rows_b[pt.a_wit][0] - 2) if rows_b[pt.a_wit][0] != p else "ALL"
            bundle_crosses.setdefault(kind, []).append(
                (cross_b, rows_b[pt.a_wit][0], d0b, d1b))
            print(f"     {kind:8s}#{t}  depth(u0,u1)=({d0b},{d1b})  deg(SB0,allg)="
                  f"({dn_b},{da_b})  {fmt_rows(pt, rows_b)}  a*={cross_b}  "
                  f"extra@a_wit={extra}")

    # ---- random-line control
    agg = {a: [] for a in pt.sweep}
    crosses = Counter()
    deep_count = 0
    allg_lines = 0
    for t in range(N_RAND):
        u0 = [rng.randrange(p) for _ in range(n)]
        u1 = [rng.randrange(p) for _ in range(n)]
        per_r, allg_r, dn_r, da_r, cons_r = pt.census(u0, u1)
        if not cons_r:
            check(f"{pt.name}: random line #{t} census consistency", False)
        rows_r, cross_r = pt.summarize(per_r, allg_r)
        for a in pt.sweep:
            agg[a].append(rows_r[a])
        crosses[cross_r] += 1
        if da_r:
            allg_lines += 1
    print(f"   RANDOM x {N_RAND}:  (per a: max badgamma | #lines with bad>0 | "
          f"max maxlist)   [{allg_lines} lines hit an all-gamma layer]")
    floor = {}
    for a in pt.sweep:
        bads = [b for b, _, _ in agg[a]]
        mxs = [m_ for _, m_, _ in agg[a]]
        nz = sum(1 for b in bads if b > 0)
        floor[a] = max(bads)
        print(f"      a={a}: max bad = {max(bads)}, lines>0 = {nz}/{N_RAND}, "
              f"max list = {max(mxs)}")
    print(f"   RANDOM crossover a* histogram: "
          f"{dict(sorted((k_ or -1, v) for k_, v in crosses.items()))}  (-1 = never)")

    # ---- the landscape verdict for this point
    print(f"   VERDICT {pt.name}: Q-line a* = {q_cross}; random a* mode = "
          f"{crosses.most_common(1)[0][0]}; random noise floor at a_wit = "
          f"{floor[pt.a_wit]}; Q-line excess over floor at a_wit = "
          f"{q_rows[pt.a_wit][0] - floor[pt.a_wit]}")
    return q_rows, q_cross, floor, crosses, bundle_crosses


POINTS = [
    ("P1", BABYBEAR, 16, 2, 5),
    ("P2", 97, 16, 2, 5),
    ("P3", BABYBEAR, 16, 4, 2),
    ("P4", 37, 12, 2, 4),
]


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--point", type=str, default="",
                    help="comma list of point names to run (default: all)")
    args = ap.parse_args()
    sel = set(args.point.split(",")) if args.point else None
    for name, p, n, m, r in POINTS:
        if sel and name not in sel:
            continue
        pt = Point(name, p, n, m, r)
        run_point(pt)
    print(f"\nfailures: {FAIL or 'none'}")
    sys.exit(1 if FAIL else 0)


if __name__ == "__main__":
    main()
