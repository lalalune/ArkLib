#!/usr/bin/env python3
"""#389 probe: (A) the affine-plane sharpness witness at the t^2 = s*n pole,
(B) the graded moment identity Sum_c C(a_c, j) = N_j(w) (degenerate j-subsets),
(C) the capped triple statistic T_3 = N_{k+1} at k=2 (exhaustive at q=7,
structured + random at larger q) -- the word-coupled quantity that, through
Kruskal-Katona, controls the sub-Johnson supply.

Exit 0 iff (A) exact at all tested q, (B) exact identity at all tested (k,q,w,j).
(C) is measurement (prints the max capped T_3 / E landscape vs the generic value).
"""
import itertools, random, sys
from math import comb

random.seed(389)
FAIL = 0


def check(name, ok):
    global FAIL
    print(("PASS " if ok else "FAIL ") + name)
    if not ok:
        FAIL += 1


# ---------- (A) affine-plane witness ----------
print("=" * 70)
print("(A) AFFINE-PLANE SHARPNESS: family of q^2 line-graphs in [q^2]")
for q in [3, 5, 7, 11, 13]:
    n = q * q
    fam = []
    for a in range(q):
        for b in range(q):
            fam.append(frozenset((x, (a * x + b) % q) for x in range(q)))
    fam = list(set(fam))
    sizes = [len(A) for A in fam]
    mass = sum(sizes)
    t = q
    s_max = 0
    ok_pair = True
    for i in range(len(fam)):
        for j in range(i + 1, len(fam)):
            c = len(fam[i] & fam[j])
            s_max = max(s_max, c)
            if c > 1:
                ok_pair = False
    check(f"q={q}: L=q^2 ({len(fam)})", len(fam) == q * q)
    check(f"q={q}: all sizes = t = q", all(sz == q for sz in sizes))
    check(f"q={q}: pairwise <= 1 (max {s_max})", ok_pair)
    check(f"q={q}: mass = q^3 = t*n ({mass})", mass == q ** 3)
    check(f"q={q}: AT the pole t^2 = s*n ({t * t} = {n})", t * t == n)
    check(f"q={q}: violates 2n law (mass {mass} > 2n {2 * n})", mass > 2 * n or q <= 2)

# ---------- helpers for (B)/(C) ----------
def line_agreements(w, dom, q):
    """a_c for ALL q^2 lines c=(a,b) (k=2, deg<=1 codewords)."""
    out = []
    for a in range(q):
        for b in range(q):
            out.append(sum(1 for x in dom if w[x] == (a * x + b) % q))
    return out


def interp_deg_le(pts, q, kdeg):
    """Is interpolating poly of pts (distinct x, over F_q prime) of degree <= kdeg?
    Equivalent: all (kdeg+2)-subsets ... simpler: build Newton differences."""
    # Lagrange: compute poly coeffs
    m = len(pts)
    poly = [0] * m
    for i, (xi, yi) in enumerate(pts):
        num = [1]
        den = 1
        for jj, (xj, _) in enumerate(pts):
            if jj == i:
                continue
            # num *= (X - xj)
            new = [0] * (len(num) + 1)
            for d, c in enumerate(num):
                new[d] = (new[d] - c * xj) % q
                new[d + 1] = (new[d + 1] + c) % q
            num = new
            den = den * (xi - xj) % q
        cmul = yi * pow(den, q - 2, q) % q
        for d, c in enumerate(num):
            poly[d] = (poly[d] + cmul * c) % q
    deg = -1
    for d in range(m - 1, -1, -1):
        if poly[d] % q:
            deg = d
            break
    return deg <= kdeg


print("=" * 70)
print("(B) MOMENT IDENTITY  Sum_c C(a_c,j) = N_j(w) := #{j-subsets S: deg interp(w|S) < k}")
for q, k in [(11, 2), (13, 2), (11, 3)]:
    dom = list(range(q))
    n = len(dom)
    for trial in range(3):
        w = [random.randrange(q) for _ in range(q)]
        # all codewords of degree < k
        agreements = []
        for coeffs in itertools.product(range(q), repeat=k):
            a_c = sum(1 for x in dom
                      if w[x] == sum(coeffs[d] * pow(x, d, q) for d in range(k)) % q)
            agreements.append(a_c)
        for j in range(k, k + 3):
            lhs = sum(comb(a, j) for a in agreements)
            rhs = sum(1 for S in itertools.combinations(dom, j)
                      if interp_deg_le([(x, w[x]) for x in S], q, k - 1))
            check(f"q={q} k={k} trial={trial} j={j}: {lhs} = {rhs}", lhs == rhs)
        # j = k sanity: N_k = C(n,k) always
        lhs_k = sum(comb(a, k) for a in agreements)
        check(f"q={q} k={k} trial={trial}: N_k = C(n,k) ({lhs_k} = {comb(n, k)})",
              lhs_k == comb(n, k))

# ---------- (C) the capped triple statistic, EXHAUSTIVE at q=7 ----------
print("=" * 70)
print("(C1) EXHAUSTIVE q=7, k=2, dom=F_7: max T_3 and max E=N_4 over ALL words, per cap")
try:
    import numpy as np

    q = 7
    n = q
    V = np.zeros((q * q, q), dtype=np.int8)
    for a in range(q):
        for b in range(q):
            for x in range(q):
                V[a * q + b, x] = (a * x + b) % q
    comb3 = np.array([comb(a, 3) for a in range(q + 1)])
    comb4 = np.array([comb(a, 4) for a in range(q + 1)])
    best_T3 = {}
    best_E = {}
    # enumerate all 7^7 words in chunks
    words = np.array(list(itertools.product(range(q), repeat=q)), dtype=np.int8)
    B = 20000
    for lo in range(0, len(words), B):
        W = words[lo:lo + B]
        agr = (W[:, None, :] == V[None, :, :]).sum(axis=2)  # (B, 49)
        amax = agr.max(axis=1)
        T3 = comb3[agr].sum(axis=1)
        E4 = comb4[agr].sum(axis=1)
        for cap in range(3, q + 1):
            mask = amax <= cap
            if mask.any():
                t3m = int(T3[mask].max())
                e4m = int(E4[mask].max())
                if t3m > best_T3.get(cap, -1):
                    best_T3[cap] = t3m
                if e4m > best_E.get(cap, -1):
                    best_E[cap] = e4m
    generic_T3 = comb(n, 3) / q
    print(f"  n=q=7: C(n,3)={comb(n,3)}, generic T3 ~ C(n,3)/q = {generic_T3:.1f}")
    for cap in sorted(best_T3):
        x3 = best_T3[cap]
        print(f"  cap={cap}: max T3 = {x3}  (T3/n = {x3 / n:.2f}, "
              f"T3/(n^3/q) = {x3 / (n ** 3 / q):.2f})   max E=N_4 = {best_E[cap]}")
except ImportError:
    print("  numpy missing; skipped")

# ---------- (C2) structured + random words at larger q, incl. sub-Johnson n<q ----------
print("=" * 70)
print("(C2) larger fields: T_3 for random / character / coset words (dom = F_q^*or F_q)")
for q in [31, 61, 101]:
    dom = list(range(q))
    n = len(dom)
    rows = []
    # random words
    rmax = 0
    for _ in range(5):
        w = [random.randrange(q) for _ in range(q)]
        agr = line_agreements(w, dom, q)
        rmax = max(rmax, sum(comb(a, 3) for a in agr))
    rows.append(("random(5)", rmax))
    # quadratic character word w(x) = x^((q-1)/2) (on full domain; w(0)=0)
    w = [pow(x, (q - 1) // 2, q) if x else 0 for x in range(q)]
    agr = line_agreements(w, dom, q)
    rows.append((f"chi (maxagr={max(agr)})", sum(comb(a, 3) for a in agr)))
    # cubic-power word
    w = [pow(x, (q - 1) // 3 if (q - 1) % 3 == 0 else 3, q) for x in range(q)]
    agr = line_agreements(w, dom, q)
    rows.append((f"x^((q-1)/3) (maxagr={max(agr)})", sum(comb(a, 3) for a in agr)))
    # inverse word w(x) = x^{-1}
    w = [pow(x, q - 2, q) if x else 0 for x in range(q)]
    agr = line_agreements(w, dom, q)
    rows.append((f"x^(-1) (maxagr={max(agr)})", sum(comb(a, 3) for a in agr)))
    gen = comb(n, 3) / q
    print(f"  q={q} n={n}: generic T3 ~ {gen:.0f}")
    for name, t3 in rows:
        print(f"    {name:28s} T3 = {t3}  ratio-to-generic {t3 / gen:.2f}")

print("=" * 70)
print("FAILURES:", FAIL)
sys.exit(0 if FAIL == 0 else 1)
