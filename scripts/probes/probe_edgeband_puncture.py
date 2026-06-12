#!/usr/bin/env python3
"""Probe: the UDR-edge band n in [2w+k+1, 2w+2k) — falsify-first for the
puncture-descent law  #bad * (n-2w-k) <= n^(k+1)  on the FULL below-UDR range.

Background (#371, DISPROOF_LOG fifth no-go): the universal below-UDR law covers
2w+2k <= n; the band n in [2w+k+1, 2w+2k) defeats both engine branches.  The
proposed descent: every explainer of a sparse direction agrees with u0 at some
off-support witness point x0; dividing the instance by (X - x0) maps
(n, k, w) -> (n-1, k-1, w) at the SAME gamma, and sigma = n-2w-k is invariant.
Induction on k bottoms at the in-tree k=1 universal law.

This probe checks, at band instances:
  P1  max #bad over adversarial stacks  <=  n^(k+1) / sigma   (the claimed law)
  P2  branch lemma: for sparse directions, every bad gamma has an explainer
      agreement point OFF the support (automatic: line = u0 there)
  P3  the puncture descent is bad-preserving: gamma bad in parent =>
      gamma bad in the punctured child (n-1, k-1) at the same w
Faithful mcaEvent semantics: gamma is bad iff SOME codeword P has
|agree(P, line)| >= n-w and the pair (u0,u1) is NOT jointly explainable on
that agreement set (exists-S form collapses to full agreement sets since
"not joint" is upward monotone and any S sits inside a full agreement set).
Exit 0 iff all checks pass.
"""

import itertools, random, sys

random.seed(371)

def inv(a, p): return pow(a, p - 2, p)

def interp_eval(pts, xs_eval, p):
    """Lagrange-interpolate through pts=[(x,y),...] and evaluate at xs_eval."""
    out = []
    for xe in xs_eval:
        tot = 0
        for i, (xi, yi) in enumerate(pts):
            num, den = 1, 1
            for j, (xj, _) in enumerate(pts):
                if i == j: continue
                num = num * ((xe - xj) % p) % p
                den = den * ((xi - xj) % p) % p
            tot = (tot + yi * num * inv(den, p)) % p
        out.append(tot)
    return out

def fits_deg_lt_k(vals, dom, idxs, k, p):
    """Do the values on positions idxs fit a single poly of degree < k?"""
    idxs = list(idxs)
    if len(idxs) <= k: return True
    base = idxs[:k]
    pts = [(dom[i], vals[i]) for i in base]
    rest = idxs[k:]
    pred = interp_eval(pts, [dom[i] for i in rest], p)
    return all(pred[t] == vals[rest[t]] for t in range(len(rest)))

def bad_set(u0, u1, dom, n, k, w, p, want_witness=False):
    """Faithful mcaEvent bad set at integer radius w (threshold |S| >= n-w)."""
    bads, wits = set(), {}
    thr = n - w
    all_k_subsets = list(itertools.combinations(range(n), k))
    for g in range(p):
        line = [(u0[i] + g * u1[i]) % p for i in range(n)]
        # every explainer with agreement >= n-w >= k is the interpolant of one
        # of its k-subsets; enumerate interpolants of k-subsets of positions
        seen = set()
        found = False
        for T in all_k_subsets:
            pts = [(dom[i], line[i]) for i in T]
            key = tuple(interp_eval(pts, [dom[i] for i in range(n)], p))
            if key in seen: continue
            seen.add(key)
            A = [i for i in range(n) if key[i] == line[i]]
            if len(A) < thr: continue
            joint = fits_deg_lt_k(u0, dom, A, k, p) and fits_deg_lt_k(u1, dom, A, k, p)
            if not joint:
                bads.add(g); wits[g] = (A, key); found = True
                break
        if found: continue
    return (bads, wits) if want_witness else bads

def puncture(u0, u1, dom, x0_idx, p):
    """Divide instance by (X - x0): child on n-1 points, dim k-1, same gamma."""
    x0 = dom[x0_idx]; a = u0[x0_idx]
    nd, n0, n1 = [], [], []
    for i, x in enumerate(dom):
        if i == x0_idx: continue
        d = inv((x - x0) % p, p)
        nd.append(x)
        n0.append(((u0[i] - a) * d) % p)
        n1.append((u1[i] * d) % p)
    return n0, n1, nd

def run_instance(p, n, k, w, rounds_random, rounds_struct, label):
    sigma = n - 2 * w - k
    assert sigma >= 1 and n - 2 * w - 2 * k < 1, f"{label}: not in band/below-UDR edge"
    dom = list(range(1, n + 1))
    budget = n ** (k + 1) // sigma
    maxbad, argmax = 0, None
    stacks = []
    # random stacks
    for _ in range(rounds_random):
        stacks.append(([random.randrange(p) for _ in range(n)],
                       [random.randrange(p) for _ in range(n)]))
    # band-critical structured: sparse directions e in (w, w+k], incl. chopped
    # codewords eps = poly*1_E with adversarial u0 (chopped poly too)
    for _ in range(rounds_struct):
        e = random.randint(w + 1, min(w + k, n - w - 1))
        E = random.sample(range(n), e)
        u1 = [0] * n
        if random.random() < 0.5:
            for i in E: u1[i] = random.randrange(1, p)
        else:  # chopped codeword
            coeffs = [random.randrange(p) for _ in range(k)]
            for i in E:
                u1[i] = sum(c * pow(dom[i], j, p) for j, c in enumerate(coeffs)) % p
                if u1[i] == 0: u1[i] = 1
        if random.random() < 0.5:
            u0 = [random.randrange(p) for _ in range(n)]
        else:  # u0 also chopped-structured
            coeffs0 = [random.randrange(p) for _ in range(k)]
            u0 = [sum(c * pow(dom[i], j, p) for j, c in enumerate(coeffs0)) % p
                  for i in range(n)]
            for i in random.sample(range(n), w):
                u0[i] = random.randrange(p)
        stacks.append((u0, u1))
    p2_viol = p3_viol = p3_checked = 0
    for u0, u1 in stacks:
        bads, wits = bad_set(u0, u1, dom, n, k, w, p, want_witness=True)
        if len(bads) > maxbad: maxbad, argmax = len(bads), (u0[:], u1[:])
        # P2/P3 on sparse directions only (post-translation shape)
        supp = [i for i in range(n) if u1[i] != 0]
        if len(supp) <= n - w - 1 and k >= 2:
            O = [i for i in range(n) if u1[i] == 0]
            for g in bads:
                A, _ = wits[g]
                offs = [i for i in A if i in O]
                if not offs: p2_viol += 1; continue
                # P3: child badness at one off-support witness point
                ok = False
                for x0 in offs[:3]:
                    c0, c1, cd = puncture(u0, u1, dom, x0, p)
                    if g in bad_set(c0, c1, cd, n - 1, k - 1, w, p):
                        ok = True; break
                p3_checked += 1
                if not ok: p3_viol += 1
    ok = maxbad <= budget and p2_viol == 0 and p3_viol == 0
    print(f"{label}: n={n} k={k} w={w} sigma={sigma} budget={budget} "
          f"maxbad={maxbad} P2viol={p2_viol} P3={p3_checked - p3_viol}/{p3_checked} "
          f"{'OK' if ok else 'FAIL'}")
    if not ok and argmax: print("   extremal:", argmax)
    return ok

def main():
    allok = True
    # k=2 band: n = 2w+3 exactly (m=1)
    allok &= run_instance(17, 7, 2, 2, 250, 250, "B1 k2 m1")
    allok &= run_instance(13, 9, 2, 3, 150, 250, "B2 k2 m1")
    # k=3 band: n in [2w+4, 2w+6): m=1 and m=2
    allok &= run_instance(17, 8, 3, 2, 120, 220, "B3 k3 m1")
    allok &= run_instance(17, 9, 3, 2, 120, 220, "B4 k3 m2")
    # control just outside the band (universal law range, recursion still applies)
    allok &= run_instance(17, 10, 3, 2, 80, 120, "C1 k3 m3")
    print("ALL OK" if allok else "FAILURES PRESENT")
    sys.exit(0 if allok else 1)

main()
