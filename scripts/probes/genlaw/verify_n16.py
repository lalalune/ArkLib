"""FORECAST VERIFIER, part 1: n=16 ground truth, fully independent.

(A) Regenerate the C19 list from scratch (brute force over C(16,9) interpolations,
    my own code -- not the census kernel): expect 19 = 3 witnesses (agree 10)
    + 16 dense (agree exactly 9).
(B) Extract (B,O,sign) data of the 16 dense elements.
(C) Independent char-0 enumeration of ALL balance solutions at s=8, pattern (3,3),
    by RAW exhaustive multiset balance in Z[zeta_16] (exact integers, NO structural
    lemmas, NO forced/free rule): O in C(8,3) x 4 sigma x B in C(complement,3).
(D) My own forced/free-axis engine at s=8; assert identical solution set to (C).
(E) Constructive correspondence: each char-0 (B,O,sigma) x 2 global signs ->
    explicit codeword mod p; assert exact set equality with the 16 dense elements.
"""
from itertools import combinations
from math import comb
import json

P = 15 * (1 << 27) + 1          # BabyBear
g0 = 31
n, s = 16, 8
h = pow(g0, (P - 1) // n, P)    # primitive 16th root
H = [pow(h, i, P) for i in range(n)]
G = [H[(2 * z) % n] for z in range(s)]          # mu_8, fiber values z_b
ZS = pow(g0, (P - 1) // 4, P)   # canonical 4th root z* (= H[4] = G[2])
assert ZS == H[4] and ZS == G[2]
LAM = (P - ZS) % P              # lam = -z*
w = [(pow(x, 10, P) + LAM * pow(x, 8, P)) % P for x in H]

# ---------------- (A) brute-force C19 regeneration (my own interpolation) ----------
def interp_coeffs(xs, ys):
    """Newton interpolation -> monomial coefficients mod P (deg <= len-1)."""
    m = len(xs)
    dd = list(ys)
    for j in range(1, m):
        for i in range(m - 1, j - 1, -1):
            dd[i] = (dd[i] - dd[i - 1]) * pow(xs[i] - xs[i - j], P - 2, P) % P
    # expand Newton form
    coeffs = [0] * m
    cur = [1]                                   # prod (X - xs[t]) so far
    for j in range(m):
        for t, c in enumerate(cur):
            coeffs[t] = (coeffs[t] + dd[j] * c) % P
        nxt = [0] * (len(cur) + 1)
        for t, c in enumerate(cur):
            nxt[t + 1] = (nxt[t + 1] + c) % P
            nxt[t] = (nxt[t] - c * xs[j]) % P
        cur = nxt
    return coeffs

codewords = {}                                  # eval-tuple -> coeffs
for T in combinations(range(n), 9):
    xs = [H[i] for i in T]
    ys = [w[i] for i in T]
    cf = interp_coeffs(xs, ys)
    if cf[8] % P != 0:
        continue                                # interpolant degree 8 -> not deg<8
    ev = tuple(sum(c * pow(x, j, P) for j, c in enumerate(cf[:8])) % P for x in H)
    codewords[ev] = cf[:8]

listing = []
for ev in codewords:
    agree = [i for i in range(n) if ev[i] == w[i]]
    assert len(agree) >= 9
    listing.append((len(agree), ev, tuple(agree)))
hist = {}
for a, _, _ in listing:
    hist[a] = hist.get(a, 0) + 1
print(f"[A] C19 regeneration: list size = {len(listing)}; agreement histogram = {hist}")
assert len(listing) == 19 and hist == {10: 3, 9: 16}, "C19 ground truth FAILED"
print("[A] C19 VERIFIED: 19 = 3 (agree 10) + 16 dense (agree exactly 9)")

# ---------------- (B) (B,O,sign) extraction of the 16 dense -----------------------
dense = sorted(ev for a, ev, _ in listing if a == 9)
dense_data = []
for ev in dense:
    T = [i for i in range(n) if ev[i] == w[i]]
    B, O, dvec = [], [], []
    for z in range(s):
        a, b = z in T, (z + s) in T
        if a and b:
            B.append(z)
        elif a:
            O.append(z); dvec.append(0)
        elif b:
            O.append(z); dvec.append(1)
    assert len(B) == 3 and len(O) == 3, f"pattern not (3,3): {len(B)},{len(O)}"
    dense_data.append((frozenset(B), tuple(O), tuple(dvec)))
print(f"[B] all 16 dense elements have pattern (|B|,|O|) = (3,3); extracted (B,O,d).")

# ---------------- (C) RAW char-0 exhaustive balance enumeration -------------------
# x_i = zeta^{o_i + 8 d_i}; multiset = {x1x2,x1x3,x2x3} u B_z u O_z u {-z*}
# exponents mod 16; -z* = -zeta^4 = zeta^12.  Balance: n[m]==n[m+8] for m in 0..7.
SIGS = [(0, 0, 0), (0, 1, 1), (1, 0, 1), (1, 1, 0)]
raw_sols = set()
for O in combinations(range(s), 3):
    for sig in SIGS:
        d = (0, sig[0], sig[1])
        a = [O[i] + s * d[i] for i in range(3)]
        base = [(a[0] + a[1]) % n, (a[0] + a[2]) % n, (a[1] + a[2]) % n,
                (2 * O[0]) % n, (2 * O[1]) % n, (2 * O[2]) % n, 12]
        rest = [z for z in range(s) if z not in O]
        for B in combinations(rest, 3):
            cnt = [0] * n
            for t in base:
                cnt[t] += 1
            for b in B:
                cnt[(2 * b) % n] += 1
            if all(cnt[m] == cnt[m + s] for m in range(s)):
                raw_sols.add((frozenset(B), O, sig))
print(f"[C] RAW char-0 enumeration at s=8, pattern (3,3): "
      f"{len(raw_sols)} (B,O,sigma) solutions -> x2 signs = {2 * len(raw_sols)} elements")

# ---------------- (D) my forced/free-axis engine, generic in s --------------------
def engine(s):
    n2 = 2 * s
    msz = s // 2 - 1                            # |B|
    out = set()
    classes = []
    for O in combinations(range(s), 3):
        Oset = set(O)
        for sig in SIGS:
            d = (0, sig[0], sig[1])
            a = [O[i] + s * d[i] for i in range(3)]
            terms = [(a[0] + a[1]) % n2, (a[0] + a[2]) % n2, (a[1] + a[2]) % n2,
                     (2 * O[0]) % n2, (2 * O[1]) % n2, (2 * O[2]) % n2,
                     (3 * s // 2) % n2]         # -z* = zeta^{3s/2}
            cnt = [0] * n2
            for t in terms:
                cnt[t] += 1
            ok = all(cnt[m] == cnt[m + s] for m in range(1, s, 2))
            forced, free = [], []
            if ok:
                for c in range(s // 2):
                    dd = cnt[2 * c] - cnt[2 * c + s]
                    if abs(dd) >= 2:
                        ok = False; break
                    if dd == -1:
                        f = c
                    elif dd == 1:
                        f = c + s // 2
                    else:
                        if c not in Oset and (c + s // 2) not in Oset:
                            free.append(c)
                        continue
                    if f in Oset:
                        ok = False; break
                    forced.append(f)
            if not ok:
                continue
            hh, v = len(forced), len(free)
            if (msz - hh) < 0 or (msz - hh) % 2:
                continue
            kk = (msz - hh) // 2
            if kk > v:
                continue
            classes.append(dict(O=O, sig=sig, h=hh, v=v, k=kk, ways=comb(v, kk),
                                forced=tuple(sorted(forced)), freeaxes=tuple(free)))
            for pick in combinations(free, kk):
                B = frozenset(forced) | {c for c in pick} | {c + s // 2 for c in pick}
                assert len(B) == msz and not (B & Oset)
                out.add((B, O, sig))
    return out, classes

eng_sols, eng_classes = engine(8)
print(f"[D] forced/free engine at s=8: {len(eng_sols)} solutions; "
      f"identical to RAW set: {eng_sols == raw_sols}")
assert eng_sols == raw_sols

# ---------------- (E) constructive correspondence with the 16 dense ---------------
def build_codeword(B, O, dvec, s):
    """codeword evals = w - e on H, plus degree check. Returns (ok, ev, agreeset)."""
    n2 = 2 * s
    X = [H[O[i] + s * dvec[i]] for i in range(3)]
    xi = (-sum(X)) % P
    roots = X + [xi]
    e = [1]
    for b in B:                                 # X^2 - z_b
        zb = G[b]
        ne = [0] * (len(e) + 2)
        for t, c in enumerate(e):
            ne[t + 2] = (ne[t + 2] + c) % P
            ne[t] = (ne[t] - c * zb) % P
        e = ne
    for r in roots:                             # X - r
        ne = [0] * (len(e) + 1)
        for t, c in enumerate(e):
            ne[t + 1] = (ne[t + 1] + c) % P
            ne[t] = (ne[t] - c * r) % P
        e = ne
    assert len(e) == 2 * len(B) + 5             # degree 2|B|+4
    ok = (e[-1] == 1 and e[2 * len(B) + 3] == 0 and e[2 * len(B) + 2] == LAM)
    ev = tuple((w[i] - sum(c * pow(H[i], j, P) for j, c in enumerate(e))) % P
               for i in range(n2))
    agree = tuple(i for i in range(n2) if ev[i] == w[i])
    return ok, ev, agree

constructed = set()
for B, O, sig in sorted(raw_sols, key=lambda t: (sorted(t[0]), t[1], t[2])):
    for flip in (0, 1):
        dvec = tuple((flip + dd) % 2 for dd in (0, sig[0], sig[1]))
        ok, ev, agree = build_codeword(B, O, dvec, 8)
        assert ok, "degree-<8 condition failed for a balance solution!"
        assert len(agree) == 9, f"agreement {len(agree)} != 9"
        constructed.add(ev)
print(f"[E] constructed {len(constructed)} distinct codewords from "
      f"{len(raw_sols)} classes x 2 signs")
print(f"[E] EXACT set equality with the 16 dense C19 elements: "
      f"{constructed == set(dense)}")
assert constructed == set(dense)

# strata summary for the report
strat = {}
for c in eng_classes:
    strat[(c['h'], c['v'], c['k'])] = strat.get((c['h'], c['v'], c['k']), 0) + 1
print(f"[S] n=16 (O,sigma)-class strata (h,v,k)->#classes: {strat}; "
      f"sum ways = {sum(c['ways'] for c in eng_classes)}")
json.dump({"dense_data": [[sorted(B), list(O), list(d)] for B, O, d in dense_data],
           "raw_sols": [[sorted(B), list(O), list(sg)] for B, O, sg in sorted(
               raw_sols, key=lambda t: (sorted(t[0]), t[1], t[2]))]},
          open("/tmp/genlaw/n16_groundtruth.json", "w"), indent=1)
print("N16 DONE: count = 16 = 2 x", len(raw_sols), " -- all checks PASSED")
