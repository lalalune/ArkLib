# R1 converse probe (#371 cycle 2): does EVERY interior bad gamma have
# locus-structured witnesses?
#
# For monomial stacks (x^a, x^{a-1}) on mu_n in F_q, at each interior slice
# t = |S| (k+1 <= t <= n), enumerate ALL bad (gamma, S) pairs by brute force
# (agreement: interp(line|_S) has deg < k; mutuality: NOT both rows interp
# to deg < k).  For each bad pair, classify the witness set:
#   S' := S minus the line root {-gamma} (if it is a domain point);
#   find minimal d >= 1 such that S' splits into equal d-power classes
#   matching the tower law (single class = pure locus; several = multi-coset
#   config; none up to n = EXOTIC -> R1 counterexample).
# q-stability: each n is run at two fields.

import sys
from itertools import combinations

def gen_mu(q, n):
    for cand in range(2, q):
        if pow(cand, n, q) == 1 and all(pow(cand, d, q) != 1
                                        for d in range(1, n) if n % d == 0):
            return cand
    return None

def interp_deg(xs, ys, q):
    """Degree of the unique interpolating polynomial through (xs, ys) mod q
    (Newton divided differences mod q); returns max index with nonzero coeff."""
    m = len(xs)
    coef = list(ys)
    for j in range(1, m):
        for i in range(m - 1, j - 1, -1):
            num = (coef[i] - coef[i - 1]) % q
            den = (xs[i] - xs[i - j]) % q
            coef[i] = num * pow(den, q - 2, q) % q
    deg = -1
    # Newton form: coef[j] is the leading coeff of the degree-j basis term;
    # the true degree is the largest j with coef[j] != 0
    for j in range(m - 1, -1, -1):
        if coef[j] % q != 0:
            deg = j
            break
    return deg

def classify(Spts, gamma, q, n):
    """Classify witness set structure. Returns (rootin, mind, sig)."""
    root = (q - gamma) % q
    Sp = [x for x in Spts if x != root]
    rootin = len(Sp) < len(Spts)
    if not Sp:
        return rootin, 0, "empty"
    for d in range(1, n + 1):
        powers = {}
        for x in Sp:
            powers.setdefault(pow(x, d, q), []).append(x)
        if max(len(v) for v in powers.values()) == len(Sp):
            return rootin, d, "pure"
    # multi-class: best partition signature at the d minimizing class count
    best = None
    for d in range(1, n + 1):
        powers = {}
        for x in Sp:
            powers.setdefault(pow(x, d, q), []).append(x)
        sig = tuple(sorted(len(v) for v in powers.values()))
        if best is None or len(sig) < len(best[1]):
            best = (d, sig)
    return rootin, best[0], f"multi{best[1]}"

INSTANCES = [
    (19, 9, 2), (37, 9, 2), (37, 9, 3),
    (13, 12, 2), (37, 12, 2),
    (31, 15, 2), (61, 15, 2),
    (17, 16, 2), (97, 16, 2), (97, 16, 3),
]

for q, n, k in INSTANCES:
    g = gen_mu(q, n)
    if g is None:
        print(f"q={q} n={n}: no mu_n, skip")
        continue
    dom = [pow(g, i, q) for i in range(n)]
    domset = set(dom)
    for a in range(k + 1, n - 1):
        row0 = {x: pow(x, a, q) for x in dom}
        row1 = {x: pow(x, a - 1, q) for x in dom}
        for t in range(k + 1, n - k + 1):
            badstruct = {}
            nbad = 0
            exotic = []
            for gamma in range(q):
                line = {x: (row0[x] + gamma * row1[x]) % q for x in dom}
                found = None
                for S in combinations(dom, t):
                    xs = list(S)
                    if interp_deg(xs, [line[x] for x in xs], q) >= k:
                        continue
                    j0 = interp_deg(xs, [row0[x] for x in xs], q) < k
                    j1 = interp_deg(xs, [row1[x] for x in xs], q) < k
                    if j0 and j1:
                        continue
                    found = S
                    rootin, mind, sig = classify(xs, gamma, q, n)
                    key = (rootin, mind, sig)
                    badstruct[key] = badstruct.get(key, 0) + 1
                    if sig.startswith("multi") or not rootin:
                        exotic.append((gamma, sorted(xs), mind, sig))
                if found is not None:
                    nbad += 1
            if nbad:
                print(f"q={q} n={n} k={k} a={a} t={t}: bad={nbad} "
                      f"structs={badstruct}"
                      + (f" EXOTIC={exotic[:4]}" if exotic else ""),
                      flush=True)
    print(f"q={q} n={n} k={k}: done", flush=True)
