"""AUDITOR n=16 ground truth, written from scratch.
(1) Full C(16,9) census of agree>=9 deg<8 codewords for w = X^10 + lam X^8
    via LAGRANGE interpolation (different algorithm than verifier's Newton).
(2) My own s=8 balance enumeration (raw, no lemmas) -> classes.
(3) Construct 2x elements per class mod p; assert exact set equality with (1)'s
    dense list. Also: agreement histogram must be {10:3, 9:16}.
"""
from itertools import combinations

P = 15 * (1 << 27) + 1
g0 = 31
n, s = 16, 8
zeta = pow(g0, (P - 1) // n, P)
H = [pow(zeta, i, P) for i in range(n)]
ZS = H[4]
assert pow(ZS, 2, P) == P - 1
LAM = (P - ZS) % P
w = [(pow(x, 10, P) + LAM * pow(x, 8, P)) % P for x in H]

def polymul(a, b):
    r = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        if x:
            for j, y in enumerate(b):
                r[i + j] = (r[i + j] + x * y) % P
    return r

def synth_div(poly, root):
    """divide poly by (X - root); poly must be divisible-ish (we use full prod)."""
    out = [0] * (len(poly) - 1)
    acc = 0
    for c in reversed(poly):
        out_idx = len(out)
        acc = c + acc * root
        # standard synthetic division: process from top
    # do it explicitly instead:
    out = [0] * (len(poly) - 1)
    out[-1] = poly[-1]
    for i in range(len(poly) - 3, -1, -1):
        out[i] = (poly[i + 1] + root * out[i + 1]) % P
    return out

# (1) census via Lagrange
dense, witnesses = set(), set()
count = 0
for T in combinations(range(n), 9):
    xs = [H[i] for i in T]
    full = [1]
    for x in xs:
        full = polymul(full, [(-x) % P, 1])
    coeffs = [0] * 9
    for i, xi_ in enumerate(xs):
        num = synth_div(full, xi_)             # prod_{j!=i}(X - x_j), deg 8
        den = 1
        for j, xj in enumerate(xs):
            if j != i:
                den = den * (xi_ - xj) % P
        sc = w[T[i]] * pow(den, P - 2, P) % P
        for t in range(9):
            coeffs[t] = (coeffs[t] + sc * num[t]) % P
    if coeffs[8] != 0:
        continue
    ev = tuple(sum(coeffs[t] * pow(x, t, P) for t in range(8)) % P for x in H)
    agr = sum(1 for i in range(n) if ev[i] == w[i])
    assert agr >= 9
    (witnesses if agr == 10 else dense).add(ev)
    count += 1
print(f"[1] census: witnesses(agree 10) = {len(witnesses)}, dense(agree 9) = {len(dense)}, "
      f"list = {len(witnesses) + len(dense)}")
assert len(witnesses) == 3 and len(dense) == 16

# (2) my raw s=8 balance enumeration (no lemmas, no axis rule)
sols = []
for O in combinations(range(s), 3):
    rest = [z for z in range(s) if z not in O]
    for m in range(4):
        d = (0, m & 1, (m >> 1) & 1)
        a = [O[i] + s * d[i] for i in range(3)]
        base = [(a[0] + a[1]) % n, (a[0] + a[2]) % n, (a[1] + a[2]) % n,
                (2 * O[0]) % n, (2 * O[1]) % n, (2 * O[2]) % n, (3 * s // 2) % n]
        for B in combinations(rest, 3):
            cnt = [0] * n
            for t in base:
                cnt[t] += 1
            for b in B:
                cnt[(2 * b) % n] += 1
            if all(cnt[t] == cnt[t + s] for t in range(s)):
                sols.append((B, O, d))
print(f"[2] raw s=8 balance solutions: {len(sols)} classes -> {2 * len(sols)} elements")
assert len(sols) == 8

# (3) constructive correspondence
made = set()
for B, O, d in sols:
    for flip in (0, 1):
        dv = [(x + flip) % 2 for x in d]
        roots = []
        for b in B:
            roots += [H[b], H[(b + s) % n]]
        X = [H[(O[i] + s * dv[i]) % n] for i in range(3)]
        xi = (-sum(X)) % P
        assert xi != 0 and xi not in H, "L4 violated"
        roots += X + [xi]
        e = [1]
        for rt in roots:
            e = polymul(e, [(-rt) % P, 1])
        assert len(e) == 11 and e[10] == 1 and e[9] == 0 and e[8] == LAM, "consistency fail"
        ev = tuple((w[i] - sum(e[t] * pow(H[i], t, P) for t in range(11))) % P
                   for i in range(n))
        agr = sum(1 for i in range(n) if ev[i] == w[i])
        assert agr == 9, f"agreement {agr}"
        made.add(ev)
print(f"[3] constructed {len(made)} distinct elements; set-equal to census dense: "
      f"{made == dense}")
assert made == dense
print("AUDIT N16: ALL PASS (19 = 3 + 16; engine classes = 8; exact element match)")
