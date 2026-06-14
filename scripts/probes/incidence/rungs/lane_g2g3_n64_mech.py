#!/usr/bin/env python3
"""MECHANISM AUDIT for the lane_g2g3_n64.py G2 violations.

For every recorded violation (witness w, marginal t, extra zero at H[i]) compute
    delta = e_t(zeta^i) - e_w(zeta^i)  in  Z[zeta_64] = Z[X]/(X^32 + 1)
by EXACT integer lattice arithmetic (no mod p in the construction):
    e_t(zeta^i) = prod_{b in B} (zeta^{2i} - zeta^{2b})
                  * prod_j (zeta^i - x_j) * (zeta^i - xi),
                  x_j = zeta^{O_j + 32 d_j}, xi = -(x1+x2+x3)
    e_w(zeta^i) = (zeta^{2i} - zeta^{16}) * prod_{z in I} (zeta^{4i} - zeta^{4z})
(d = c_w - c_t = e_t - e_w, so a collision at H[i] <=> delta(zeta -> h) = 0 mod p.)

CLASSIFIES each violation:
  CHAR0-IDENTITY: delta == 0 exactly in Z[zeta_64] -- the collision is an exact
      cyclotomic identity (char-0 exactness itself fails at n=64; cf. the n=32
      dense-dense q-root identities, which were also char-0 exact);
  BADNORM: delta != 0 in Z[zeta_64] but delta(h) == 0 mod BabyBear -- a
      transfer failure (p | Norm(delta)), the O134 bad-alpha mechanism.
Cross-checks: (a) self-test of the lattice arithmetic against mod-p evaluation
on random elements; (b) every violation re-evaluated mod p2 = 3*2^30+1
(independent prime, g0 = 5 per falsifier RESULTS.md): a CHAR0-IDENTITY must
collide at p2 too, a BADNORM generically must not; (c) extra zero outside
T_w u T_t; (d) float check |delta(e^{2 pi i/64})| for nonzero deltas.
"""
import cmath, json, random
from collections import Counter

P = 15 * (1 << 27) + 1
g0 = 31
n, s = 64, 32
h = pow(g0, (P - 1) // n, P)
H = [pow(h, i, P) for i in range(n)]
P2 = 3 * (1 << 30) + 1
g02 = 5
assert pow(g02, (P2 - 1) // 2, P2) != 1   # primitive check (order divisibility)
h2 = pow(g02, (P2 - 1) // n, P2)
H2 = [pow(h2, i, P2) for i in range(n)]
assert len(set(H2)) == 64 and pow(h2, 32, P2) == P2 - 1

# ---- exact Z[zeta_64] arithmetic: vectors of 32 ints, zeta^32 = -1 ----------
def zmul(a, b):
    r = [0] * 32
    for i, ai in enumerate(a):
        if ai:
            for j, bj in enumerate(b):
                if bj:
                    k = i + j
                    if k >= 32:
                        r[k - 32] -= ai * bj
                    else:
                        r[k] += ai * bj
    return r

def zunit(e):
    e %= 64
    v = [0] * 32
    if e >= 32:
        v[e - 32] = -1
    else:
        v[e] = 1
    return v

def zsub(a, b): return [x - y for x, y in zip(a, b)]
def zneg(a): return [-x for x in a]
def zeval(a, x, q):
    return sum(a[j] * pow(x, j, q) for j in range(32)) % q

# self-test: lattice mul is a ring hom under zeta -> h (mod P) and zeta -> h2
random.seed(1)
for _ in range(200):
    a = [random.randrange(-5, 6) for _ in range(32)]
    b = [random.randrange(-5, 6) for _ in range(32)]
    c = zmul(a, b)
    assert zeval(c, h, P) == zeval(a, h, P) * zeval(b, h, P) % P
    assert zeval(c, h2, P2) == zeval(a, h2, P2) * zeval(b, h2, P2) % P2
print("lattice arithmetic self-test: 200/200 random products agree with mod-p "
      "and mod-p2 evaluation")

def delta_of(v):
    i = v['extra'][0]
    dvec = tuple((v['flip'] + d) % 2 for d in (0, v['sg'][0], v['sg'][1]))
    et = zunit(0)
    for b in v['B']:
        et = zmul(et, zsub(zunit(2 * i), zunit(2 * b)))
    xs = [zunit(v['O'][j] + 32 * dvec[j]) for j in range(3)]
    xi = zneg([xs[0][j] + xs[1][j] + xs[2][j] for j in range(32)])
    for xv in xs:
        et = zmul(et, zsub(zunit(i), xv))
    et = zmul(et, zsub(zunit(i), xi))
    ew = zsub(zunit(2 * i), zunit(16))
    for z in v['wit_I']:
        ew = zmul(ew, zsub(zunit(4 * i), zunit(4 * z)))
    return zsub(et, ew), i

viol = json.load(open(
    "/home/nubs/Git/ArkLib/scripts/probes/incidence/rungs/lane_g2g3_n64_violations.json"))
print(f"auditing {len(viol)} recorded G2 violations\n")
zC = cmath.exp(2j * cmath.pi / 64)
classes = Counter()
units = [k for k in range(64) if k % 2 == 1]
for v in viol:
    delta, i = delta_of(v)
    assert len(v['extra']) == 1
    assert not v['extra_in_Tw'][0] and not v['extra_in_Tt'][0]
    # the violation must reproduce mod P through the lattice (consistency)
    assert zeval(delta, h, P) == 0, "violation not reproduced through lattice!"
    # p2 cross-check
    at_p2 = (zeval(delta, h2, P2) == 0)
    if not any(delta):
        cls = "CHAR0-IDENTITY"
        assert at_p2, "char-0 identity must collide at p2!"
        extra = ""
    else:
        cls = "BADNORM"
        l1 = sum(map(abs, delta))
        fl = abs(sum(delta[j] * zC**j for j in range(32)))
        assert fl > 1e-6, "float says zero but lattice nonzero?!"
        dead = sum(1 for k in units if zeval(delta, pow(h, k, P), P) == 0)
        extra = (f" L1={l1} |delta|_C={fl:.3g} embeddings-killed={dead}/32"
                 f" collides-at-p2={at_p2}")
    classes[cls] += 1
    print(f"  {cls}: wit#{v['wit']} x [{v['tag']}] O={tuple(v['O'])} "
          f"extra=H[{i}] p2-collision={at_p2}{extra}")
print(f"\nclassification: {dict(classes)}")
print("CHAR0-IDENTITY => the n=64 cross-channel has EXACT char-0 collisions "
      "(prime-independent); BADNORM => mod-p-only transfer failure")
