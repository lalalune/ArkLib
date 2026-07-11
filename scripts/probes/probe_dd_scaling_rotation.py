#!/usr/bin/env python3
"""Probe: scaling/rotation equivariance of the divided difference of x^b, and the
induced rotation law on the Schur-ratio level set gamma_{R'} = -h_{a-k}(R')/h_{b-k}(R').

dividedDifferencePow s v b = sum_{i in s} v(i)^b / prod_{j in s\i} (v i - v j).

CLAIM 1 (homogeneity): dd(s, c*v, b) = c^{b-(|s|-1)} * dd(s, v, b).
  numerator scales c^b, each of the (|s|-1) denom factors scales c => c^{b-(|s|-1)}.

CLAIM 2 (rotation law on mu_n): with |R'|=k+1 and h_d(R') = dd(R', d+k),
  gamma(zeta*R') = zeta^{a-b} * gamma(R').  (matches lalalune's R'->zeta R' => gamma->zeta^{a-b}gamma)

NEVER validate at n=q-1: this is a pure char-0/complex algebraic identity over mu_n roots
of unity (no prime, no full-group). It is the equivariance substrate, not a CORE bound.
"""
import cmath, random

def dd(vals, b):
    s = len(vals)
    tot = 0j
    for i in range(s):
        num = vals[i] ** b
        den = 1 + 0j
        for j in range(s):
            if j != i:
                den *= (vals[i] - vals[j])
        tot += num / den
    return tot

random.seed(1)
print("=== CLAIM 1: dd(s, c*v, b) == c^{b-(|s|-1)} dd(s,v,b) (complex random) ===")
ok = True
checked = 0
for trial in range(4000):
    s = random.randint(2, 5)
    vals = [complex(random.uniform(-3, 3), random.uniform(-3, 3)) for _ in range(s)]
    if len({(round(x.real, 6), round(x.imag, 6)) for x in vals}) < s:
        continue
    b = random.randint(0, 8)
    c = complex(random.uniform(-2, 2), random.uniform(-2, 2))
    if abs(c) < 1e-3:
        continue
    lhs = dd([c * x for x in vals], b)
    rhs = (c ** (b - (s - 1))) * dd(vals, b)
    checked += 1
    if abs(lhs - rhs) > 1e-6 * (1 + abs(rhs)):
        ok = False
        print("FAIL", s, b, c, lhs, rhs)
        break
print("homogeneity:", "ALL MATCH" if ok else "FAILED", f"({checked} checked)")

def hsym(vals, d, k):
    return dd(vals, d + k)

print()
print("=== CLAIM 2: gamma(zeta R') = zeta^{a-b} gamma(R') on mu_n ===")
ok = True
checked = 0
for n in [8, 16, 32]:
    roots = [cmath.exp(2j * cmath.pi * t / n) for t in range(n)]
    zeta = cmath.exp(2j * cmath.pi / n)
    for trial in range(600):
        k = random.randint(1, 3)
        sub = random.sample(range(n), k + 1)
        R = [roots[t] for t in sub]
        a = random.randint(k + 1, k + 6)
        bb = random.randint(k + 1, k + 6)
        if a == bb:
            continue
        ha = hsym(R, a - k, k)
        hb = hsym(R, bb - k, k)
        if abs(hb) < 1e-9:
            continue
        gamma = -ha / hb
        Rz = [zeta * x for x in R]
        haz = hsym(Rz, a - k, k)
        hbz = hsym(Rz, bb - k, k)
        if abs(hbz) < 1e-9:
            continue
        gammaz = -haz / hbz
        pred = (zeta ** (a - bb)) * gamma
        checked += 1
        if abs(gammaz - pred) > 1e-5 * (1 + abs(pred)):
            ok = False
            print("FAIL", n, k, a, bb, gamma, gammaz, pred)
            break
    if not ok:
        break
print("rotation gamma law:", "ALL MATCH" if ok else "FAILED", f"({checked} checked)")
