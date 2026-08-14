#!/usr/bin/env python3
"""
The rung sum bound as a GATED incidence count (p=12289, mu_16).

Reframing: a frame class is a quadratic q (deg<3) with agreement set
A_q = {i : R1(x_i) = q(x_i)} (points of R1's graph on the curve y=q(x)),
gated by ">= 2 bad scalars attach". cap = 16 - |A_q|.

This probe, for the record-22 stack's actual R1 and for random deg-<=15 R1:
 (1) enumerate quadratics through >= 3 of the 16 graph points (the
     incidence structure), report the distribution of agreement sizes a_q;
 (2) the UNGATED sum Sum_{a_q>=2}(16 - a_q) (should be huge - shows gating
     is essential);
 (3) confirm the two record big-classes are two such quadratics with a=6.
Establishes the residual = a gated incidence bound, and quantifies how much
the >=2-attached gate must cut (from ungated ~hundreds down to <= 30).
"""
import itertools
from collections import Counter

p, n = 12289, 16
g0 = next(g for g in range(2, 500)
          if all(pow(g, (p - 1) // f, p) != 1 for f in (2, 3)))
w = pow(g0, (p - 1) // n, p)
D = [pow(w, j, p) for j in range(n)]

def quad_through(i, j, k, vals):
    """deg<=2 poly through (D[i],vals[i]),(D[j],vals[j]),(D[k],vals[k]);
    return coeff tuple or None if x's collide."""
    xs = [D[i], D[j], D[k]]
    if len(set(xs)) < 3:
        return None
    ys = [vals[i], vals[j], vals[k]]
    # Lagrange -> deg<=2 coeffs
    c = [0, 0, 0]
    for a in range(3):
        num = [1]  # prod (x - xs[b]), b!=a
        den = 1
        for b in range(3):
            if b == a:
                continue
            num = [(- xs[b] * (num[t] if t < len(num) else 0)
                    + (num[t-1] if t-1 >= 0 else 0)) % p
                   for t in range(len(num) + 1)]
            den = den * ((xs[a] - xs[b]) % p) % p
        f = ys[a] * pow(den, p-2, p) % p
        for t in range(3):
            c[t] = (c[t] + f * (num[t] if t < len(num) else 0)) % p
    return tuple(c)

def agreement_size(coeff, vals):
    cnt = 0
    for i in range(n):
        q = (coeff[0] + coeff[1]*D[i] + coeff[2]*D[i]*D[i]) % p
        if q == vals[i]:
            cnt += 1
    return cnt

def analyze(vals, label):
    quads = {}
    for (i, j, k) in itertools.combinations(range(n), 3):
        c = quad_through(i, j, k, vals)
        if c is None:
            continue
        quads.setdefault(c, agreement_size(c, vals))
    sizes = Counter(quads.values())
    ungated = sum(16 - a for a in quads.values() if a >= 2)
    big = sorted([a for a in quads.values()], reverse=True)[:6]
    print(f"[{label}] #distinct quadratics thru>=3 pts: {len(quads)}; "
          f"agreement-size dist {sorted(sizes.items(), reverse=True)}; "
          f"top sizes {big}; UNGATED sum(16-a, a>=2) = {ungated}")

# record-22 stack R1: built from blockladder2 trial 0
import importlib.util
src = open("scripts/probes/probe_wb371_blockladder2.py").read()
ns = {}
exec(src[:src.index("best_per_ns")], ns)
peval = ns['peval']; solve_linear = ns['solve_linear']; pencil_row = ns['pencil_row']
import random
rng = random.Random(7000 + 2)
gams = rng.sample(range(2, p), 2)
b1 = rng.sample(range(0,6), 4); b2 = rng.sample(range(6,12), 4)
rows = []
for jj, gg in enumerate(gams):
    for i in b1[2*jj:2*jj+2]: rows.append(pencil_row(0,6,D[i],gg))
    for i in b2[2*jj:2*jj+2]: rows.append(pencil_row(3,9,D[i],gg))
sol = solve_linear(rows, 18, rng)
q1c, q2c = sol[0:3], sol[3:6]
# R1 = the deg-9 direction row of the record stack (reconstruct its values)
# u1 on domain: blocks q1,q2; pts 12-14 q3; pt15 steered
q3c = sol[12:15]
u1 = [0]*n
for i in range(6): u1[i] = peval(q1c, D[i])
for i in range(6,12): u1[i] = peval(q2c, D[i])
for i in (12,13,14): u1[i] = peval(q3c, D[i])
# pt 15 steered value (recompute as in blockladder2)
r1c, r2c = sol[6:9], sol[9:12]
ga, gb = rng.randrange(1,p), rng.randrange(1,p)
x = D[15]
rhs1 = (peval(r1c,x)+ga*peval(q1c,x))%p; rhs2 = (peval(r2c,x)+gb*peval(q2c,x))%p
u1[15] = (rhs1-rhs2)*pow((ga-gb)%p,p-2,p)%p
analyze(u1, "record-22 R1")
# the two big classes should be q1c, q2c with a=6
print(f"  q1 agreement size: {agreement_size(tuple(q1c), u1)}, "
      f"q2 agreement size: {agreement_size(tuple(q2c), u1)}")

for seed in (1, 2):
    rng2 = random.Random(seed)
    vals = [rng2.randrange(p) for _ in range(n)]
    analyze(vals, f"random R1 #{seed}")
