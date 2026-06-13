#!/usr/bin/env python3
"""Twin classification CORRECTED (#371): the pair-alignment test was tautological.

On a multiplicative-subgroup domain every pair (x_i, x_j) is 'inversion-aligned'
with c := x_i*x_j (x -> c/x always preserves the subgroup), so the earlier 3/3
alignment record carried no information.  The refined conjecture: a twin pair
(i,j) forces sigma_c-TWIST EQUIVARIANCE OF THE STACK for c = x_i*x_j, in the
MCAMobiusInversion sense (T u)(x) = x^{k-1} * u(c/x)) -- the rows are projective
T_c-eigenvectors or T_c swaps the row span.

Test at (29,7,4,2): collect twins (large sample incl. structured modes); for each
twin (i,j) with c = x_i x_j, compute T_c u_b and test span-stability
{u0,u1} vs {T_c u0, T_c u1} (2-dim row span preserved?).  CONTROL: the same
test on non-twin pairs of the same stacks and on random twin-free stacks.
"""
import random, os
from collections import Counter
exec(open(os.path.join(os.path.dirname(os.path.abspath(__file__)),
     "probe_wb_window_pencil_crt.py")).read().split("total_mm = 0")[0]
     .replace('random.seed(20260611)', 'pass'))
exec(open(os.path.join(os.path.dirname(os.path.abspath(__file__)),
     "probe_wb_twin_classification.py")).read().split('def normalizer_aligned')[0]
     .split('exec(open')[0].split('"""')[-1] if False else "pass")
random.seed(424243)

q, n, k, w = 29, 7, 4, 2
def gen_mu(q, n):
    for cand in range(2, q):
        if pow(cand, n, q) == 1 and all(pow(cand, d, q) != 1 for d in range(1, n) if n % d == 0):
            return cand
    return None
inst = Inst(q, n, k, w, gen_mu(q, n))

def twin_pairs(l0, r0, l1, r1):
    M0, M1, dims = pencil_matrices(inst, l0, r0, l1, r1)
    ncol = sum(dims); nz = dims[0]
    agree = {}
    seen = 0
    for gam in range(q):
        M = [[(M0[i][j] + gam * M1[i][j]) % q for j in range(ncol)]
             for i in range(len(M0))]
        rk, ker = rank_and_kernel(M, q, want_kernel=True)
        if len(ker) != 2:
            continue
        seen += 1
        K1, K2 = ker
        z1 = [sum(K1[t] * pow(a, t, q) for t in range(nz)) % q for a in inst.dom]
        z2 = [sum(K2[t] * pow(a, t, q) for t in range(nz)) % q for a in inst.dom]
        for i in range(n):
            for j in range(i + 1, n):
                eq = (z1[i] * z2[j] - z1[j] * z2[i]) % q == 0
                agree[(i, j)] = agree.get((i, j), True) and eq
    return ([p for p, v in agree.items() if v] if seen else None)

def twist(u, c):
    """(T_c u)(x) = x^{k-1} * u(c/x) on the domain (in-tree reversalTwist form)."""
    out = []
    for x in inst.dom:
        sx = (c * pow(x, q - 2, q)) % q
        if sx not in inst.dom:
            return None
        out.append(pow(x, k - 1, q) * u[inst.dom.index(sx)] % q)
    return out

def span2(vs):
    """Row space (as echelon signature) of a list of vectors mod q."""
    M = [list(v) for v in vs]
    rk, _ = rank_and_kernel(M, q)
    return rk

def span_stable(u0, u1, c):
    t0, t1 = twist(u0, c), twist(u1, c)
    if t0 is None or t1 is None:
        return None
    base = span2([u0, u1])
    joint = span2([u0, u1, t0, t1])
    return base == joint   # twisted rows inside the original span

stats = Counter()
twin_records = []
for trial in range(15000):
    mode = random.randrange(4)
    l0 = [random.randrange(q) for _ in range(w + 1)]
    r0 = [random.randrange(q) for _ in range(w + k)]
    if not genuine_reduced(inst, l0, r0):
        continue
    if mode == 0:
        l1 = [random.randrange(q) for _ in range(w + 1)]
        r1 = [random.randrange(q) for _ in range(w + k)]
    else:
        l1, r1 = l0[:], [random.randrange(q) for _ in range(w + k)]
    if not genuine_reduced(inst, l1, r1):
        continue
    u0, u1 = inst.ratword(l0, r0), inst.ratword(l1, r1)
    if u0 is None or u1 is None:
        continue
    tp = twin_pairs(l0, r0, l1, r1)
    if tp is None:
        continue
    if not tp:
        stats["twinfree"] += 1
        # CONTROL on a random pair of a twin-free stack (sample sparsely)
        if stats["twinfree"] <= 40:
            i, j = random.sample(range(n), 2)
            c = (inst.dom[i] * inst.dom[j]) % q
            st = span_stable(list(u0), list(u1), c)
            stats[("control_stable", st)] += 1
        continue
    for (i, j) in tp:
        c = (inst.dom[i] * inst.dom[j]) % q
        st = span_stable(list(u0), list(u1), c)
        stats[("twin_stable", st)] += 1
        twin_records.append(((i, j), c, st))
        print(f"  twin {(i,j)} c={c} span-stable={st}", flush=True)
        # also non-twin pairs of the SAME stack as inner control
        for (i2, j2) in [(a, b) for a in range(n) for b in range(a+1, n)
                         if (a, b) not in tp][:3]:
            c2 = (inst.dom[i2] * inst.dom[j2]) % q
            st2 = span_stable(list(u0), list(u1), c2)
            stats[("sameStack_nontwin_stable", st2)] += 1

print(f"\nstats: {dict(sorted(stats.items(), key=str))}")
print(f"twins found: {len(twin_records)}")
