import random, os
from collections import Counter
exec(open("scripts/probes/probe_wb_window_pencil_crt.py").read().split("total_mm = 0")[0]
     .replace('random.seed(20260611)', 'pass'))
random.seed(13579)
q, n, k, w = 29, 7, 4, 2
def gen_mu(q, n):
    for cand in range(2, q):
        if pow(cand, n, q) == 1 and all(pow(cand, d, q) != 1 for d in range(1, n) if n % d == 0):
            return cand
inst = Inst(q, n, k, w, gen_mu(q, n))

def g_poly(l0, r0, l1, r1, i, j):
    """Interpolate g_ij(gamma) from kernel evaluations (deg <= 2w+2 = 6 < q)."""
    M0, M1, dims = pencil_matrices(inst, l0, r0, l1, r1)
    ncol = sum(dims); nz = dims[0]
    vals = {}
    for gam in range(q):
        M = [[(M0[i2][j2] + gam * M1[i2][j2]) % q for j2 in range(ncol)]
             for i2 in range(len(M0))]
        rk, ker = rank_and_kernel(M, q, want_kernel=True)
        if len(ker) != 2:
            vals[gam] = None  # rank-drop point: kernel basis not canonical
            continue
        K1, K2 = ker
        z1 = [sum(K1[t] * pow(a, t, q) for t in range(nz)) % q for a in (inst.dom[i], inst.dom[j])]
        z2 = [sum(K2[t] * pow(a, t, q) for t in range(nz)) % q for a in (inst.dom[i], inst.dom[j])]
        vals[gam] = (z1[0] * z2[1] - z1[1] * z2[0]) % q
    return vals  # note: kernel-basis-dependent SCALE per gamma — only the ZERO SET is canonical!

# The zero set of g_ij is basis-independent; compare ZERO SETS across stacks
zsets = Counter()
samples = 0
PAIR = (0, 5)
while samples < 60:
    l0 = [random.randrange(q) for _ in range(w + 1)]
    r0 = [random.randrange(q) for _ in range(w + k)]
    l1 = [random.randrange(q) for _ in range(w + 1)]
    r1 = [random.randrange(q) for _ in range(w + k)]
    if not (genuine_reduced(inst, l0, r0) and genuine_reduced(inst, l1, r1)):
        continue
    if inst.ratword(l0, r0) is None or inst.ratword(l1, r1) is None:
        continue
    vals = g_poly(l0, r0, l1, r1, *PAIR)
    if any(v is None for v in vals.values()):
        zs = tuple(sorted(g for g, v in vals.items() if v == 0 or v is None))
        tag = "withdrop"
    else:
        zs = tuple(sorted(g for g, v in vals.items() if v == 0))
        tag = "clean"
    samples += 1
    zsets[(tag, len(zs))] += 1
print("zero-set SIZE distribution for pair", PAIR, ":", dict(sorted(zsets.items(), key=str)))
# if phi were data-independent, all stacks would share THE SAME zero set:
# count distinct zero sets among clean samples
random.seed(2468)
distinct = Counter()
samples = 0
while samples < 40:
    l0 = [random.randrange(q) for _ in range(w + 1)]
    r0 = [random.randrange(q) for _ in range(w + k)]
    l1 = [random.randrange(q) for _ in range(w + 1)]
    r1 = [random.randrange(q) for _ in range(w + k)]
    if not (genuine_reduced(inst, l0, r0) and genuine_reduced(inst, l1, r1)):
        continue
    if inst.ratword(l0, r0) is None or inst.ratword(l1, r1) is None:
        continue
    vals = g_poly(l0, r0, l1, r1, *PAIR)
    if any(v is None for v in vals.values()):
        continue
    zs = tuple(sorted(g for g, v in vals.items() if v == 0))
    distinct[zs] += 1
    samples += 1
print(f"distinct zero sets across {samples} clean stacks: {len(distinct)}")
for zs, cnt in list(distinct.items())[:6]:
    print("  ", zs, "x", cnt)
