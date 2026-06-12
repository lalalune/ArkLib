# BLIND-POINT PROBE: structure of the degenerate-pencil kernel family at the
# RESULTS: normalizer (37,12,7,2): corank=1 at ALL gamma, blind=0; coset
# (37,12,5,3): corank 1 at 36, corank 2 at 1, blind=0; generic: corank 0 at 36,
# 1 at 1 (branch-(i) unsolvability visible). Corank-1 proportionality forces
# Z_T | recZ(v(gamma)) directly; the incidence count needs only the named strata
# (Degenerate, CorankOne, NoBlind) — all probe-validated.
# known adversarial stacks. For each gamma: compute ker(recMatrix(gamma)) (the
# inverse-free system as explicit linear system); record corank, and the kernel
# Z-part's domain roots. Blind x := domain point with Z-kernel vanishing at x for
# ALL gamma (with corank >= 1). Checks the branch-(ii) count design.
import sys
sys.path.insert(0, 'scripts/probes')
from probe_pade_reconstruction import *

def kernel_family(q, n, k, w, dom, l0, l1, R0, R1):
    j = 3*w+k-1-n
    m01 = pmul(l0, l1, q)
    ZD = [1]
    for x in dom: ZD = pmul(ZD, [(-x) % q, 1], q)
    A = pmul(l1, R0, q); B = pmul(l0, R1, q)
    # columns: h-coeffs (j+1), Z-coeffs (w+1); rows: 2w coefficients of the mod
    rows_h = []
    for t in range(j+1):
        col = pmod(pmul(ZD, [0]*t+[1], q), m01, q)
        rows_h.append(col)
    blind_candidates = {x: True for x in dom}
    coranks = {}
    kerZs = {}
    for gam in range(q):
        F_ = [((A[i] if i < len(A) else 0) + gam*(B[i] if i < len(B) else 0)) % q
              for i in range(max(len(A), len(B)))]
        cols = []
        for t in range(j+1):
            cols.append(pmod(pmul(ZD, [0]*t+[1], q), m01, q))
        for s in range(w+1):
            cols.append([(-c) % q for c in pmod(pmul(F_, [0]*s+[1], q), m01, q)])
        # matrix: 2w rows x (j+w+2) cols
        M = [[cols[c][r] if r < len(cols[c]) else 0 for c in range(j+w+2)]
             for r in range(2*w)]
        # gaussian: find kernel basis
        Mm = [row[:] for row in M]
        m_, nc, r = 2*w, j+w+2, 0
        piv = []
        for c in range(nc):
            p = next((i for i in range(r, m_) if Mm[i][c] % q), None)
            if p is None: continue
            Mm[r], Mm[p] = Mm[p], Mm[r]
            inv = pow(Mm[r][c], q-2, q)
            Mm[r] = [(v*inv) % q for v in Mm[r]]
            for i in range(m_):
                if i != r and Mm[i][c] % q:
                    f = Mm[i][c]
                    Mm[i] = [(a-f*b) % q for a, b in zip(Mm[i], Mm[r])]
            piv.append(c); r += 1
        free = [c for c in range(nc) if c not in piv]
        corank = len(free)
        coranks[gam] = corank
        if corank >= 1:
            # one kernel vector per free col
            kers = []
            for fc in free:
                v = [0]*nc; v[fc] = 1
                for ri, pc in enumerate(piv): v[pc] = (-Mm[ri][fc]) % q
                kers.append(v)
            # Z-parts
            Zs = [v[j+1:] for v in kers]
            kerZs[gam] = Zs
            for x in list(blind_candidates):
                if not all(sum(Z[s]*pow(x, s, q) for s in range(w+1)) % q == 0
                           for Z in Zs):
                    blind_candidates[x] = False
        # blind only meaningful over gammas with corank>=1
    solv = [g for g in coranks if coranks[g] >= 1]
    blind = [x for x in blind_candidates if blind_candidates[x]] if solv else []
    print(f"  corank profile: {{c: count}} =",
          {c: sum(1 for g in coranks.values() if g == c) for c in set(coranks.values())})
    print(f"  #gamma with kernel: {len(solv)}  blind domain points: {len(blind)}")
    return solv, blind

# the normalizer-pair stack at (37,12,7,2) (rebuild as in the Pade probe)
q, n, k, w = 37, 12, 7, 2
g = find_gen(q, n); dom = [pow(g, i, q) for i in range(n)]
domset = set(dom)
xi = next(x for x in range(2, q) if x not in domset
          and pow(x, q-2, q) not in domset and pow(x, q-2, q) != x)
xi2 = pow(xi, q-2, q)
eta = next(x for x in range(2, q) if x not in domset and x not in (xi, xi2)
           and pow(x, q-2, q) not in domset
           and pow(x, q-2, q) not in (x, xi, xi2))
eta2 = pow(eta, q-2, q)
l0 = [xi*xi2 % q, (-(xi+xi2)) % q, 1]
l1 = [eta*eta2 % q, (-(eta+eta2)) % q, 1]
ZD = [1]
for x in dom: ZD = pmul(ZD, [(-x) % q, 1], q)
a0, b0 = dom[1], pow(dom[1], q-2, q) % q
ZT0 = pmul([(-a0) % q, 1], [(-b0) % q, 1], q)
m01 = pmul(l0, l1, q)
ZS0 = pmod(pmul(ZD, pinv(ZT0, m01, q), q), m01, q)
R0 = pmod(pmul(pinv(l1, l0, q), ZS0, q), l0, q)
R1 = pmod(pmul(pinv(l0, l1, q), ZS0, q), l1, q)
print("normalizer (37,12,7,2):")
kernel_family(q, n, k, w, dom, l0, l1, R0, R1)
# the j=1 coset stack
q2, n2, k2, w2 = 37, 12, 5, 3
g2 = find_gen(q2, n2); dom2 = [pow(g2, i, q2) for i in range(n2)]
munw = {pow(x, w2, q2) for x in dom2}
es = [e for e in range(2, q2) if e not in munw][:2]
l0b = [(-es[0]) % q2, 0, 0, 1]; l1b = [(-es[1]) % q2, 0, 0, 1]
print("coset (37,12,5,3):")
kernel_family(q2, n2, k2, w2, dom2, l0b, l1b, [1], [1])
# a RANDOM (generic, branch-i) stack for contrast
import random
random.seed(1)
print("generic (37,12,5,3):")
R0r = [random.randrange(q2) for _ in range(w2+k2)]
R1r = [random.randrange(q2) for _ in range(w2+k2)]
l0r = [random.randrange(q2) for _ in range(w2)]+[1]
l1r = [random.randrange(q2) for _ in range(w2)]+[1]
kernel_family(q2, n2, k2, w2, dom2, l0r, l1r, R0r, R1r)
