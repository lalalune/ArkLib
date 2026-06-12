import random, os
from collections import Counter
exec(open("scripts/probes/probe_wb_window_pencil_crt.py").read().split("total_mm = 0")[0]
     .replace('random.seed(20260611)', 'pass'))
exec(open("scripts/probes/probe_wb_jacobi_factorization.py").read()
     .split("trials = 0")[0].split('inst = Inst')[1].split('\n', 1)[1])
random.seed(1)
q, n, k, w = 29, 7, 4, 2
def gen_mu(q, n):
    for cand in range(2, q):
        if pow(cand, n, q) == 1 and all(pow(cand, d, q) != 1 for d in range(1, n) if n % d == 0):
            return cand
inst = Inst(q, n, k, w, gen_mu(q, n))

def wb_rep(u):
    ncolwb = (w + 1) + (w + k)
    M = []
    for i2, x in enumerate(inst.dom):
        row = [pow(x, t, q) * u[i2] % q for t in range(w + 1)]
        row += [(-pow(x, s, q)) % q for s in range(w + k)]
        M.append(row)
    _, ker = rank_and_kernel(M, q, want_kernel=True)
    return next(((pnorm(list(v[:w+1])), pnorm(list(v[w+1:]))) for v in ker
                 if pnorm(list(v[:w+1]))), None)

for a in (5, 6):
    u0 = [pow(x, a, q) for x in inst.dom]
    u1 = [pow(x, a - 1, q) for x in inst.dom]
    s0, s1 = wb_rep(u0), wb_rep(u1)
    if not s0 or not s1: continue
    l0, r0 = s0; l1, r1 = s1
    m = 3 * w + k - 1 - n
    N = (w+1) + (w+k) + (m + 1 if m >= 0 else 0)
    rows = 3 * w + k
    if N - 2 > rows: break
    J = [0, 0] + list(range(N - 2))
    c0, c0p, cs, csp = 0, 1, 0, 1
    B2, N_, nz = build_B2(l0, r0, l1, r1, J, c0, c0p, cs, csp)
    detB2 = pol_det(B2)
    B = bad_set(inst, u0, u1)
    rhos = {}
    for i in range(n):
        for j in range(i + 1, n):
            def Gpoly(col, idx):
                acc = []
                for t in range(nz):
                    e = adj_entry(B2, t, col)
                    acc = pol_add(acc, psmul(pow(inst.dom[idx], t, q), e, q))
                return acc
            Gi1, Gi2 = Gpoly(c0, i), Gpoly(c0p, i)
            Gj1, Gj2 = Gpoly(c0, j), Gpoly(c0p, j)
            gij = pol_add(pol_mul(Gi1, Gj2), pol_neg(pol_mul(Gj1, Gi2)))
            if not gij or not detB2:
                rhos[(i, j)] = 'twin'; continue
            quo, rem = pol_divmod(gij, detB2)
            if rem or len(quo) - 1 != 1:
                rhos[(i, j)] = f'odd(deg{len(quo)-1 if not rem else "?"})'; continue
            rho = (-quo[0] * pow(quo[1], q - 2, q)) % q
            rhos[(i, j)] = rho
    print(f"a={a}: bad={sorted(B)}")
    print(f"  rho set = {sorted(set(v for v in rhos.values() if isinstance(v, int)))}")
    # closed-form fits: rho_ij vs symmetric functions of x_i, x_j
    fits = Counter()
    for (i, j), rho in rhos.items():
        if not isinstance(rho, int): continue
        xi, xj = inst.dom[i], inst.dom[j]
        e1, e2 = (xi + xj) % q, (xi * xj) % q
        for name, val in [("-e1", (-e1) % q), ("e1", e1), ("-e2", (-e2) % q),
                          ("e2", e2), ("e2/e1", e2 * pow(e1, q-2, q) % q if e1 else None),
                          ("-e1*e2", (-e1*e2) % q), ("e1^2/e2", e1*e1*pow(e2,q-2,q) % q)]:
            if val is not None and rho == val:
                fits[name] += 1
    print(f"  closed-form fit counts (21 pairs): {dict(fits)}")
    print(f"  rho==bad match: {set(v for v in rhos.values() if isinstance(v,int)) == set(B)}")
