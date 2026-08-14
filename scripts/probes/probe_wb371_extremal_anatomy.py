#!/usr/bin/env python3
"""
Anatomy of the deep-window extremal at (11,10,1,4), bad = {0,1,4,10}:
  u0 = (0,5,0,0,5,6,0,0,6,0)   spike on sigma-orbits (2,5)->5, (6,9)->6
  u1 = (4,0,4,5,0,10,4,5,10,4)
Predictions to verify per bad gamma:
  (1) every witness S contains the pole set Z0 = {2,5,6,9} minus <= D_def exceptions;
  (2) gamma solves the spike-matching equations u0(z)+g*u1(z) = p (p = line value);
  (3) sigma-alignment: matching equations coincide on sigma-orbits.
Also: what is u1?  (rational rep, sigma-invariance check), and the witness/level-set
structure of each bad gamma.
"""
q, n, k, w = 11, 10, 1, 4
D = list(range(1, 11))
need = n - w
u0 = (0,5,0,0,5,6,0,0,6,0)
u1 = (4,0,4,5,0,10,4,5,10,4)
inv = {x: pow(x, q-2, q) for x in range(1, q)}
sigma = {x: (q - inv[x]) % q for x in D}
idx = {x: i for i, x in enumerate(D)}

print("u0 by domain point:", {D[i]: u0[i] for i in range(n)})
print("u1 by domain point:", {D[i]: u1[i] for i in range(n)})
print("sigma-invariant? u0:", all(u0[idx[x]] == u0[idx[sigma[x]]] for x in D),
      " u1:", all(u1[idx[x]] == u1[idx[sigma[x]]] for x in D))

Z0 = [D[i] for i in range(n) if u0[i] != 0]
print("u0 spike support Z0 =", Z0)

for g in range(q):
    line = [(u0[i] + g*u1[i]) % q for i in range(n)]
    levels = {}
    for i, v in enumerate(line):
        levels.setdefault(v, []).append(D[i])
    wit = [(v, P) for v, P in levels.items() if len(P) >= need]
    if not wit:
        continue
    bad = False
    info = []
    for v, P in wit:
        c0 = len({u0[idx[x]] for x in P}) == 1
        c1 = len({u1[idx[x]] for x in P}) == 1
        if not (c0 and c1):
            bad = True
        info.append((v, P, "joint" if (c0 and c1) else "WITNESS"))
    if bad:
        print(f"\ngamma={g} BAD; level sets >= {need}:")
        for v, P, tag in info:
            inZ = [x for x in P if x in Z0]
            print(f"   value {v}: P={P} [{tag}]  P∩Z0={inZ}")
            # spike-matching residuals at poles in P
            for z in inZ:
                lhs = (u0[idx[z]] + g*u1[idx[z]]) % q
                print(f"      pole z={z}: u0+g*u1 = {lhs} (= line value {v}? {lhs==v})")

# u1 rational rep: find (l, R) deg l <= 4 nonvanishing, deg R <= 4 with l*u1 = R on D
import itertools
def poleval(p, x):
    return sum(c * pow(x, i, q) for i, c in enumerate(p)) % q
found = []
for lc in itertools.product(range(q), repeat=4):
    l = list(lc) + [1]
    vals = [poleval(l, x) for x in D]
    pts = [(x, (vals[i]*u1[i]) % q) for i, x in enumerate(D)]
    # interpolate R deg <= 4 through 10 pts? solve linear system
    A = [[pow(x, j, q) for j in range(5)] for x, _ in pts]
    b = [y for _, y in pts]
    # gaussian solve / consistency
    M = [row[:] + [b[i]] for i, row in enumerate(A)]
    r = 0
    for col in range(5):
        piv = None
        for row in range(r, n):
            if M[row][col] % q: piv = row; break
        if piv is None: continue
        M[r], M[piv] = M[piv], M[r]
        ip = pow(M[r][col], q-2, q)
        M[r] = [(v*ip)%q for v in M[r]]
        for row in range(n):
            if row != r and M[row][col] % q:
                f = M[row][col]
                M[row] = [(M[row][j]-f*M[r][j])%q for j in range(6)]
        r += 1
    ok = all(all(M[row][j]%q==0 for j in range(5)) == (M[row][5]%q==0) or
             any(M[row][j]%q for j in range(5)) for row in range(n))
    consistent = True
    for row in range(n):
        if all(M[row][j]%q==0 for j in range(5)) and M[row][5]%q:
            consistent = False; break
    if consistent:
        # has l roots in D?
        roots = [x for x in D if poleval(l, x) == 0]
        found.append((l, roots))
        if len(found) <= 4:
            print(f"\nu1 rep: l={l} roots-in-D={roots}")
print(f"\ntotal u1 reps found: {len(found)}; reps with NO roots in D: "
      f"{sum(1 for _, r in found if not r)}")
