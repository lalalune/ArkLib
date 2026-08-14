# RED-TEAM probe (#371 cycle 2): is the a=6/n=12 interior slice (t=4) a genuine
# InteriorSpectrumSilent falsifier, or a small-field artifact?
# At q=13 the domain mu_12 = F_13^* saturates the field; rerun at q=37, 61
# (12 | q-1) and count bad gamma at t=4,5 with per-gamma witness samples.

from itertools import combinations

def gen_mu(q, n):
    for cand in range(2, q):
        if pow(cand, n, q) == 1 and all(pow(cand, d, q) != 1
                                        for d in range(1, n) if n % d == 0):
            return cand
    return None

def interp_deg(xs, ys, q):
    m = len(xs)
    coef = list(ys)
    for j in range(1, m):
        for i in range(m - 1, j - 1, -1):
            num = (coef[i] - coef[i - 1]) % q
            den = (xs[i] - xs[i - j]) % q
            coef[i] = num * pow(den, q - 2, q) % q
    for j in range(m - 1, -1, -1):
        if coef[j] % q != 0:
            return j
    return -1

for q in (13, 37, 61):
    n, k = 12, 2
    g = gen_mu(q, n)
    dom = [pow(g, i, q) for i in range(n)]
    for a in (4, 5, 6, 7, 8):
        row0 = {x: pow(x, a, q) for x in dom}
        row1 = {x: pow(x, a - 1, q) for x in dom}
        for t in (4, 5):
            badg = []
            samples = {}
            for gamma in range(q):
                for S in combinations(dom, t):
                    xs = list(S)
                    line = [(row0[x] + gamma * row1[x]) % q for x in xs]
                    if interp_deg(xs, line, q) >= k:
                        continue
                    j0 = interp_deg(xs, [row0[x] for x in xs], q) < k
                    j1 = interp_deg(xs, [row1[x] for x in xs], q) < k
                    if j0 and j1:
                        continue
                    badg.append(gamma)
                    samples[gamma] = xs
                    break
            print(f"q={q} a={a} t={t}: bad={len(badg)} "
                  f"badg={badg[:8]}{'...' if len(badg) > 8 else ''} "
                  f"sample_w={dict(list(samples.items())[:2])}", flush=True)
