# RESONANCE-SCALING probe (#371 cycle 2): do the whole-field interior
# explosions (n=12, t=4, a=6/8 at q=37) persist at larger fields, or are they
# small-field saturation?  Sweep q with 12 | q-1 upward and count bad gamma.

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

n, k, t = 12, 2, 4
for q in (37, 61, 73, 97, 109, 157, 181, 193):
    if (q - 1) % n != 0:
        print(f"q={q}: 12 does not divide q-1, skip")
        continue
    g = gen_mu(q, n)
    dom = [pow(g, i, q) for i in range(n)]
    combos = list(combinations(dom, t))
    out = []
    for a in (4, 5, 6, 7, 8):
        row0 = {x: pow(x, a, q) for x in dom}
        row1 = {x: pow(x, a - 1, q) for x in dom}
        nbad = 0
        for gamma in range(q):
            for S in combos:
                xs = list(S)
                line = [(row0[x] + gamma * row1[x]) % q for x in xs]
                if interp_deg(xs, line, q) >= k:
                    continue
                if (interp_deg(xs, [row0[x] for x in xs], q) < k
                        and interp_deg(xs, [row1[x] for x in xs], q) < k):
                    continue
                nbad += 1
                break
        out.append(f"a={a}:bad={nbad}")
    print(f"q={q} n=12 k=2 t=4: " + " ".join(out), flush=True)
