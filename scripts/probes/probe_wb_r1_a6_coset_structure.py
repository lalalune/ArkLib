# Structure probe (#371 cycle 2): the 37 = 3n+1 interior bad set at
# (n=12, k=2, t=4, a=6), q=73/97: decompose into mu_12-cosets (norm gamma^12
# invariant) and classify EVERY witness of each bad gamma (pure locus vs
# mixed-sign sets x^6 = +-1).

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

n, k, t, a = 12, 2, 4, 6
for q in (73, 97):
    g = gen_mu(q, n)
    dom = [pow(g, i, q) for i in range(n)]
    domset = set(dom)
    combos = list(combinations(dom, t))
    row0 = {x: pow(x, a, q) for x in dom}
    row1 = {x: pow(x, a - 1, q) for x in dom}
    bad = {}
    for gamma in range(q):
        wits = []
        for S in combos:
            xs = list(S)
            line = [(row0[x] + gamma * row1[x]) % q for x in xs]
            if interp_deg(xs, line, q) >= k:
                continue
            if (interp_deg(xs, [row0[x] for x in xs], q) < k
                    and interp_deg(xs, [row1[x] for x in xs], q) < k):
                continue
            wits.append(xs)
        if wits:
            bad[gamma] = wits
    # norm classes
    norms = {}
    for gamma in bad:
        norms.setdefault(pow(gamma, n, q) if gamma else 'zero', []).append(gamma)
    print(f"q={q}: bad={len(bad)} norm-classes="
          f"{[(nm, len(gs)) for nm, gs in norms.items()]}")
    # witness classification for one representative per norm class
    for nm, gs in norms.items():
        gamma = gs[0]
        cls = {}
        for xs in bad[gamma]:
            root = (q - gamma) % q
            Sp = [x for x in xs if x != root]
            rootin = len(Sp) < len(xs)
            mind = next((d for d in range(1, n)
                         if len({pow(x, d, q) for x in Sp}) == 1), None)
            if mind:
                key = ('root+' if rootin else 'noroot+') + f"locus(d={mind},|{len(Sp)}|)"
            else:
                # sign pattern under x^6 (in mu_2)
                sig = tuple(sorted(pow(x, 6, q) for x in Sp))
                key = ('root+' if rootin else 'noroot+') + f"mixed(sgn6={sig})"
            cls[key] = cls.get(key, 0) + 1
        print(f"  γ={gamma} (norm={nm}): wits={len(bad[gamma])} {cls}", flush=True)
