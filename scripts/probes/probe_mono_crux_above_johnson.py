#!/usr/bin/env python3
"""
probe_mono_crux_above_johnson.py  (issue #389)

THE CRUX points only (above Johnson), with a faster maxagree:
  - n=12 q=61  k=6  w=4  (d=0.333 > J=0.293)   [user's requested larger-n point, ABOVE Johnson]
  - n=8  q=1009 k=4 w=3  (d=0.375 > J=0.293, q/n=126)  [deepest tractable q>>n at n=8]

Question: is worst-monomial < average-pencil above Johnson, at larger n and deeper q?
"""
import itertools, random

def inv(a, q):
    return pow(a, q - 2, q)

def rou(q, n):
    for g in range(2, q):
        x = 1; s = set()
        for _ in range(q - 1):
            x = x * g % q; s.add(x)
        if len(s) == q - 1:
            o = pow(g, (q - 1) // n, q)
            return [pow(o, i, q) for i in range(n)]
    return None

def make_maxagree(mu, q, k, n):
    subs = list(itertools.combinations(range(n), k))
    # precompute, per subset, the Lagrange "value-at-domain-point" weights:
    #   interp value at domain index t = sum_{j in sub} vals[sub_j] * W[sub][t][j]
    # so agreement test f[t]==vals[t] is exact field arithmetic, no per-call inversion.
    W = []
    for sub in subs:
        xs = [mu[i] for i in sub]
        rowt = []
        for t in range(n):
            xt = mu[t]
            wj = []
            for j in range(k):
                num = 1; den = 1
                for l in range(k):
                    if l != j:
                        num = num * (xt - xs[l]) % q
                        den = den * (xs[j] - xs[l]) % q
                wj.append(num * inv(den, q) % q)
            rowt.append(wj)
        W.append((sub, rowt))
    def maxagree(vals):
        best = 0
        for sub, rowt in W:
            c = 0
            for t in range(n):
                acc = 0
                wj = rowt[t]
                for jj, sj in enumerate(sub):
                    acc += wj[jj] * vals[sj]
                if acc % q == vals[t]:
                    c += 1
            if c > best:
                best = c
                if best == n:
                    return n
        return best
    return maxagree

def run(q, n, k, w, nsamp=50, seed=7):
    mu = rou(q, n)
    a = n - w
    J = 1 - (k / n) ** 0.5
    d = w / n
    ma = make_maxagree(mu, q, k, n)
    monwords = [[pow(mu[i], e, q) for i in range(n)] for e in range(n)]

    def nbad(u0, u1):
        c = 0
        for g in range(q):
            v = [(u0[i] + g * u1[i]) % q for i in range(n)]
            if ma(v) >= a:
                c += 1
        return c

    def isfar(u1):
        return ma(u1) < a

    mono_vals = []; Imono = 0; marg = None
    for b in range(n):
        for c in range(n):
            if b == c:
                continue
            u1 = monwords[c]
            if not isfar(u1):
                continue
            nb = nbad(monwords[b], u1)
            mono_vals.append(nb)
            if nb > Imono:
                Imono, marg = nb, (b, c)
    mono_avg = (sum(mono_vals) / len(mono_vals)) if mono_vals else float('nan')

    rng = random.Random(seed)
    samp_vals = []; Isamp = 0; tried = 0; attempts = 0
    while tried < nsamp and attempts < nsamp * 80:
        attempts += 1
        u0 = [rng.randrange(q) for _ in range(n)]
        u1 = [rng.randrange(q) for _ in range(n)]
        if not isfar(u1):
            continue
        tried += 1
        nb = nbad(u0, u1)
        samp_vals.append(nb)
        if nb > Isamp:
            Isamp = nb
    samp_avg = (sum(samp_vals) / len(samp_vals)) if samp_vals else float('nan')
    beats = sum(1 for v in samp_vals if v > Imono)
    tagJ = 'ABOVE-J' if d > J else ('below-J' if d < J else 'AT-J')
    print(f"n={n} q={q} k={k} (rho={k/n:.3f} q/n={q/n:.0f}) w={w} d={d:.3f} {tagJ} J={J:.3f} a={a}", flush=True)
    print(f"   MONO:    worst={Imono} (x^{marg[0]},x^{marg[1]})  avg={mono_avg:.2f}  #far_mono={len(mono_vals)}", flush=True)
    if samp_vals and Imono:
        srt = sorted(samp_vals)
        print(f"   NONMONO: worst(sampled {tried})={Isamp}  AVG={samp_avg:.2f}  min={srt[0]}  median={srt[len(srt)//2]}", flush=True)
        vA = "UNDERESTIMATES" if Isamp > Imono else "worst-mono>=worst-sampled"
        vB = "BELOW-AVG" if Imono < samp_avg else "NOT-below-avg"
        print(f"   --> (A) worst-over-mono: {vA}  (worst_nonmono/worst_mono={Isamp/Imono:.3f})", flush=True)
        print(f"   --> (B) mono-vs-avg: {vB}  (avg_nonmono/worst_mono={samp_avg/Imono:.3f}, #beating={beats}/{tried})", flush=True)
    print(flush=True)

if __name__ == "__main__":
    print("=== CRUX: above-Johnson monomial extremality at larger n / deeper q ===\n", flush=True)
    run(61, 12, 6, 4, nsamp=50)     # n=12 ABOVE Johnson  (the requested larger-n crux)
    run(1009, 8, 4, 3, nsamp=40)    # n=8 deepest q>>n (q/n=126)
    print("done", flush=True)
