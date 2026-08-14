#!/usr/bin/env python3
"""
probe_mono_n12_deepq.py  (issue #389)

RESOLVE the n=8 vs n=12 DISCREPANCY found in probe_mono_crux_above_johnson.py:
  - n=8  (q/n=32..126): worst-mono BELOW avg pencil above Johnson  (monomials sub-optimal)
  - n=12 q=61 (q/n=5):   worst-mono ABOVE avg pencil above Johnson  (monomials extremal!)

Is the n=12 result because q/n=5 is too shallow (NOT q>>n) or because n=12 samples too few
non-monomial pencils?  Re-test n=12 ABOVE Johnson at DEEPER q with MORE samples.

n=12 needs q=12m+1: 61(q/n=5), 73(6), 97(8), 109(9), 157(13), 193(16).
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
    W = []
    for sub in subs:
        xs = [mu[i] for i in sub]
        rowt = []
        for t in range(n):
            xt = mu[t]; wj = []
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
                acc = 0; wj = rowt[t]
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

def run(q, n, k, w, nsamp, seed=11):
    mu = rou(q, n)
    a = n - w; J = 1 - (k / n) ** 0.5; d = w / n
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
    Imono = 0; marg = None; mono_vals = []
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
    mono_avg = sum(mono_vals) / len(mono_vals) if mono_vals else float('nan')
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
    samp_avg = sum(samp_vals) / len(samp_vals) if samp_vals else float('nan')
    beats = sum(1 for v in samp_vals if v > Imono)
    tagJ = 'ABOVE-J' if d > J else ('below-J' if d < J else 'AT-J')
    print(f"n={n} q={q} k={k} (rho={k/n:.3f} q/n={q/n:.0f}) w={w} d={d:.3f} {tagJ} J={J:.3f} a={a}", flush=True)
    print(f"   MONO:    worst={Imono} (x^{marg[0]},x^{marg[1]})  avg={mono_avg:.2f}  #far_mono={len(mono_vals)}", flush=True)
    if samp_vals and Imono:
        srt = sorted(samp_vals)
        print(f"   NONMONO: worst(sampled {tried})={Isamp}  AVG={samp_avg:.2f}  min={srt[0]}  median={srt[len(srt)//2]}  max={srt[-1]}", flush=True)
        vA = "UNDERESTIMATES" if Isamp > Imono else "worst-mono>=worst-sampled"
        vB = "BELOW-AVG" if Imono < samp_avg else "NOT-below-avg(worst-mono ABOVE mean pencil)"
        print(f"   --> (A) {vA}  worst_nonmono/worst_mono={Isamp/Imono:.3f}", flush=True)
        print(f"   --> (B) {vB}  avg_nonmono/worst_mono={samp_avg/Imono:.3f}  #beating={beats}/{tried}", flush=True)
    print(flush=True)

if __name__ == "__main__":
    print("=== n=12 ABOVE-Johnson at deeper q, heavier non-mono sampling ===\n", flush=True)
    # w=4 -> d=0.333 above J=0.293.  Increase q (deeper q>>n) and samples.
    run(97, 12, 6, 4, nsamp=120)    # q/n=8
    run(157, 12, 6, 4, nsamp=80)    # q/n=13
    print("done", flush=True)
