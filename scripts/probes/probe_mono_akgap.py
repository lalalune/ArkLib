#!/usr/bin/env python3
"""
probe_mono_akgap.py  (issue #389)

DIAGNOSE the n=8 vs n=12 FLIP found in the monomial-extremality verification:
  n=8  k=4 w=3: a=5 = k+1 -> monomials BELOW average pencil (sub-optimal)   [original finding]
  n=12 k=6 w=4: a=8 = k+2 -> monomials ABOVE average pencil (extremal)      [contradicts it]

HYPOTHESIS: the controlling parameter is (a - k), NOT n.  At a=k+1 (shallowest above-Johnson
stratum, huge ball) random pencils swamp the atypically-sparse monomial; at a>=k+2 the tighter
constraint favours the monomial's structure.

TEST on n=10 k=5 (q=10m+1: 11,31,41,61,71,101), which reaches BOTH a=k+1 and a=k+2 above Johnson:
  w=4 d=0.40 above J=0.293, a=6 = k+1
  w=3 d=0.30 above J=0.293, a=7 = k+2
If the flip tracks (a-k) and not n, n=10 should show: a=k+1 -> mono below avg ; a=k+2 -> mono above avg.
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
        xs = [mu[i] for i in sub]; rowt = []
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

def run(q, n, k, w, nsamp, seed=13):
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
    print(f"n={n} q={q} k={k} (q/n={q/n:.0f}) w={w} d={d:.3f} {tagJ} J={J:.3f} a={a}=k+{a-k}", flush=True)
    print(f"   MONO:    worst={Imono} (x^{marg[0]},x^{marg[1]})  avg={mono_avg:.2f}  #far_mono={len(mono_vals)}", flush=True)
    if samp_vals and Imono:
        srt = sorted(samp_vals)
        print(f"   NONMONO: worst(samp {tried})={Isamp}  AVG={samp_avg:.2f}  median={srt[len(srt)//2]}  max={srt[-1]}", flush=True)
        vB = "mono BELOW avg (sub-optimal)" if Imono < samp_avg else "mono ABOVE avg (extremal-ish)"
        print(f"   --> (a-k={a-k}) {vB}  avg/worst-mono={samp_avg/Imono:.3f}  worst-nonmono/worst-mono={Isamp/Imono:.3f}  #beating={beats}/{tried}", flush=True)
    print(flush=True)

if __name__ == "__main__":
    print("=== a-k FLIP DIAGNOSIS on n=10 k=5 (both a=k+1 and a=k+2 are above Johnson) ===\n", flush=True)
    # n=10 needs 10 | q-1: q=11,31,41,61,71,101
    run(41, 10, 5, 4, nsamp=120)   # a=6=k+1, above J  -> predict mono BELOW avg
    run(41, 10, 5, 3, nsamp=120)   # a=7=k+2, above J  -> predict mono ABOVE avg
    run(101, 10, 5, 4, nsamp=60)   # deeper q, a=k+1
    run(101, 10, 5, 3, nsamp=60)   # deeper q, a=k+2
    print("done", flush=True)
