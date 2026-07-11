#!/usr/bin/env python3
"""
probe_monomial_extremality_verify.py  (issue #389)  -- ADVERSARIAL VERIFICATION of:

  "Monomial far directions are SUB-optimal (below the AVERAGE pencil incidence) in the
   prize regime, so 'worst-over-monomials' UNDERESTIMATES I(delta)."

The original probe (probe_qbign_pencil_extremal.py) reported only the SAMPLED MAX
non-monomial incidence, NOT the average.  The claim is phrased two distinct ways that
must be measured separately:
  (A)  worst-monomial < worst-pencil   ==>  worst-over-monomials UNDERESTIMATES I = max-incidence
  (B)  worst-monomial < AVERAGE-pencil ==>  monomials literally below the mean pencil

This script measures BOTH, plus the average, the monomial average, and the full
distribution, at several genuine q>>n points and multiple radii spanning Johnson.

#bad(u0,u1) = #{gamma in F_q : maxagree(u0 + gamma*u1, RS[k]) >= a},  a = n - w.
A "far direction" requires u1 itself far (maxagree(u1) < a) so the pencil is a genuine far coset.
"""
import itertools, random


def inv(a, q):
    return pow(a, q - 2, q)


def rou(q, n):
    """Return n n-th roots of unity in F_q (requires n | q-1), via a primitive root."""
    for g in range(2, q):
        x = 1; s = set()
        for _ in range(q - 1):
            x = x * g % q; s.add(x)
        if len(s) == q - 1:
            o = pow(g, (q - 1) // n, q)
            return [pow(o, i, q) for i in range(n)]
    return None


def interp_fit(pts_idx, mu, vals, q, k):
    xs = [mu[i] for i in pts_idx]; ys = [vals[i] for i in pts_idx]
    res = [0] * len(mu)
    for t in range(len(mu)):
        xt = mu[t]; acc = 0
        for j in range(k):
            num = 1; den = 1
            for l in range(k):
                if l != j:
                    num = num * (xt - xs[l]) % q; den = den * (xs[j] - xs[l]) % q
            acc = (acc + ys[j] * num * inv(den, q)) % q
        res[t] = acc
    return res


def maxagree(mu, vals, q, k, n):
    best = 0
    for sub in itertools.combinations(range(n), k):
        f = interp_fit(sub, mu, vals, q, k)
        c = sum(1 for i in range(n) if f[i] == vals[i])
        if c > best:
            best = c
            if best == n:
                break
    return best


def nbad(mu, u0, u1, q, k, n, a):
    c = 0
    for g in range(q):
        v = [(u0[i] + g * u1[i]) % q for i in range(n)]
        if maxagree(mu, v, q, k, n) >= a:
            c += 1
    return c


def isfar(mu, u1, q, k, n, a):
    return maxagree(mu, u1, q, k, n) < a


def run(q, n, k, w, nsamp=400, seed=3):
    mu = rou(q, n)
    if mu is None:
        print(f"  (no primitive root / rou failed for q={q})")
        return None
    a = n - w
    J = 1 - (k / n) ** 0.5
    d = w / n

    # ---- ALL monomial pencils (x^b, x^c), b != c, with x^c far ----
    monwords = [[pow(mu[i], e, q) for i in range(n)] for e in range(n)]
    mono_vals = []
    Imono = 0; marg = None
    for b in range(n):
        for c in range(n):
            if b == c:
                continue
            u1 = monwords[c]
            if not isfar(mu, u1, q, k, n, a):
                continue
            nb = nbad(mu, monwords[b], u1, q, k, n, a)
            mono_vals.append(nb)
            if nb > Imono:
                Imono, marg = nb, (b, c)
    mono_avg = (sum(mono_vals) / len(mono_vals)) if mono_vals else float('nan')

    # ---- random NON-monomial pencils: FULL distribution ----
    rng = random.Random(seed)
    samp_vals = []
    Isamp = 0; sarg = None
    tried = 0
    attempts = 0
    while tried < nsamp and attempts < nsamp * 60:
        attempts += 1
        u0 = [rng.randrange(q) for _ in range(n)]
        u1 = [rng.randrange(q) for _ in range(n)]
        if not isfar(mu, u1, q, k, n, a):
            continue
        tried += 1
        nb = nbad(mu, u0, u1, q, k, n, a)
        samp_vals.append(nb)
        if nb > Isamp:
            Isamp, sarg = nb, (u0, u1)
    samp_avg = (sum(samp_vals) / len(samp_vals)) if samp_vals else float('nan')
    beats_worst_mono = sum(1 for v in samp_vals if v > Imono)

    tagJ = 'ABOVE-J' if d > J else ('AT-J' if abs(d - J) < 1e-9 else 'below-J')
    print(f"n={n} q={q} k={k} (rho={k/n:.3f} q/n={q/n:.0f}) w={w} d={d:.3f} {tagJ} J={J:.3f} a={a}")
    if mono_vals:
        print(f"   MONO:    worst={Imono} (x^{marg[0]},x^{marg[1]})  avg={mono_avg:.2f}  "
              f"#far_mono_pencils={len(mono_vals)}  incid/q(worst)={Imono / q:.4f}")
    else:
        print(f"   MONO:    (no far monomial pencils at this radius)")
    if samp_vals:
        srt = sorted(samp_vals)
        print(f"   NONMONO: worst(sampled {tried})={Isamp}  AVG={samp_avg:.2f}  "
              f"min={srt[0]}  median={srt[len(srt) // 2]}  max={srt[-1]}")
        if Imono:
            print(f"   --> worst_nonmono/worst_mono = {Isamp / Imono:.3f}   "
                  f"AVG_nonmono/worst_mono = {samp_avg / Imono:.3f}")
            verdict_A = "UNDERESTIMATES (worst nonmono > worst mono)" if Isamp > Imono else "worst-mono >= worst sampled nonmono"
            verdict_B = ("BELOW AVG (worst mono < avg pencil)" if Imono < samp_avg
                         else "NOT below avg (worst mono >= avg pencil)")
            print(f"   --> (A) worst-over-monomials: {verdict_A}")
            print(f"   --> (B) worst-mono vs avg-pencil: {verdict_B}   "
                  f"(#samples beating worst-mono = {beats_worst_mono}/{tried})")
    print()
    return dict(q=q, n=n, k=k, w=w, d=d, J=J, tagJ=tagJ, Imono=Imono, mono_avg=mono_avg,
                Isamp=Isamp, samp_avg=samp_avg, beats=beats_worst_mono, tried=tried)


if __name__ == "__main__":
    print("=== ADVERSARIAL: monomial extremality above/below Johnson, genuine q>>n ===\n")
    results = []
    # Point 1: the original claimed point (reproduce).
    results.append(run(257, 8, 4, 3, nsamp=120))
    results.append(run(257, 8, 4, 2, nsamp=120))
    # Point 2: same n=8, LARGER q (q=8m+1): isolate q-dependence of the finding.
    results.append(run(433, 8, 4, 3, nsamp=100))
    results.append(run(1009, 8, 4, 3, nsamp=60))
    # Point 3: LARGER n=12 (q=12m+1), multiple radii spanning Johnson.
    #   k=6 => rho=0.5, J=0.293.  w/12: 3->0.25(below), 4->0.333(above), 5->0.417(above)
    for w in (3, 4, 5):
        results.append(run(61, 12, 6, w, nsamp=80))
    # Point 4: n=12, different rate k=4 (rho=0.333, J=0.423), push above Johnson.
    for w in (5, 6):
        results.append(run(61, 12, 4, w, nsamp=80))
    print("done")
