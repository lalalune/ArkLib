#!/usr/bin/env python3
"""
Multi-frame adversarial stacks (p=17 toy + p=12289 target; n=16, k=3, s=7).

The assembly gap: per agreement set A, my proven laws cap scalars PER FRAME
(off-part disjointness, <= 16-|A|), but the number of FRAMES per A is only
Fisher-bounded (~C(|A|,3)) -- composed cap ~200 vs census truth 16.  The
missing rigidity is cross-frame (pool-span applies to EVERY distinct pair).

This probe ENGINEERS stacks with multiple frames on one A:
  R1 = q + m_A * h;  frame i: T_i subset A (3 pts, disjoint), S_i = T_i + 4
  fresh off-A points, R0 values on S_i := (P_i - gamma_i*R1)(x) -- forcing
  gamma_i bad with witness S_i.  Free R0 values randomized.
Then runs the FULL fast census (per 7-subset residue alignment: res_S(R0) +
gamma*res_S(R1) must drop below degree 3 -- 4 linear conditions, <= 1 gamma
per subset unless degenerate) and reports: total bad count, per-A frame
structure of the bad set, and whether any engineered stack beats the pencil's
16 or approaches the obligation 31.
"""
import itertools, random, sys

def run(p, trials, label, seed):
    n, k, s = 16, 3, 7
    # domain = mu_16 in F_p
    g0 = next(g for g in range(2, 500)
              if pow(g, (p - 1) // 2, p) != 1
              and all((p - 1) % f or pow(g, (p - 1) // f, p) != 1
                      for f in (3, 5, 7)))
    w = pow(g0, (p - 1) // n, p)
    assert pow(w, n, p) == 1 and all(pow(w, j, p) != 1 for j in range(1, n))
    D = [pow(w, j, p) for j in range(n)]

    def polmul(a, b):
        out = [0] * (len(a) + len(b) - 1)
        for i, x in enumerate(a):
            if x:
                for j, y in enumerate(b):
                    out[i + j] = (out[i + j] + x * y) % p
        return out

    def m_of(pts):
        out = [1]
        for x in pts:
            out = polmul(out, [(-x) % p, 1])
        return out

    def peval(f, x):
        r = 0
        for c in reversed(f):
            r = (r * x + c) % p
        return r

    def interp(pts, vals):
        # full Lagrange -> coefficient vector (len = len(pts))
        m = len(pts)
        coeffs = [0] * m
        for i in range(m):
            num = [1]
            den = 1
            for j in range(m):
                if j == i:
                    continue
                num = polmul(num, [(-pts[j]) % p, 1])
                den = den * ((pts[i] - pts[j]) % p) % p
            ci = vals[i] * pow(den, p - 2, p) % p
            for t in range(len(num)):
                coeffs[t] = (coeffs[t] + ci * num[t]) % p
        return coeffs

    SUBS = list(itertools.combinations(range(n), s))

    def census(u0, u1):
        """fast census: per 7-subset solve the residue alignment for gamma."""
        bad = {}          # gamma -> list of witness subsets
        for S in SUBS:
            pts = [D[i] for i in S]
            a = interp(pts, [u0[i] for i in S])   # deg<=6 interpolant of u0|S
            b = interp(pts, [u1[i] for i in S])   # deg<=6 interpolant of u1|S
            # need a + gamma*b to have deg < 3: coeffs 3..6 vanish
            top_a = [a[t] if t < len(a) else 0 for t in range(3, 7)]
            top_b = [b[t] if t < len(b) else 0 for t in range(3, 7)]
            if all(x == 0 for x in top_b):
                if all(x == 0 for x in top_a):
                    continue  # both explainable on S -> joint -> not a witness
                continue      # no gamma can cancel a's top
            # unique gamma candidate from first nonzero of top_b; verify rest
            j = next(t for t in range(4) if top_b[t])
            gam = (-top_a[j]) * pow(top_b[j], p - 2, p) % p
            if all((top_a[t] + gam * top_b[t]) % p == 0 for t in range(4)):
                # explainable; badness needs NOT-joint: u0|S or u1|S not deg<3
                a_low = all(x == 0 for x in
                            [a[t] if t < len(a) else 0 for t in range(3, 7)])
                b_low = False  # top_b nonzero => u1|S not deg<3 => not joint
                if not (a_low and b_low):
                    bad.setdefault(gam, []).append(S)
        return bad

    best = 0
    best_info = None
    for trial in range(trials):
        rng = random.Random(seed + trial)
        asz = rng.choice([6, 6, 7, 8])
        A = sorted(rng.sample(range(n), asz))
        offA = [i for i in range(n) if i not in A]
        q = [rng.randrange(p) for _ in range(3)]
        # h: random, degree such that deg R1 <= 15; avoid domain roots off A
        for _ in range(50):
            h = [rng.randrange(p) for _ in range(rng.choice([2, 3, 4]))]
            h[-1] = h[-1] or 1
            if all(peval(h, D[i]) for i in offA):
                break
        mA = m_of([D[i] for i in A])
        R1 = [0] * max(len(q), len(mA) + len(h) - 1)
        for t, c in enumerate(q):
            R1[t] = c
        prod = polmul(mA, h)
        for t, c in enumerate(prod):
            R1[t] = (R1[t] + c) % p
        # frames: 2 or 3, disjoint 3-subsets of A, disjoint 4-point off-parts
        nf = rng.choice([2, 2, 3]) if asz >= (3 * 3 if False else 6) else 2
        nf = min(nf, asz // 3, len(offA) // 4)
        nf = max(nf, 1)
        Apts = rng.sample(A, 3 * nf)
        Opts = rng.sample(offA, 4 * nf)
        u0 = [None] * n
        u1 = [peval(R1, D[i]) for i in range(n)]
        gams = rng.sample(range(1, p), nf)
        for f in range(nf):
            T = Apts[3 * f:3 * f + 3]
            O = Opts[4 * f:4 * f + 4]
            P = [rng.randrange(p) for _ in range(3)]
            for i in T + O:
                u0[i] = (peval(P, D[i]) - gams[f] * u1[i]) % p
        for i in range(n):
            if u0[i] is None:
                u0[i] = rng.randrange(p)
        bad = census(u0, u1)
        tot = len(bad)
        if tot > best:
            best = tot
            # frame structure of the maximizer: witness count per scalar
            best_info = (asz, nf, tot,
                         sorted(len(v) for v in bad.values())[-5:])
        if tot > 16:
            print(f"  [{label}] trial {trial}: BEAT-16! total={tot} "
                  f"(|A|={asz}, frames={nf})")
    print(f"[{label}] {trials} engineered multi-frame stacks: "
          f"max total bad = {best}  (info: |A|,nf,tot,top-witness-counts = "
          f"{best_info})")
    return best

if __name__ == "__main__":
    random.seed(424)
    b1 = run(17, 120, "p=17", 1000)
    b2 = run(12289, 40, "p=12289", 2000)
    print(f"VERDICT: max engineered total {max(b1, b2)} vs pencil 16 vs "
          f"obligation 31")
