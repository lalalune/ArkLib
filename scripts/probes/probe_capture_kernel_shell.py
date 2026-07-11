#!/usr/bin/env python3
"""Falsify-first probe for the capture-kernel OUTER SHELL (issue #232 / #302, O78).

Target Lean statements (CaptureKernelShell.lean):

  K1 (root extraction): over R[Y] with R = F[x] (reduced),
      (Y - C q) | (Y - C r)^e, e > 0  ==>  q = r.

  K2 (capture extraction): if gamma is mca-bad (witness set S: |S| >= (1-d)n,
      some codeword w agrees with the fold u0 + gamma*u1 on S, and no joint pair
      agrees on S), and EVERY deg<k polynomial agreeing with the fold on >= (1-d)n
      points divides into the affine power (Y - C(a + gamma*b))^e, then
      AffineCaptured holds for gamma with the SAME witness set S.

  K3 (bad-restriction normalization): replacing every cell E_ij by E_ij \cap bad
      preserves the cover of bad scalars, and only shrinks cells (so the
      capture-above-n obligation weakens monotonically).

The probe checks all three on GF(13), n = 6, k = 2 with planted MCA-bad stacks,
exhaustively over witness sets, plus randomized K1 trials including q = 0 and
q = r edge cases.  Any violation exits 1.
"""

import itertools, random, sys

P = 13  # field GF(13)
random.seed(232078)

# ---------- polynomial helpers over GF(P), coefficient lists little-endian ----
def pnorm(c):
    c = [x % P for x in c]
    while c and c[-1] == 0:
        c.pop()
    return c

def padd(a, b):
    n = max(len(a), len(b))
    return pnorm([(a[i] if i < len(a) else 0) + (b[i] if i < len(b) else 0) for i in range(n)])

def psub(a, b):
    n = max(len(a), len(b))
    return pnorm([(a[i] if i < len(a) else 0) - (b[i] if i < len(b) else 0) for i in range(n)])

def pmul(a, b):
    if not a or not b:
        return []
    out = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            out[i + j] = (out[i + j] + x * y) % P
    return pnorm(out)

def pscale(a, s):
    return pnorm([x * s for x in a])

def peval(a, x):
    v = 0
    for c in reversed(a):
        v = (v * x + c) % P
    return v

# ---------- bivariate: element of (F[x])[Y] = list of F[x] coeffs (little-endian in Y)
def ypow_sub(r, e):
    """(Y - r(x))^e as list of F[x] coefficients."""
    base = [pscale(r, -1), [1]]  # -r + 1*Y
    out = [[1]]
    for _ in range(e):
        # multiply out * base
        res = [[] for _ in range(len(out) + 1)]
        for i, c in enumerate(out):
            res[i] = padd(res[i], pmul(c, base[0]))
            res[i + 1] = padd(res[i + 1], pmul(c, base[1]))
        out = res
    return out

def yeval(B, q):
    """Evaluate bivariate B (list of F[x] coeffs in Y) at Y := q(x): Horner in F[x]."""
    v = []
    for c in reversed(B):
        v = padd(pmul(v, q), c)
    return v

# ---------- K1: divisibility into affine power -------------------------------
# (Y - C q) | B  in (F[x])[Y]  <=>  remainder of division by monic linear = B(q) == 0.
def k1_trials():
    viol = 0
    trials = 0
    for _ in range(4000):
        dq = random.randint(-1, 3)   # -1 encodes the zero polynomial
        dr = random.randint(-1, 3)
        q = [] if dq < 0 else pnorm([random.randrange(P) for _ in range(dq)] + [random.randrange(1, P)])
        r = [] if dr < 0 else pnorm([random.randrange(P) for _ in range(dr)] + [random.randrange(1, P)])
        if random.random() < 0.3:
            r = q[:]  # force equality edge case
        e = random.choice([1, 2, 3, 4, 13])  # include e = p (Frobenius-shaped)
        B = ypow_sub(r, e)
        rem = yeval(B, q)            # remainder of B by (Y - q)
        dvd = (rem == [])
        trials += 1
        # K1 claim: dvd ==> q == r ; converse trivially: q == r ==> dvd
        if dvd and q != r:
            viol += 1
        if q == r and not dvd:
            viol += 1
    return trials, viol

# ---------- RS / MCA machinery on GF(13), n = 6, k = 2 -----------------------
N, K = 6, 2
DOM = [1, 2, 3, 4, 5, 6]  # injective domain

def rs_eval(poly):  # poly deg < K
    return [peval(poly, x) for x in DOM]

def exists_codeword_agreeing(word, S):
    """Is there a deg<K poly agreeing with word on S?  Return one (or None)."""
    # brute force over all K-coefficient polys: 13^2 = 169
    for c0 in range(P):
        for c1 in range(P):
            pl = pnorm([c0, c1])
            if all(peval(pl, DOM[i]) == word[i] % P for i in S):
                return pl
    return None

def pair_joint_agrees(u0, u1, S):
    return (exists_codeword_agreeing(u0, S) is not None and
            exists_codeword_agreeing(u1, S) is not None)

def mca_bad_witnesses(u0, u1, gamma, tmin):
    """All witness sets S (|S| >= tmin) certifying mcaEvent for gamma."""
    fold = [(u0[i] + gamma * u1[i]) % P for i in range(N)]
    out = []
    for sz in range(tmin, N + 1):
        for S in itertools.combinations(range(N), sz):
            q = exists_codeword_agreeing(fold, S)
            if q is None:
                continue
            if not pair_joint_agrees(u0, u1, S):
                out.append((S, q))
    return out

def k2_k3_trials():
    """Planted instances; check the K2 extraction and assembled AffineCaptured."""
    viol_k2 = 0
    captures_checked = 0
    bad_gamma_total = 0
    inst = 0
    for trial in range(60):
        # plant: rows = codeword + error of weight wt
        a = pnorm([random.randrange(P) for _ in range(K)])
        b = pnorm([random.randrange(P) for _ in range(K)])
        wt = random.choice([1, 2])
        pos = random.sample(range(N), wt)
        u0 = rs_eval(a)[:]
        u1 = rs_eval(b)[:]
        for i in pos:
            u0[i] = (u0[i] + random.randrange(1, P)) % P
            u1[i] = (u1[i] + random.randrange(1, P)) % P
        delta_n = wt          # delta = wt/n; witness sets size >= n - wt
        tmin = N - delta_n
        inst += 1
        for gamma in range(P):
            wits = mca_bad_witnesses(u0, u1, gamma, tmin)
            if not wits:
                continue
            bad_gamma_total += 1
            # the affine specialization the forcing would hand us
            agb = padd(a, pscale(b, gamma))
            for (S, q) in wits:
                # dvd supply test: does q agree with fold on >= tmin points AND
                # divide the affine power?  (here: dvd <=> q == agb, by K1 checked
                # independently above; we verify the assembled AffineCaptured)
                e = 13  # p^f shape
                B = ypow_sub(agb, e)
                dvd = (yeval(B, q) == [])
                if dvd:
                    # K2 conclusion: AffineCaptured with the SAME S:
                    # (a + gamma*b) evals = fold on S, and no joint pair on S (by construction)
                    captures_checked += 1
                    fold = [(u0[i] + gamma * u1[i]) % P for i in range(N)]
                    ok = all(peval(agb, DOM[i]) == fold[i] for i in S)
                    if not ok or pair_joint_agrees(u0, u1, S):
                        viol_k2 += 1
                else:
                    # q != agb: the supply hypothesis simply does not hold for this
                    # cell; no obligation. Sanity: q really differs from agb.
                    if q == agb:
                        viol_k2 += 1
    # K3: random cells, restriction normalization
    viol_k3 = 0
    for _ in range(2000):
        bad = set(random.sample(range(P), random.randint(0, P)))
        ncells = random.randint(1, 4)
        cells = [set(random.sample(range(P), random.randint(0, P))) for _ in range(ncells)]
        # only test instances where the cover holds
        if not bad <= set().union(*cells):
            continue
        rcells = [c & bad for c in cells]
        if not bad <= set().union(*rcells):
            viol_k3 += 1                       # cover must be preserved
        if any(len(rc) > len(c) for rc, c in zip(rcells, cells)):
            viol_k3 += 1                       # cells only shrink
    return inst, bad_gamma_total, captures_checked, viol_k2, viol_k3

t1, v1 = k1_trials()
inst, badg, caps, v2, v3 = k2_k3_trials()
print(f"K1 root-extraction trials: {t1}, violations: {v1}")
print(f"K2 planted instances: {inst}, mca-bad (gamma, instance) pairs: {badg}, "
      f"assembled AffineCaptured checks: {caps}, violations: {v2}")
print(f"K3 bad-restriction trials (cover+monotone): violations: {v3}")
ok = (v1 == 0 and v2 == 0 and v3 == 0 and caps > 0 and badg > 0)
print("PROBE", "PASS" if ok else "FAIL")
sys.exit(0 if ok else 1)
