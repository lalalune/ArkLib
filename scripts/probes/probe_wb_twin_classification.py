#!/usr/bin/env python3
"""Twin classification at grade 2 (#371, WB-5/WB-6 residual).

A twin pair (i,j) has coincidence polynomial g_ij == 0 identically: the Cramer
ratio functions lambda_i, lambda_j coincide at EVERY gamma. The per-grade
residual of the graded ladder is twin-freeness; this probe classifies when
twins occur at the grade-2 slice (29,7,4,2) and (113,8,5,2) [mu8 | 112]:

1. random genuine rational stacks: twin-pair count (prediction: 0 - else their
   bad counts would q-scale, contradicting the C(n,2) saturation);
2. structured stacks: shared denominators, sigma-aligned rows (u1 = Moebius
   image of u0 under x -> c/x normalizer maps), proportional numerators;
3. for every twin found: test normalizer alignment x_j = c/x_i or x_j = -x_i.
"""
import random, os
from collections import Counter
exec(open(os.path.join(os.path.dirname(os.path.abspath(__file__)),
     "probe_wb_window_pencil_crt.py")).read().split("total_mm = 0")[0]
     .replace('random.seed(20260611)', 'pass'))
random.seed(99887)

def gen_mu(q, n):
    for cand in range(2, q):
        if pow(cand, n, q) == 1 and all(pow(cand, d, q) != 1 for d in range(1, n) if n % d == 0):
            return cand
    return None

def twin_pairs(inst, l0, r0, l1, r1):
    """Pairs (i,j) whose ratio functions coincide at every gamma with kerdim 2.
    Detected via: at every gamma where kerdim == 2, the projective pairs
    (z1[i]:z2[i]) and (z1[j]:z2[j]) coincide.  (Degree <= 2w+2 < q => identical.)"""
    q, n, w = inst.q, inst.n, inst.w
    M0, M1, dims = pencil_matrices(inst, l0, r0, l1, r1)
    ncol = sum(dims); nz = dims[0]
    agree = {}
    seen = 0
    for gam in range(q):
        M = [[(M0[i][j] + gam * M1[i][j]) % q for j in range(ncol)]
             for i in range(len(M0))]
        rk, ker = rank_and_kernel(M, q, want_kernel=True)
        if len(ker) != 2:
            continue
        seen += 1
        K1, K2 = ker
        z1 = [sum(K1[t] * pow(a, t, q) for t in range(nz)) % q for a in inst.dom]
        z2 = [sum(K2[t] * pow(a, t, q) for t in range(nz)) % q for a in inst.dom]
        for i in range(n):
            for j in range(i + 1, n):
                # projective equality (z1i:z2i) == (z1j:z2j) <=> z1i*z2j == z1j*z2i
                eq = (z1[i] * z2[j] - z1[j] * z2[i]) % q == 0
                key = (i, j)
                if key not in agree:
                    agree[key] = eq
                else:
                    agree[key] = agree[key] and eq
    if seen == 0:
        return None, 0
    return [k for k, v in agree.items() if v], seen

def normalizer_aligned(inst, i, j):
    """x_j = c/x_i for some c with the map preserving the domain, or x_j = -x_i."""
    q = inst.q
    xi, xj = inst.dom[i], inst.dom[j]
    if (xi + xj) % q == 0:
        return "neg"
    c = (xi * xj) % q  # x_j = c / x_i
    # does x -> c/x preserve the domain set?
    dset = set(inst.dom)
    if all((c * pow(x, q - 2, q)) % q in dset for x in inst.dom):
        return f"inv(c={c})"
    return None

def run(q, n, k, w, trials_random, trials_struct):
    g = gen_mu(q, n)
    inst = Inst(q, n, k, w, g)
    print(f"\n=== (q,n,k,w)=({q},{n},{k},{w}) dom={inst.dom} ===", flush=True)
    stats = Counter()
    twin_reports = []
    def consider(tag, l0, r0, l1, r1):
        tp, seen = twin_pairs(inst, l0, r0, l1, r1)
        if tp is None:
            stats[(tag, "nokerdim2")] += 1
            return
        stats[(tag, f"twins{len(tp)}")] += 1
        if tp:
            u0, u1 = inst.ratword(l0, r0), inst.ratword(l1, r1)
            B = bad_set(inst, u0, u1) if u0 and u1 else set()
            aligns = [(p, normalizer_aligned(inst, *p)) for p in tp]
            twin_reports.append((tag, tp, aligns, len(B)))
            print(f"  TWIN [{tag}] pairs={tp} align={aligns} |BAD|={len(B)}", flush=True)
    for _ in range(trials_random):
        l0 = [random.randrange(q) for _ in range(w + 1)]
        r0 = [random.randrange(q) for _ in range(w + k)]
        l1 = [random.randrange(q) for _ in range(w + 1)]
        r1 = [random.randrange(q) for _ in range(w + k)]
        if not (genuine_reduced(inst, l0, r0) and genuine_reduced(inst, l1, r1)):
            continue
        if inst.ratword(l0, r0) is None or inst.ratword(l1, r1) is None:
            continue
        consider("random", l0, r0, l1, r1)
    for _ in range(trials_struct):
        mode = random.randrange(3)
        l0 = [random.randrange(q) for _ in range(w + 1)]
        r0 = [random.randrange(q) for _ in range(w + k)]
        if not genuine_reduced(inst, l0, r0):
            continue
        u0 = inst.ratword(l0, r0)
        if u0 is None:
            continue
        if mode == 0:    # shared denominator
            l1, r1 = l0[:], [random.randrange(q) for _ in range(w + k)]
        elif mode == 1:  # proportional numerator
            l1, r1 = [random.randrange(q) for _ in range(w + 1)], psmul(random.randrange(1, q), r0, q)
        else:            # sigma-image row: u1(x) = u0(c/x) for domain-preserving inversion
            c = (inst.dom[0] * inst.dom[1]) % q
            dset = set(inst.dom)
            if not all((c * pow(x, q - 2, q)) % q in dset for x in inst.dom):
                continue
            u1 = [u0[inst.dom.index((c * pow(x, q - 2, q)) % q)] for x in inst.dom]
            # find a WB rep of u1
            ncolwb = (w + 1) + (w + k)
            M = []
            for i, x in enumerate(inst.dom):
                row = [pow(x, t, q) * u1[i] % q for t in range(w + 1)]
                row += [(-pow(x, s, q)) % q for s in range(w + k)]
                M.append(row)
            _, ker = rank_and_kernel(M, q, want_kernel=True)
            rep = next(((pnorm(list(v[:w + 1])), pnorm(list(v[w + 1:])))
                        for v in ker if pnorm(list(v[:w + 1]))), None)
            if rep is None:
                continue
            l1, r1 = rep
        if not genuine_reduced(inst, l1, r1):
            continue
        if inst.ratword(l1, r1) is None:
            continue
        consider(f"struct{mode}", l0, r0, l1, r1)
    print(f"stats: {dict(sorted(stats.items(), key=str))}")
    print(f"twin stacks found: {len(twin_reports)}")

run(29, 7, 4, 2, 60, 60)
run(113, 8, 5, 2, 30, 40)
