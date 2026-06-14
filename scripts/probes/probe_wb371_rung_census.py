#!/usr/bin/env python3
"""
The rung census falsification probe (toy -> target protocol).

CONJECTURE under test (the good-side obligation's truth): for polynomial-pair
stacks at the d=2 level-1 rung shape (n=16, k=3, |S|=7), the number of distinct
nonzero fiber-gammas is <= 16 (= n; budget needs <= 31).

Adversarial constructions maximizing R1's quadratic-agreement geometry:
  (a) R1 = X^9 (the pencil: agreement = half-cosets, known 16);
  (b) R1 = q + m_A*h for engineered agreement sets A (|A| = 6..8), q quadratic,
      deg h <= 9-|A|: R1 == q on A by construction; pair two structures;
  (c) R0 aligned to light up structures: R0 = q0 + m_A*h0 variants;
  (d) random controls.

Protocol: TOY at p=17 (mu_16 = F_17^*), then TARGET at p=12289.
Output: max distinct nonzero gammas per construction per scale, vs 16 and 31.
"""
import itertools, random

def run_scale(p, label, n=16, GDEG=2, PDEG=2, DEG_R1=9, trials=40):
    def mu_n():
        if p == 17:
            return list(range(1, 17))
        for g in range(2, 300):
            ok = True
            for f in (2, 3):
                if (p - 1) % f == 0 and pow(g, (p - 1) // f, p) == 1:
                    ok = False
                    break
            if ok:
                h = pow(g, (p - 1) // n, p)
                pts = sorted(pow(h, j, p) for j in range(n))
                if len(set(pts)) == n:
                    return pts
        raise RuntimeError
    D = mu_n()

    def polmul(a, b):
        out = [0] * (len(a) + len(b) - 1)
        for i, x in enumerate(a):
            if x:
                for j, y in enumerate(b):
                    out[i + j] = (out[i + j] + x * y) % p
        return out

    def m_of(T):
        out = [1]
        for x in T:
            out = polmul(out, [(-x) % p, 1])
        return out

    def polmod(a, b):
        a = [x % p for x in a]
        db = max(i for i in range(len(b)) if b[i] % p)
        inv = pow(b[db], p - 2, p)
        for i in range(len(a) - 1, db - 1, -1):
            c = a[i] % p
            if c:
                f = (c * inv) % p
                for j in range(db + 1):
                    a[i - db + j] = (a[i - db + j] - f * b[j]) % p
        out = [x % p for x in a[:db]]
        return out + [0] * (db - len(out))

    def solve_affine(M, rhs):
        rows = len(M); cols = len(M[0])
        Aug = [M[r][:] + [rhs[r]] for r in range(rows)]
        piv_cols = []
        r = 0
        for c in range(cols):
            piv = None
            for rr in range(r, rows):
                if Aug[rr][c] % p:
                    piv = rr; break
            if piv is None:
                continue
            Aug[r], Aug[piv] = Aug[piv], Aug[r]
            ip = pow(Aug[r][c], p - 2, p)
            Aug[r] = [(x * ip) % p for x in Aug[r]]
            for rr in range(rows):
                if rr != r and Aug[rr][c] % p:
                    f = Aug[rr][c]
                    Aug[rr] = [(Aug[rr][i] - f * Aug[r][i]) % p
                               for i in range(cols + 1)]
            piv_cols.append(c)
            r += 1
        for rr in range(r, rows):
            if Aug[rr][cols] % p:
                return None
        base = [0] * cols
        for i, c in enumerate(piv_cols):
            base[c] = Aug[i][cols]
        kernel_count = cols - len(piv_cols)
        return base, kernel_count

    SUBS7 = list(itertools.combinations(range(n), 7))

    def fiber_count(R0, R1):
        """count distinct nonzero gammas with a dim-0 fiber solution;
           flag higher-dim solution spaces separately."""
        if max(i for i in range(len(R1)) if R1[i] % p) != DEG_R1:
            return -1, 0  # R1 not deg 9; skip
        # normalize monic
        lead = R1[DEG_R1]
        if lead != 1:
            inv = pow(lead, p - 2, p)
            R1 = [(x * inv) % p for x in R1]
            R0 = [(x * inv) % p for x in R0]
        R0p = [(R0[i] if i < len(R0) else 0) % p for i in range(10)]
        gam = set()
        flags = 0
        for Sidx in SUBS7:
            S = [D[i] for i in Sidx]
            mS = m_of(S)
            cols = []
            for gi in range(GDEG + 1):
                cols.append(polmod(polmul([0] * gi + [1], mS), R1))
            for pi in range(PDEG + 1):
                cols.append(polmod([0] * pi + [1], R1))
            rhs_poly = polmod(R0p, R1)
            M = [[cols[c][r] for c in range(6)] for r in range(DEG_R1)]
            rhs = [rhs_poly[r] for r in range(DEG_R1)]
            sol = solve_affine(M, rhs)
            if sol is None:
                continue
            base, kdim = sol
            def gamma_of(v):
                tot9 = 0
                for gi in range(GDEG + 1):
                    full = polmul([0] * gi + [1], mS)
                    if len(full) > 9:
                        tot9 = (tot9 + v[gi] * full[9]) % p
                tot9 = (tot9 - (R0p[9] if len(R0p) > 9 else 0)) % p
                return tot9
            if kdim == 0:
                gv = gamma_of(base)
                if gv:
                    gam.add(gv)
            else:
                flags += 1
        return len(gam), flags

    random.seed(7 + p)
    results = {}
    # (a) pencil
    R0 = [0] * 8 + [1]
    R1 = [0] * 9 + [1]
    c, f = fiber_count(R0, R1)
    results["pencil"] = (c, f)
    best = (c, "pencil")
    # (b)+(c) engineered agreement structures
    for trial in range(trials):
        sizeA = random.choice([6, 7, 8])
        A = random.sample(D, sizeA)
        q = [random.randrange(p) for _ in range(3)]
        hdeg = DEG_R1 - sizeA
        h = [random.randrange(p) for _ in range(hdeg)] + [1]
        R1c = polmod_free = polmul(m_of(A), h)
        R1c = [(R1c[i] if i < len(R1c) else 0) + (q[i] if i < 3 else 0)
               for i in range(max(len(R1c), 3))]
        R1c = [x % p for x in R1c]
        # R0 variants: aligned (same A) or random
        if trial % 2 == 0:
            q0 = [random.randrange(p) for _ in range(3)]
            h0 = [random.randrange(p) for _ in range(max(1, 8 - sizeA))] + [1]
            R0c = polmul(m_of(A), h0)
            R0c = [(R0c[i] if i < len(R0c) else 0) + (q0[i] if i < 3 else 0)
                   for i in range(max(len(R0c), 3))]
            R0c = [x % p for x in R0c]
            tag = f"aligned|A|={sizeA}"
        else:
            R0c = [random.randrange(p) for _ in range(9)]
            tag = f"randR0|A|={sizeA}"
        c, f = fiber_count(R0c, R1c)
        if c > best[0]:
            best = (c, tag)
        results.setdefault(tag, (0, 0))
        if c > results[tag][0]:
            results[tag] = (c, f)
    print(f"[{label} p={p}] pencil={results['pencil']}, "
          f"max over {trials} adversarial: {best}  (n=16, budget=31)")
    return best

print("=== TOY SCALE ===")
toy = run_scale(17, "toy")
print("=== TARGET SCALE ===")
target = run_scale(12289, "target")
print(f"\nVERDICT: toy max {toy[0]} | target max {target[0]} | "
      f"conjecture <=16: {'HOLDS' if max(toy[0], target[0]) <= 16 else 'REFUTED'}"
      f" | budget <=31: {'HOLDS' if max(toy[0], target[0]) <= 31 else 'REFUTED'}")
