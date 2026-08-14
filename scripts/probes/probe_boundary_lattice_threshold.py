#!/usr/bin/env python3
"""Probe: the LATTICE leaf of the corrected boundary threshold route (#304 / #232 frontier).

Context (DISPROOF_LOG O76/O78): both *nonemptiness* leaves of the boundary quantization
split are refuted; the corrected route carries the §5 probability threshold at a
floor-matched strict radius.  At a LATTICE endpoint (deg*n a perfect square, so
delta*n = n - sqrt(deg*n) is integral) there is NO floor-matched strict radius
(`not_exists_lt_floor_eq_of_lattice`), and the §5 threshold `Pr > k*errorBound(delta)`
is vacuous there (errorBound = 0 at the boundary).  The candidate corrected LATTICE
hypothesis is the field-quantitative threshold

    Pr[curve delta-close] > k * (n+1)/q     i.e.    |good| > (n+1)*k,

which by the in-tree assembly bridge
(`goodCoeffsCurve_coeff_polys_implies_jointAgreement_of_pos_core`) plus the §5
coefficient-polynomial extraction implies jointAgreement.  This probe measures, at
lattice endpoints over 4 parameter points (varying q, n, deg, k, incl. a larger q):

  T1  does the quantitative threshold ALONE (|good| > (n+1)k, no extraction) already
      imply jointAgreement?  A violation here is fine for the Lean deliverable (the
      theorem carries the extraction hypothesis) but certifies extraction is
      load-bearing; absence of violations is honest evidence the toy points cannot
      separate them.
  T2  tightness: max |good| among stacks WITHOUT jointAgreement, vs (n+1)k.
  T3  the composite (threshold AND extraction-for-all-P => jointAgreement) — a
      violation would refute the in-tree bridge (expected: none).  For stacks
      failing jointAgreement with |good| > (n+1)k we must find a P-choice with no B.
  T4  witness sanity: the zero stack has good = ALL z, Pr = 1 > k(n+1)/q, and the
      per-z decoding is unique (P z = 0 forced), i.e. the Lean witness spine holds.

Exact integer arithmetic throughout.  Exit 0 iff no T3 violation and T4 holds.
"""

import itertools
import random
import sys
from math import isqrt

def make_field(q):
    inv = [0] * q
    for a in range(1, q):
        inv[a] = pow(a, q - 2, q)
    return inv

def codewords(q, n, deg, domain):
    """All evaluations of polynomials of degree < deg on domain (deg >= 1)."""
    words = []
    polys = []
    for coeffs in itertools.product(range(q), repeat=deg):
        w = tuple(sum(c * pow(x, j, q) for j, c in enumerate(coeffs)) % q
                  for x in domain)
        words.append(w)
        polys.append(coeffs)
    return words, polys

def dist(u, v):
    return sum(1 for a, b in zip(u, v) if a != b)

def curve(q, stack, z):
    n = len(stack[0])
    return tuple(sum(pow(z, t, q) * stack[t][i] for t in range(len(stack))) % q
                 for i in range(n))

def good_set(q, stack, words, radius):
    out = []
    for z in range(q):
        w = curve(q, stack, z)
        if min(dist(w, c) for c in words) <= radius:
            out.append(z)
    return out

def joint_agreement(q, stack, words, agree_min):
    """Exists S, |S| >= agree_min, and per-row codewords agreeing with the row on S."""
    n = len(stack[0])
    cand_rows = []
    for row in stack:
        cands = []
        for c in words:
            ag = frozenset(i for i in range(n) if c[i] == row[i])
            if len(ag) >= agree_min:
                cands.append(ag)
        if not cands:
            return False
        cand_rows.append(cands)
    # product of per-row candidate agreement sets; prune by intersection size
    for combo in itertools.product(*cand_rows):
        inter = set(range(n))
        for ag in combo:
            inter &= ag
            if len(inter) < agree_min:
                break
        else:
            return True
    return False

def decode_lists(q, stack, words, polys, radius, zs):
    """Per z in zs: list of poly coeff-tuples within radius of curve_z."""
    lists = []
    for z in zs:
        w = curve(q, stack, z)
        lz = [polys[ci] for ci, c in enumerate(words) if dist(w, c) <= radius]
        lists.append(lz)
    return lists

def interpolates_deg_le(q, inv, pts, dmax):
    """Do the points (z, y) lie on a polynomial of degree <= dmax?  Lagrange on the
    first dmax+1 points, then verify the rest (z's distinct)."""
    base = pts[:dmax + 1]
    def eval_lagrange(x):
        total = 0
        for i, (xi, yi) in enumerate(base):
            num, den = 1, 1
            for j, (xj, _) in enumerate(base):
                if i == j:
                    continue
                num = num * ((x - xj) % q) % q
                den = den * ((xi - xj) % q) % q
            total = (total + yi * num * inv[den]) % q
        return total
    return all(eval_lagrange(z) == y for z, y in pts)

def extraction_holds(q, inv, deg, k, lists, zs, cap=20000, rng=None):
    """For every choice P (one decoding per z), do all coeff maps z -> P_z[j] lie on a
    degree-<=k polynomial?  Exhaustive if the product of list sizes <= cap, else sampled.
    Returns (verdict, exhaustive, failing_choice_found)."""
    total = 1
    for lz in lists:
        total *= len(lz)
        if total > cap:
            break
    exhaustive = total <= cap
    def check(choice):
        for j in range(deg):
            pts = [(z, choice[i][j]) for i, z in enumerate(zs)]
            if not interpolates_deg_le(q, inv, pts, k):
                return False
        return True
    if exhaustive:
        for choice in itertools.product(*lists):
            if not check(choice):
                return False, True, choice
        return True, True, None
    rng = rng or random.Random(0)
    for _ in range(cap):
        choice = tuple(rng.choice(lz) for lz in lists)
        if not check(choice):
            return False, False, choice
    return True, False, None

def random_stack(q, n, k, rng):
    return [tuple(rng.randrange(q) for _ in range(n)) for _ in range(k + 1)]

def near_code_stack(q, n, k, words, wts, rng):
    stack = []
    for _ in range(k + 1):
        c = list(rng.choice(words))
        wt = rng.choice(wts)
        for i in rng.sample(range(n), wt):
            c[i] = (c[i] + rng.randrange(1, q)) % q
        stack.append(tuple(c))
    return stack

def block_mix_stacks(q, n, k, words, agree_min, rng, count):
    """Rows that are coordinate-blends of two codewords (per-row list size >= 2 at the
    boundary radius), with misaligned blocks across rows."""
    out = []
    idx = list(range(n))
    for _ in range(count):
        stack = []
        for _ in range(k + 1):
            c1, c2 = rng.choice(words), rng.choice(words)
            split = set(rng.sample(idx, agree_min))
            stack.append(tuple(c1[i] if i in split else c2[i] for i in range(n)))
        out.append(stack)
    return out

def run_point(q, n, deg, k, n_random=300, n_near=300, n_block=200, seed=232):
    rng = random.Random(seed)
    inv = make_field(q)
    domain = list(range(n))
    assert n <= q
    s2 = deg * n
    r = isqrt(s2)
    assert r * r == s2, "not a lattice endpoint"
    radius = n - r            # floor(delta*n) = delta*n exactly (lattice)
    agree_min = r             # (1-delta)*n
    thr = (n + 1) * k         # |good| must EXCEED this
    assert thr < q, "threshold unsatisfiable at this point"
    words, polys = codewords(q, n, deg, domain)

    stacks = []
    stacks.append([tuple([0] * n) for _ in range(k + 1)])                 # zero stack
    for _ in range(5):
        stacks.append([rng.choice(words) for _ in range(k + 1)])          # pure codewords
    stacks += [near_code_stack(q, n, k, words, [radius - 1, radius, radius + 1], rng)
               for _ in range(n_near)]
    stacks += block_mix_stacks(q, n, k, words, agree_min, rng, n_block)
    stacks += [random_stack(q, n, k, rng) for _ in range(n_random)]

    t1_viol = 0          # threshold alone, no jointAgreement
    t3_viol = 0          # threshold + extraction holds, no jointAgreement  (refutes bridge)
    t3_nonexhaustive = 0
    fired = 0
    max_card_no_ja = 0
    for stack in stacks:
        g = good_set(q, stack, words, radius)
        card = len(g)
        ja = None
        if card > thr:
            fired += 1
            ja = joint_agreement(q, stack, words, agree_min)
            if not ja:
                t1_viol += 1
                lists = decode_lists(q, stack, words, polys, radius, g)
                ok, exh, _ = extraction_holds(q, inv, deg, k, lists, g, rng=rng)
                if ok:
                    t3_viol += 1
                    if not exh:
                        t3_nonexhaustive += 1
                    print(f"  T3 VIOLATION (exhaustive={exh}): stack={stack}")
        if ja is None and card > max_card_no_ja:
            # only compute jointAgreement when needed for the tightness stat
            ja = joint_agreement(q, stack, words, agree_min)
        if ja is False and card > max_card_no_ja:
            max_card_no_ja = card

    # T4: zero-stack witness spine
    zero = [tuple([0] * n) for _ in range(k + 1)]
    g0 = good_set(q, zero, words, radius)
    t4_good_univ = (len(g0) == q)
    lists0 = decode_lists(q, zero, words, polys, radius, g0)
    t4_unique_zero = all(lz == [tuple([0] * deg)] for lz in lists0)
    t4 = t4_good_univ and t4_unique_zero

    print(f"point q={q} n={n} deg={deg} k={k}: lattice delta*n={radius}, agree_min={r}, "
          f"(n+1)k={thr}; stacks={len(stacks)}, threshold fired on {fired}; "
          f"T1 threshold-alone violations={t1_viol}; T3 bridge violations={t3_viol} "
          f"(non-exhaustive checks among them: {t3_nonexhaustive}); "
          f"max |good| without jointAgreement = {max_card_no_ja} (vs threshold {thr}); "
          f"T4 zero-stack witness: good=univ {t4_good_univ}, forced P=0 {t4_unique_zero}")
    return t3_viol == 0 and t4

def main():
    ok = True
    # 4 lattice endpoints: deg*n a perfect square, q > (n+1)k, varying q (incl. larger), n, deg, k
    ok &= run_point(q=11, n=8, deg=2, k=1)
    ok &= run_point(q=17, n=8, deg=2, k=1)
    ok &= run_point(q=11, n=9, deg=1, k=1)
    ok &= run_point(q=29, n=8, deg=2, k=2, n_random=150, n_near=150, n_block=100)
    print("RESULT:", "OK (no bridge violation; witness spine holds at all points)" if ok
          else "VIOLATION FOUND")
    sys.exit(0 if ok else 1)

if __name__ == "__main__":
    main()
