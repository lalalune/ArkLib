#!/usr/bin/env python3
"""
Issue #232 / O67 follow-up — falsify-first probe for the CRT DOUBLE-SLICE route
to the de Bruijn two-prime base case.

Two claims under attack (exact integer arithmetic throughout, no floats):

CLAIM 1 (weighted prime-power slice — the engine, generalizing O66 from 0/1
indicators to arbitrary rational weights):
  For n = p^(m+1) and a : range n -> Z,
      sum_e a_e zeta_n^e = 0   <=>   a_(i*p^m + s) is independent of i < p.
  (Vanishing is checked exactly: remainder of sum a_e X^e mod Phi_n over Z.)

CLAIM 2 (CRT fiber-sum invariance — the two-prime double-slice):
  For n = P*Q with P = p^a, Q = q^b coprime, zeta = zeta_n, xi = zeta^Q
  (order P), eta = zeta^P (order Q), every vanishing SUBSET sum S of mu_n has
  q-side fiber sums
      A(c) = sum_{x in S with eta-coordinate c} (xi-part of x)   in Z[xi]
  invariant under mu_q-shifts of c:  A(i*q^(b-1) + s) independent of i < q;
  and symmetrically on the p side.
  Exhaustive at n = 12 (2^12 subsets) and n = 18 (2^18 subsets).

Controls: non-vanishing weight vectors / subsets must (and do) violate the
invariances; counts reported.
"""

from itertools import product

# ---------- exact polynomial arithmetic mod a monic integer polynomial ----------

def polymod(coeffs, mod):
    """Reduce integer coeff list (index = degree) mod monic integer poly `mod`."""
    c = list(coeffs)
    d = len(mod) - 1  # degree of modulus
    while len(c) > d:
        lead = c.pop()
        if lead:
            for k in range(d):
                c[len(c) - d + k] -= lead * mod[k]
    while len(c) < d:
        c.append(0)
    return tuple(c)

# cyclotomic polynomials we need, as integer coeff lists (low -> high, monic last)
PHI = {
    2:  [1, 1],
    3:  [1, 1, 1],
    4:  [1, 0, 1],
    8:  [1, 0, 0, 0, 1],
    9:  [1, 0, 0, 1, 0, 0, 1],
    12: [1, 0, -1, 0, 1],
    18: [1, 0, 0, -1, 0, 0, 1],
}

def root_pow_table(n):
    """Table of zeta_n^e for e < n, reduced mod Phi_n, as tuples."""
    mod = PHI[n]
    return [polymod([0]*e + [1], mod) for e in range(n)]

def vec_add(u, v):
    return tuple(a + b for a, b in zip(u, v))

def is_zero(u):
    return all(a == 0 for a in u)

# ---------- CLAIM 1: weighted prime-power slice <=> vanishing ----------

def claim1(p, m, trials=20000, seed=1):
    import random
    rng = random.Random(seed)
    n = p ** (m + 1)
    q = p ** m
    mod = PHI[n]
    tbl = root_pow_table(n)
    deg = len(mod) - 1

    def vanishes(a):
        acc = tuple([0] * deg)
        for e in range(n):
            if a[e]:
                acc = vec_add(acc, tuple(a[e] * x for x in tbl[e]))
        return is_zero(acc)

    def slices_equal(a):
        return all(a[i * q + s] == a[s] for i in range(p) for s in range(q))

    mismatches = 0
    pos = neg = 0
    # random vectors (mostly non-vanishing): test equivalence both ways
    for _ in range(trials):
        a = [rng.randint(-5, 5) for _ in range(n)]
        v, sl = vanishes(a), slices_equal(a)
        if v != sl:
            mismatches += 1
        if v:
            pos += 1
        else:
            neg += 1
    # explicit kernel samples: a = Phi_n * R with deg R < q  (must vanish + slice)
    kernel_bad = 0
    for _ in range(trials // 10):
        R = [rng.randint(-5, 5) for _ in range(q)]
        a = [0] * n
        for i, ci in enumerate(mod):
            for j, rj in enumerate(R):
                a[i + j] += ci * rj
        if not (vanishes(a) and slices_equal(a)):
            kernel_bad += 1
        pos += 1
    return mismatches, kernel_bad, pos, neg

# ---------- CLAIM 2: CRT fiber-sum invariance for vanishing subset sums ----------

def claim2(n, P, Q, qp, qq):
    """n = P*Q coprime. qp, qq = the primes (P = qp^a, Q = qq^b).
    Exhaustive over all subsets of mu_n. Returns
    (num_vanishing, violations_on_vanishing, invariant_nonvanishing_count,
     num_nonvanishing)."""
    mod_n = PHI[n]
    tbl_n = root_pow_table(n)
    deg_n = len(mod_n) - 1

    tbl_P = root_pow_table(P)   # Z[xi]
    tbl_Q = root_pow_table(Q)   # Z[eta]
    degP = len(PHI[P]) - 1
    degQ = len(PHI[Q]) - 1

    # CRT coordinates: zeta^e = xi^j * eta^c with Q*j + P*c == e (mod n)
    Qinv = pow(Q, -1, P)
    Pinv = pow(P, -1, Q)
    jcoord = [ (e * Qinv) % P for e in range(n) ]
    ccoord = [ (e * Pinv) % Q for e in range(n) ]
    # sanity: reconstruction
    for e in range(n):
        assert (Q * jcoord[e] + P * ccoord[e]) % n == e

    stepq = Q // qq   # q^(b-1)
    stepp = P // qp   # p^(a-1)

    def fiber_invariant(I):
        # q-side: A(c) in Z[xi]
        A = [tuple([0] * degP) for _ in range(Q)]
        for e in I:
            A[ccoord[e]] = vec_add(A[ccoord[e]], tbl_P[jcoord[e]])
        for s in range(stepq):
            base = A[s]
            for i in range(1, qq):
                if A[i * stepq + s] != base:
                    return False
        # p-side: B(j) in Z[eta]
        B = [tuple([0] * degQ) for _ in range(P)]
        for e in I:
            B[jcoord[e]] = vec_add(B[jcoord[e]], tbl_Q[ccoord[e]])
        for s in range(stepp):
            base = B[s]
            for i in range(1, qp):
                if B[i * stepp + s] != base:
                    return False
        return True

    num_van = viol = inv_nonvan = num_nonvan = 0
    for mask in range(1 << n):
        I = [e for e in range(n) if (mask >> e) & 1]
        acc = tuple([0] * deg_n)
        for e in I:
            acc = vec_add(acc, tbl_n[e])
        if is_zero(acc):
            num_van += 1
            if not fiber_invariant(I):
                viol += 1
        else:
            num_nonvan += 1
            if fiber_invariant(I):
                inv_nonvan += 1
    return num_van, viol, inv_nonvan, num_nonvan


def main():
    print("== CLAIM 1: weighted slice <=> vanishing, prime powers ==")
    for (p, m) in [(2, 2), (3, 1)]:
        mism, kbad, pos, neg = claim1(p, m)
        n = p ** (m + 1)
        print(f"  p={p} m={m} (n={n}): equivalence mismatches={mism}, "
              f"kernel-sample failures={kbad}, vanishing seen={pos}, non-vanishing={neg}")
        assert mism == 0 and kbad == 0 and pos > 0 and neg > 0

    print("== CLAIM 2: CRT fiber-sum invariance on vanishing subset sums ==")
    for (n, P, Q, qp, qq) in [(12, 4, 3, 2, 3), (18, 2, 9, 2, 3)]:
        nv, viol, invnv, nnv = claim2(n, P, Q, qp, qq)
        print(f"  n={n} (P={P}, Q={Q}): vanishing subsets={nv}, violations={viol}, "
              f"non-vanishing total={nnv}, non-vanishing-but-invariant={invnv}")
        assert viol == 0 and nv > 1 and nnv > 0
        # control: invariance must FAIL somewhere on non-vanishing sets
        assert invnv < nnv

    print("ALL CHECKS PASS")


if __name__ == "__main__":
    main()
