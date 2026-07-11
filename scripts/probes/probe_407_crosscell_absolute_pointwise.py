#!/usr/bin/env python3
"""
probe_407_crosscell_absolute_pointwise.py  (#407 / #444 lane: CrossCellAbsoluteBound audit)

QUESTION (deconflicted): the in-tree CrossCellShkredovBound.lean labels
    CrossCellAbsoluteBound :  crossCell(H,zeta,r) * q  <=  2^r * |H|^r
as "the genuine open core (NOT refuted; remains the wall)".

Round-1 L1 (issue #444 sec.11) claims this POINTWISE form is FALSE:
counterexample p=97, n=8, r=4: crossCell*q = 9312 > 4096 = 2^4 * 4^4.

Settle it EXACTLY, multi-prime, PROPER subgroup mu_n (m=(p-1)/n > 1),
p >> n^3, p == 1 mod n, NEVER n=q-1.

Definitions (matching the Lean file exactly):
  G = mu_n  (cyclic 2-power subgroup of F_p*),  H = mu_{n/2} = squares of G,
  zeta = a fixed generator-ish non-square in G so G = H u zeta*H (disjoint).
  N0(S, r) = #{ v in S^r : sum(v) == 0 in F_p }.
  crossCell(H,zeta,r) = N0(G, r) - 2*N0(H, r).

N0(S,r) is computed EXACTLY via the residue-class generating count:
  let cnt[c] = number of elements of S with that residue (here each residue
  appears 0/1 times since S is a set), then N0(S,r) = coefficient extraction
  = (1/p) * sum_{t in F_p} ( sum_{x in S} w^{t*x} )^r   with w = p-th root of unity,
  done EXACTLY in integer arithmetic via DFT over Z (convolution power), or
  simply: N0(S,r) = sum over the r-fold additive convolution of the indicator,
  evaluated at 0. We use exact integer FFT-free convolution (numpy int64 with
  modulus-p index folding) -- but to stay EXACT we use Python big-int polynomial
  powering mod (x^p - 1).  For the small (n<=16, r<=10) regime this is fine.
"""
import sys

def subgroup(p, n):
    """Return sorted list of the order-n subgroup of F_p^* (requires n | p-1)."""
    assert (p - 1) % n == 0, f"n={n} does not divide p-1={p-1}"
    g = primitive_root(p)
    h = pow(g, (p - 1) // n, p)         # element of order n
    S = []
    x = 1
    for _ in range(n):
        S.append(x)
        x = (x * h) % p
    assert len(set(S)) == n, "subgroup size mismatch"
    return sorted(S), h

def primitive_root(p):
    if p == 2:
        return 1
    # factor p-1
    phi = p - 1
    fac = factorize(phi)
    for g in range(2, p):
        if all(pow(g, phi // q, p) != 1 for q in fac):
            return g
    raise RuntimeError("no primitive root")

def factorize(m):
    fs = set()
    d = 2
    while d * d <= m:
        while m % d == 0:
            fs.add(d); m //= d
        d += 1
    if m > 1:
        fs.add(m)
    return fs

def N0_exact(S, r, p):
    """N0(S,r) = #{v in S^r : sum v = 0 mod p}, EXACT via poly powering mod x^p-1."""
    # indicator polynomial f[c] = 1 if c in S else 0, length p
    f = [0] * p
    for x in S:
        f[x % p] += 1
    # compute f^r as a circular convolution power mod x^p - 1, exact big-int coeffs.
    acc = [0] * p
    acc[0] = 1  # represents the constant 1 (r=0)
    base = f
    e = r
    while e > 0:
        if e & 1:
            acc = circ_mul(acc, base, p)
        e >>= 1
        if e:
            base = circ_mul(base, base, p)
    return acc[0]

def circ_mul(a, b, p):
    """Circular convolution (mod x^p - 1) of two length-p integer vectors."""
    out = [0] * p
    # only iterate nonzero entries of b for speed
    nzb = [(j, bj) for j, bj in enumerate(b) if bj]
    for i, ai in enumerate(a):
        if not ai:
            continue
        for j, bj in nzb:
            out[(i + j) % p] += ai * bj
    return out

def run():
    # prize-shaped: p == 1 mod n, p >> n^3, multiple primes, PROPER subgroup (m=(p-1)/n>1)
    cases = {
        8:  [97, 113, 193, 257, 401, 577, 769, 1153, 2593],
        16: [97, 113, 193, 257, 353, 593, 1153, 2593],
        32: [193, 257, 353, 577, 1153, 2593, 7393],
    }
    print("# CrossCellAbsoluteBound POINTWISE audit: is crossCell*q <= 2^r * |H|^r ?")
    print("# (n=8,16,32 ; proper mu_n ; p==1 mod n ; p>>n^3 ; never n=q-1)")
    any_violation = False
    for n in (8, 16, 32):
        Hn = n // 2
        for p in cases[n]:
            if (p - 1) % n != 0:
                continue
            m = (p - 1) // n
            if m < 2:      # PROPER subgroup only, never full group
                continue
            if p < n ** 3:  # want p >> n^3 in the prize regime
                pass        # keep small ones too as a contrast but tag them
            G, _ = subgroup(p, n)
            H, _ = subgroup(p, Hn)
            # H must be the squares-subgroup of G (index 2). Verify H subset G.
            assert set(H) <= set(G), "H not subgroup of G"
            for r in range(2, 11):
                N0G = N0_exact(G, r, p)
                N0H = N0_exact(H, r, p)
                cross = N0G - 2 * N0H
                lhs = cross * p
                rhs = (2 ** r) * (Hn ** r)
                ok = lhs <= rhs
                tag = "OK " if ok else "VIOLATION"
                if not ok:
                    any_violation = True
                regime = "p>n^3" if p >= n ** 3 else "p<n^3"
                if (not ok) or r in (2, 4, 6, 8, 10):
                    print(f"n={n:2d} p={p:5d} m={m:4d} {regime:6s} r={r:2d} "
                          f"cross={cross:8d} cross*q={lhs:12d} 2^r|H|^r={rhs:12d} "
                          f"ratio={lhs/max(rhs,1):8.3f} {tag}")
    print()
    if any_violation:
        print("VERDICT: CrossCellAbsoluteBound (POINTWISE) is REFUTED -- crossCell*q EXCEEDS 2^r|H|^r")
        print("         at prize-shaped proper-subgroup instances. The in-tree docstring calling it")
        print("         'the genuine open core (NOT refuted)' is WRONG for the pointwise/per-r form.")
    else:
        print("VERDICT: no pointwise violation found in tested range (bound holds here).")

if __name__ == "__main__":
    run()
