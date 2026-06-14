#!/usr/bin/env python3
"""Ground-truth brute-force engine for the agreement-spectrum third-moment tensor M3.

Issue #334 moments lane, probe protocol step 1 (see HYPOTHESES-M3.md next to this file).

Setting (exact integer arithmetic, stdlib only):
  q an odd prime; domain D = n distinct nonzero elements of F_q;
  code C = all univariate polynomials over F_q of degree < k (q^k of them, incl. 0),
  as evaluation vectors on D.
  For a received word u : D -> F_q the agreement spectrum is
      a_j(u) = #{p in C : p(x) = u(x) for exactly j of the n points x in D}.
  Targets:
      M1[j]            = sum_u a_j(u)
      M3[j1][j2][j3]   = sum_u a_{j1}(u) * a_{j2}(u) * a_{j3}(u)
  with the sum over ALL q^n received words u.

Algorithm (deliberately simple and obviously-correct; tiny scales only):
  precompute all q^k codeword evaluation tuples; enumerate all q^n received words;
  for each u histogram the agreement counts (a-vector), then add the outer cube of
  the a-vector into M3 (iterating only over the histogram's nonzero support).

Internal asserts (verified facts from prior work, O120/O122):
  * sum_j a_j(u) == q^k for every u;
  * M1[j] == q^k * C(n,j) * (q-1)^(n-j);
  * sum_{j3} M3[j1][j2][j3] == q^k * M2[j1][j2]   (M2 accumulated internally);
  * sum_{j2,j3} M3[j1][j2][j3] == q^(2k) * M1[j1];
  * grand totals sum_j M1[j] == q^(n+k), sum M3 == q^(n+3k);
  * S3 symmetry of the emitted M3 tensor.

CLI:
  python3 probe_agreement_m3_bruteforce.py --q 5 --k 2 --domain 1,2,3,4 [--json-out PATH]
  --domain subgroup:N means the order-N multiplicative subgroup of F_q* (N | q-1),
  computed via a primitive root.

Output (stdout, and --json-out PATH if given) — schema shared with the decomposition
engine so the two can be diffed byte-for-byte:
  {"q":int,"n":int,"k":int,"domain":[sorted ints],"M1":{"j":count,...},
   "M3":{"j1,j2,j3":count,...}}    (M3 keys only for nonzero entries)
"""

import argparse
import itertools
import json
import math
import sys
from operator import eq


def is_prime(m: int) -> bool:
    if m < 2:
        return False
    if m % 2 == 0:
        return m == 2
    f = 3
    while f * f <= m:
        if m % f == 0:
            return False
        f += 2
    return True


def prime_factors(m: int) -> set:
    fs = set()
    d = 2
    while d * d <= m:
        while m % d == 0:
            fs.add(d)
            m //= d
        d += 1
    if m > 1:
        fs.add(m)
    return fs


def primitive_root(q: int) -> int:
    """Smallest primitive root of the prime q (trial test against q-1's prime factors)."""
    fs = prime_factors(q - 1)
    for g in range(2, q):
        if all(pow(g, (q - 1) // p, q) != 1 for p in fs):
            return g
    raise ValueError(f"no primitive root found for q={q} (q not prime?)")


def parse_domain(spec: str, q: int) -> list:
    """Parse --domain: either 'subgroup:N' (order-N subgroup of F_q*) or a comma list."""
    if spec.startswith("subgroup:"):
        N = int(spec.split(":", 1)[1])
        if N <= 0 or (q - 1) % N != 0:
            raise SystemExit(f"error: subgroup order N={N} must satisfy N | q-1 = {q - 1}")
        g = primitive_root(q)
        h = pow(g, (q - 1) // N, q)  # generator of the order-N subgroup
        dom, e = [], 1
        for _ in range(N):
            dom.append(e)
            e = (e * h) % q
        if len(set(dom)) != N:
            raise SystemExit(f"error: subgroup construction yielded repeats (N={N}, q={q})")
        return sorted(dom)
    vals = [int(t) % q for t in spec.split(",") if t.strip() != ""]
    if not vals:
        raise SystemExit("error: empty domain")
    if any(v == 0 for v in vals):
        raise SystemExit("error: domain elements must be nonzero in F_q")
    if len(set(vals)) != len(vals):
        raise SystemExit("error: domain elements must be distinct mod q")
    return sorted(vals)


def compute_moments(q: int, k: int, domain: list):
    """Brute-force M1 (list), M2 (matrix, internal), M3 (dict keyed by (j1,j2,j3))."""
    n = len(domain)
    qk = q ** k

    # Precompute every codeword's evaluation tuple on the domain (q^k of them, incl. 0).
    pows = [[pow(x, e, q) for e in range(k)] for x in domain]
    codewords = [
        tuple(sum(coeffs[e] * pows[i][e] for e in range(k)) % q for i in range(n))
        for coeffs in itertools.product(range(q), repeat=k)
    ]
    assert len(codewords) == qk

    M1 = [0] * (n + 1)
    M2 = [[0] * (n + 1) for _ in range(n + 1)]
    M3 = {}

    for u in itertools.product(range(q), repeat=n):
        # Agreement histogram a_j(u). sum(map(eq, cw, u)) counts coordinates where
        # the codeword tuple equals u (booleans summed exactly) — the tight inner loop.
        hist = [0] * (n + 1)
        for cw in codewords:
            hist[sum(map(eq, cw, u))] += 1
        assert sum(hist) == qk, f"sum_j a_j(u) != q^k for u={u}"

        support = [(j, aj) for j, aj in enumerate(hist) if aj]
        for j, aj in support:
            M1[j] += aj
        for j1, a1 in support:
            for j2, a2 in support:
                a12 = a1 * a2
                M2[j1][j2] += a12
                for j3, a3 in support:
                    key = (j1, j2, j3)
                    M3[key] = M3.get(key, 0) + a12 * a3

    return M1, M2, M3


def run_internal_asserts(q: int, k: int, n: int, M1, M2, M3) -> list:
    """Closed-form and marginal identities; returns human-readable check descriptions."""
    qk = q ** k
    checks = []

    # M1 closed form: q^k * C(n,j) * (q-1)^(n-j).
    for j in range(n + 1):
        expect = qk * math.comb(n, j) * (q - 1) ** (n - j)
        assert M1[j] == expect, f"M1[{j}]={M1[j]} != closed form {expect}"
    checks.append("M1[j] == q^k * C(n,j) * (q-1)^(n-j) for all j")

    assert sum(M1) == q ** (n + k), "sum_j M1[j] != q^(n+k)"
    checks.append("sum_j M1[j] == q^(n+k)")

    # Marginal: sum_{j3} M3 == q^k * M2 (M2 accumulated independently in the same pass).
    for j1 in range(n + 1):
        for j2 in range(n + 1):
            s = sum(M3.get((j1, j2, j3), 0) for j3 in range(n + 1))
            assert s == qk * M2[j1][j2], f"sum_j3 M3[{j1}][{j2}][.] != q^k*M2"
    checks.append("sum_j3 M3[j1][j2][j3] == q^k * M2[j1][j2] for all (j1,j2)")

    # Marginal: sum_{j2,j3} M3 == q^(2k) * M1.
    for j1 in range(n + 1):
        s = sum(v for (a, _, _), v in M3.items() if a == j1)
        assert s == qk * qk * M1[j1], f"sum_j2j3 M3[{j1}][.][.] != q^(2k)*M1"
    checks.append("sum_{j2,j3} M3[j1][j2][j3] == q^(2k) * M1[j1] for all j1")

    assert sum(M3.values()) == q ** (n + 3 * k), "total M3 mass != q^(n+3k)"
    checks.append("sum over all (j1,j2,j3) of M3 == q^(n+3k)")

    for (j1, j2, j3), v in M3.items():
        assert M3.get((j2, j1, j3), 0) == v and M3.get((j1, j3, j2), 0) == v, \
            f"M3 not S3-symmetric at {(j1, j2, j3)}"
    checks.append("M3 tensor is S3-symmetric")

    return checks


def main() -> int:
    ap = argparse.ArgumentParser(
        description="Brute-force ground truth for agreement-spectrum moments M1 and M3.")
    ap.add_argument("--q", type=int, required=True, help="odd prime field size")
    ap.add_argument("--k", type=int, required=True, help="degree bound (code = deg < k)")
    ap.add_argument("--domain", type=str, required=True,
                    help="comma list of distinct nonzero elements, or subgroup:N (N | q-1)")
    ap.add_argument("--json-out", type=str, default=None,
                    help="also write the JSON result to this path")
    args = ap.parse_args()

    q, k = args.q, args.k
    if not is_prime(q) or q == 2:
        raise SystemExit(f"error: q={q} must be an odd prime")
    if k < 1:
        raise SystemExit(f"error: k={k} must be >= 1")

    domain = parse_domain(args.domain, q)
    n = len(domain)

    M1, M2, M3 = compute_moments(q, k, domain)
    checks = run_internal_asserts(q, k, n, M1, M2, M3)
    for c in checks:
        print(f"[assert ok] {c}", file=sys.stderr)

    result = {
        "q": q,
        "n": n,
        "k": k,
        "domain": domain,
        "M1": {str(j): M1[j] for j in range(n + 1)},
        "M3": {f"{j1},{j2},{j3}": M3[(j1, j2, j3)]
               for (j1, j2, j3) in sorted(M3)},
    }
    blob = json.dumps(result, separators=(",", ":"))
    print(blob)
    if args.json_out:
        with open(args.json_out, "w") as fh:
            fh.write(blob + "\n")
    return 0


if __name__ == "__main__":
    sys.exit(main())
