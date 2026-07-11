#!/usr/bin/env python3
"""
Door-(iv) probe: proper subgroup-coset splits of a 2-power subgroup stay on the real wall.

For H=<h> of order n=2^a in F_p^*, split H into d cosets of the subgroup <h^d>, where d|n
and d<n.  Since -1=h^(n/2), every proper power-of-two index d<=n/2 divides n/2.  Hence each
coset h^r<h^d> is closed under x -> -x, so every piece

    A_r(b) = sum_{t=0}^{n/d-1} exp(2pi i b h^{r+d t}/p)

is real.  This script verifies the finite object and measures the adversarial coherence

    rho_d(b) = |sum_r A_r(b)| / sum_r |A_r(b)|.

Verdict to test: no proper subgroup-coset partition of a 2-power H escapes the same real-piece
sign degeneracy.  Any genuine door-(iv) phase anti-concentration must use a non-subgroup/non-
negation-stable partition, or the singleton phase set itself.
"""
from __future__ import annotations

import argparse, cmath, math, random
from dataclasses import dataclass


def is_prime(n: int) -> bool:
    if n < 2:
        return False
    small = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37]
    for q in small:
        if n == q:
            return True
        if n % q == 0:
            return False
    d = 41
    while d * d <= n:
        if n % d == 0:
            return False
        d += 2
    return True


def factor(n: int) -> list[int]:
    out: list[int] = []
    d = 2
    while d * d <= n:
        if n % d == 0:
            out.append(d)
            while n % d == 0:
                n //= d
        d += 1 if d == 2 else 2
    if n > 1:
        out.append(n)
    return out


def primitive_root(p: int) -> int:
    fs = factor(p - 1)
    for g in range(2, p):
        if all(pow(g, (p - 1) // q, p) != 1 for q in fs):
            return g
    raise RuntimeError("no primitive root")


def next_prime_1_mod_n_near(n: int, beta: int = 4) -> int:
    target = n ** beta
    k = max(1, (target - 1 + n - 1) // n)
    for radius in range(0, 2_000_000):
        for kk in ((k + radius) if radius else k, k - radius):
            if kk <= 0:
                continue
            p = kk * n + 1
            if is_prime(p):
                return p
    raise RuntimeError(f"no prime found for n={n}")


@dataclass
class Row:
    n: int
    p: int
    d: int
    m: int
    j: int
    b: int
    eta: float
    rho: float
    den: float
    max_imag: float
    pos: int
    neg: int
    q_center: int
    rep_min: int


def candidate_js(total: int, limit: int | None, seed: int, n: int, p: int) -> list[int]:
    if limit is None or limit >= total:
        return list(range(total))
    rng = random.Random(seed + n + p)
    base = set(range(min(total, 4096))) | {total - 1 - i for i in range(min(total, 4096))}
    for t in [total // 8, total // 4, 3 * total // 8, total // 2, 5 * total // 8, 3 * total // 4, 7 * total // 8]:
        for off in range(-128, 129):
            if 0 <= t + off < total:
                base.add(t + off)
    x = 1
    while x < total:
        for off in range(-16, 17):
            if 0 <= x + off < total:
                base.add(x + off)
        x *= 2
    while len(base) < limit:
        base.add(rng.randrange(total))
    return sorted(base)[:limit]


def scan(n: int, p: int, d: int, limit: int | None, seed: int) -> tuple[Row, Row, int]:
    assert n % d == 0 and d < n
    g = primitive_root(p)
    m = (p - 1) // n
    h = pow(g, m, p)
    hd = pow(h, d, p)
    cosets: list[list[int]] = []
    for r in range(d):
        x = pow(h, r, p)
        xs: list[int] = []
        for _ in range(n // d):
            xs.append(x)
            x = (x * hd) % p
        cosets.append(xs)
    js = candidate_js(m, limit, seed, n, p)
    twopi = 2 * math.pi
    best_eta: Row | None = None
    best_rho: Row | None = None
    for j in js:
        b = pow(g, j, p)
        parts: list[complex] = []
        for xs in cosets:
            s = 0j
            for x in xs:
                s += cmath.exp(1j * twopi * ((b * x) % p) / p)
            parts.append(s)
        eta = abs(sum(parts))
        den = sum(abs(z) for z in parts)
        rho = eta / den if den else 0.0
        q = pow(b, n, p)
        row = Row(
            n=n,
            p=p,
            d=d,
            m=m,
            j=j,
            b=b,
            eta=eta,
            rho=rho,
            den=den,
            max_imag=max(abs(z.imag) for z in parts),
            pos=sum(1 for z in parts if z.real >= 0),
            neg=sum(1 for z in parts if z.real <= 0),
            q_center=min(q, p - q),
            rep_min=min(b, p - b),
        )
        if best_eta is None or row.eta > best_eta.eta:
            best_eta = row
        if best_rho is None or (row.rho, row.eta) > (best_rho.rho, best_rho.eta):
            best_rho = row
    assert best_eta is not None and best_rho is not None
    return best_eta, best_rho, len(js)


def fmt(r: Row) -> str:
    return (
        f"d={r.d:<3d} j={r.j:<8d} b={r.b:<11d} |eta|={r.eta:.3f} "
        f"rho={r.rho:.6f} den={r.den:.3f} max|Im piece|={r.max_imag:.2e} "
        f"signs(+/-)={r.pos}/{r.neg} q_center={r.q_center} min(b,p-b)={r.rep_min}"
    )


def proper_power_two_indices(n: int) -> list[int]:
    ds: list[int] = []
    d = 2
    while d < n:
        if n % d == 0:
            ds.append(d)
        d *= 2
    return ds


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--ns", default="16,32,64,128")
    ap.add_argument("--limit-large", type=int, default=100_000)
    ap.add_argument("--full-large", action="store_true")
    ap.add_argument("--seed", type=int, default=444)
    args = ap.parse_args()
    print("Door-(iv) proper coset-split degeneracy probe.")
    print("For n=2^a, every proper subgroup-coset split has d|n/2, so pieces are real.\n")
    for n in [int(s) for s in args.ns.split(",") if s.strip()]:
        p = 65537 if n == 16 else next_prime_1_mod_n_near(n, 4)
        m = (p - 1) // n
        limit = None if (args.full_large or n <= 64) else args.limit_large
        print(f"## n={n} p={p} beta={math.log(p)/math.log(n):.3f} quotient_cosets={m}")
        for d in proper_power_two_indices(n):
            if d > 16 and not args.full_large:
                continue
            best_eta, best_rho, scanned = scan(n, p, d, limit, args.seed)
            print(f"scanned={scanned} index d={d} (d divides n/2: {(n//2) % d == 0})")
            print("  worst |eta|: " + fmt(best_eta))
            print("  best rho : " + fmt(best_rho))
        print()


if __name__ == "__main__":
    main()
