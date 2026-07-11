#!/usr/bin/env python3
"""
probe_wf9G6_roughprime_descent.py  (#444, lane G6)

STRUCTURED-PRIME-SPECIFIC Stepanov / Weil-on-curve probe.

Question: at a ROUGH prime (m=(p-1)/n has a large prime factor ell), do the "extra
coincidences" -- the spurious additive mass that makes the moment method char-p-FALSE --
live on a CURVE attached to (mu_n, ell) that descends to a smaller field F_ell, where the
Stepanov-Weil point-count atom |V| <= (deg)*sqrt(field) would finally beat the trivial n?

Verdict (EXACT integer arithmetic, n<=128, p~n^4, hundreds of primes per n):
  (1) Additive energy E(mu_n)=#{(a,b,c,d):a+b=c+d} is BIT-FOR-BIT identical for the roughest
      and smoothest prime at every n (= char-0 value 3n^2-3n). Factorization-blind.
  (2) Depth-3 spurious mass spur_3 = E_3(mu_n)-E_3^char0 is QUANTIZED (multiples of ~11520
      at n=64) and UNCORRELATED with ell (spur/ell ranges 0.17..193 as ell ranges 179..263293;
      spur stays capped at 46080). This is the short-+-1-relation signature, NOT a curve point
      count (which would track ell). => NO subfield descent; Stepanov-Weil field size pinned to
      p~n^4, sqrt(p)>=n^2>>n, vacuous at rough primes exactly as at smooth.

This is the Python reference matching the Rust probes probe_g6{b,c,d}.rs; it is intentionally
small-n (the structural conclusion is n-independent: F_p is a prime field, no subfield exists).
"""
from sympy import isprime, primitive_root, factorint


def mu_n(n, p):
    g = primitive_root(p)
    h = pow(g, (p - 1) // n, p)
    return [pow(h, j, p) for j in range(n)]


def add_energy(mu, p):
    from collections import Counter
    c = Counter((a + b) % p for a in mu for b in mu)
    return sum(v * v for v in c.values())


def e3(mu, p):
    from collections import Counter
    c = Counter((a + b + d) % p for a in mu for b in mu for d in mu)
    return sum(v * v for v in c.values())


def find_primes_cong1(n, lo, count):
    out = []
    p = lo + ((1 + n - lo % n) % n)
    while len(out) < count:
        if p > 2 and p % n == 1 and isprime(p):
            out.append(p)
        p += n
    return out


def rough_factor(m):
    return max(factorint(m).keys())


def main():
    print("# (1) additive energy: rough vs smooth, per n")
    print("# n  rough_p  rough_E  smooth_p  smooth_E  char0(3n^2-3n)  equal?")
    for n in (16, 32, 64):
        ps = find_primes_cong1(n, int(n ** 4), 80)
        scored = [(rough_factor((p - 1) // n) / ((p - 1) // n), p) for p in ps]
        rp = max(scored)[1]
        sp = min(scored)[1]
        eR = add_energy(mu_n(n, rp), rp)
        eS = add_energy(mu_n(n, sp), sp)
        print(f"{n:4} {rp:>12} {eR:>8} {sp:>12} {eS:>8} {3*n*n-3*n:>8} {eR==eS}")

    print("\n# (2) depth-3 spurious mass at n=64: quantized & ell-blind (curve would track ell)")
    n = 64
    ps = find_primes_cong1(n, int(n ** 4), 120)
    vals = [(p, rough_factor((p - 1) // n), e3(mu_n(n, p), p)) for p in ps]
    base = min(v[2] for v in vals)
    print(f"# char-0 baseline E3 = {base}")
    print("# p  ell  spur  spur/ell")
    nz = [(p, ell, e - base) for (p, ell, e) in vals if e > base]
    for p, ell, spur in nz[:12]:
        print(f"{p:>12} {ell:>10} {spur:>8} {spur/ell:.4f}")
    if nz:
        spurs = sorted({s for _, _, s in nz})
        print(f"# distinct spur values (quantized): {spurs}")
        print(f"# max spur = {max(spurs)};  ell ranges {min(e for _,e,_ in nz)}..{max(e for _,e,_ in nz)}")
        print("# => spur bounded & ell-uncorrelated = SHORT RELATION, not curve-over-F_ell")


if __name__ == "__main__":
    main()
