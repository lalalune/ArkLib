#!/usr/bin/env python3
"""
#407 CONNECTION C3 — sumset-size <-> energy duality; does the q-INDEPENDENT count
UPPER-bound the energy / sup-norm?

SETUP (mu_n, n=2^mu, p=q prime, p == 1 mod n; r-fold "additive convolution").
For an r-fold sum c of elements of mu_n over F_p, let
    a(c) = #{ (x_1,...,x_r) in mu_n^r : x_1 + ... + x_r = c (mod p) }   (multiplicity).
Then:
  - N_r := #{ distinct c : a(c) > 0 } = | r-fold sumset of mu_n over F_p | = "the count".
  - sum_c a(c) = n^r   (total mass).
  - E_r := sum_c a(c)^2 = additive energy = #{(x,y) in mu_n^{2r} : sum x = sum y (mod p)}.
  - M := max_{b != 0} |eta_b|,  eta_b = sum_{x in mu_n} e_p(b x).   (sup-norm)

EXACT FOURIER IDENTITY (the spine of #407):
    E_r = (1/p) * sum_{b=0}^{p-1} |eta_b|^{2r} = n^{2r}/p + (1/p) sum_{b != 0} |eta_b|^{2r}.
So A_r := E_r - n^{2r}/p = (1/p) sum_{b != 0} |eta_b|^{2r}  (the anomalous energy = 2r-th moment of M).

KNOWN (the useless direction): Cauchy-Schwarz on (a(c))_c supported on N_r values:
    n^{2r} = (sum_c a(c))^2 <= N_r * sum_c a(c)^2 = N_r * E_r
  => E_r >= n^{2r} / N_r   (LOWER bound on energy from the count). USELESS for upper-bounding.

THE TASK (other direction): can N_r (q-independent count) give an UPPER bound on E_r or M?
We test 3 candidate routes numerically:

(a) max-multiplicity route:  E_r = sum_c a(c)^2 <= (max_c a(c)) * sum_c a(c) = max_c a(c) * n^r.
    So  E_r <= a_max * n^r,  and  A_r = E_r - n^{2r}/p <= a_max*n^r - n^{2r}/p.
    DOES THE COUNT BOUND a_max? Test if a_max is controlled by N_r (e.g. a_max <= n^r/N_r * something,
    or a_max q-independent). Note a_max >= n^r/N_r (pigeonhole, average mult). Question: upper bound.

(b) flattening / spread:  if the mass n^r is spread over N_r values, the L^2 (energy) is minimized
    when FLAT (a(c)=n^r/N_r for all), giving E_r = n^{2r}/N_r (= the CS lower bound, tight iff flat).
    The MAXIMUM of E_r given fixed N_r and fixed total mass is achieved by concentrating: it is
    UNBOUNDED by N_r alone (one big atom). So N_r alone canNOT upper-bound E_r unless a_max is bounded.
    => the upper bound EXISTS iff a_max is separately bounded. Test whether a_max is q-independent /
       count-controlled, or whether it grows with q (then no upper bound).

(c) identity linking a_max to the count-lane spurious structure: a_max = max multiplicity = the
    most-popular sum's representation count. The DIAGONAL/trivial part of a_max is n^{r-1}/p-ish?
    Actually the c=0 sum (if reachable) has the antipodal-pairing count. Test exact a_max vs n.

We compute EVERYTHING exactly by enumerating r-fold sums over EXPONENTS (g a primitive n-th root in F_p),
mapping to F_p, and counting. Feasible while n^r <= ~2*10^7.
"""
import sys, itertools
from collections import Counter
from sympy import isprime, primitive_root

def first_prime_1modn(n, lo):
    p = lo - (lo % n) + 1
    if p <= lo: p += n
    while not isprime(p):
        p += n
    return p

def primitive_nth_root(n, p):
    g = primitive_root(p)
    return pow(g, (p - 1)//n, p)  # order n

def analyze(n, p, r, verbose=True):
    """Exact multiplicities a(c) of r-fold sums of mu_n over F_p."""
    w = primitive_nth_root(n, p)
    roots = [pow(w, j, p) for j in range(n)]
    # multiplicity of each F_p value as an r-fold sum
    a = Counter()
    # iterate over multisets? No: ordered tuples give a(c) = #ordered reps. We want a(c) ordered
    # (matches E_r = #ordered pairs). Enumerate ordered r-tuples.
    for tup in itertools.product(range(n), repeat=r):
        s = 0
        for j in tup:
            s = (s + roots[j]) % p
        a[s] += 1
    N_r = len(a)                       # distinct sums = sumset size = the COUNT
    total = sum(a.values())            # = n^r
    E_r = sum(v*v for v in a.values()) # additive energy (ordered)
    a_max = max(a.values())
    a_min = min(a.values())
    avg = total / N_r
    return dict(n=n, p=p, r=r, N_r=N_r, total=total, E_r=E_r, a_max=a_max,
                a_min=a_min, avg=avg, nr=n**r)

def main():
    print("="*100)
    print("C3: does the q-INDEPENDENT sumset count N_r upper-bound the energy E_r / sup-norm M?")
    print("="*100)
    print("Legend: N_r=|sumset|(count), E_r=energy, a_max=max multiplicity, n^r=total mass,")
    print("        CS_lower = n^{2r}/N_r (Cauchy-Schwarz LOWER bnd on E_r), flat would give E_r=CS_lower.")
    print("        ub(a) = a_max*n^r (route-a upper bnd on E_r). diag floor a_max >= n^r/N_r.")
    print()

    # Sweep several n, several primes (to test q-DEPENDENCE), several r.
    cases = []
    for mu in [3,4,5]:
        n = 2**mu
        # several primes == 1 mod n of increasing size to test q-dependence
        primes = []
        lo = n+1
        for _ in range(6):
            pp = first_prime_1modn(n, lo)
            primes.append(pp)
            lo = pp + 1
        # also a couple bigger primes
        for tgt in [n**3, n**4]:
            primes.append(first_prime_1modn(n, tgt))
        for r in [2,3]:
            if n**r > 3_000_000:  # keep enumeration feasible
                continue
            cases.append((n, primes, r))

    for (n, primes, r) in cases:
        print(f"\n### n={n} (mu={n.bit_length()-1}), r={r}, n^r={n**r}")
        print(f"{'p':>10} {'N_r':>8} {'E_r':>10} {'a_max':>7} {'CS_low':>10} {'E_r/CS':>7} "
              f"{'a_max/avg':>9} {'a_max*n^r':>11} {'E_r<=ub?':>8}")
        N_r_vals = []
        a_max_vals = []
        E_r_vals = []
        for p in primes:
            d = analyze(n, p, r)
            CS_low = d['nr']**2 / d['N_r']
            ub_a = d['a_max'] * d['nr']
            print(f"{p:>10} {d['N_r']:>8} {d['E_r']:>10} {d['a_max']:>7} {CS_low:>10.1f} "
                  f"{d['E_r']/CS_low:>7.3f} {d['a_max']/d['avg']:>9.2f} {ub_a:>11} "
                  f"{'OK' if d['E_r']<=ub_a else 'FAIL':>8}")
            N_r_vals.append(d['N_r']); a_max_vals.append(d['a_max']); E_r_vals.append(d['E_r'])
        # q-dependence diagnostics
        print(f"   -> N_r over primes: {N_r_vals}  (saturates to char-0 |sumset|={max(N_r_vals)})")
        print(f"   -> a_max over primes: {a_max_vals}  (q-DEPENDENT? {len(set(a_max_vals))>1})")
        print(f"   -> E_r over primes: {E_r_vals}  (q-DEPENDENT? {len(set(E_r_vals))>1})")

if __name__ == "__main__":
    main()
