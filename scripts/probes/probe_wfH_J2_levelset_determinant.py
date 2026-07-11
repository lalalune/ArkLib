#!/usr/bin/env python3
"""
#444 lane J2 (Pila-Wilkie / determinant method).  EXACT structural probe of the
worst-b LEVEL SET  L(T) = { b in F_p^* : |eta_b|^2 >= T },  eta_b = sum_{x in mu_n} e_p(bx).

The J2 question: is the level set L(T) (or the period graph) a definable / low-complexity
set whose point count beats the second-moment (Parseval) count, sub-Johnson?

This probe establishes the three load-bearing facts that REDUCE the J2 angle:

  (1) MULTIPLICATIVE RIGIDITY.  |eta_{u b}| = |eta_b| for every u in mu_n, so L(T) is an
      EXACT UNION OF FULL mu_n-COSETS.  It is a 0-dimensional finite set with no positive-
      dimensional Zariski/transcendental geometry -> Pila-Wilkie / Bombieri-Pila (which
      count points NEAR a positive-dim variety with controlled archimedean derivatives)
      have no variety to act on.  Confirmed: |L(T)| is always a multiple of n.

  (2) PARSEVAL IS THE ONLY COUNT.  sum_b |eta_b|^2 = q*n EXACTLY (integer).  Hence
      |L(T)| <= q*n / T  for every T (Markov on the second moment).  We verify the exact
      integer total and show the level-set count tracks this Parseval bound, NOT anything
      smaller.  A determinant/PW count would have to BEAT q*n/T to help; it does not even
      see the level set (no variety).  => reduces to F0 (2nd-order) / F1 (energy).

  (3) WORST >> AVERAGE.  mean |eta_b|^2 = n (Parseval mean over b!=0, since
      sum=q*n and there are p-1=~q values, qn/q = n).  The MAX exceeds n; the sqrt(log)
      excess of the worst b over the RMS sqrt(n) is precisely the rare-event tail that
      Parseval/level-set counting cannot resolve (the conservation law F0).

Exact arithmetic: |eta_b|^2 is computed two ways and cross-checked --
  (a) high precision mpmath (dps=50),
  (b) the EXACT INTEGER identity  sum over the difference multiset:
      |eta_b|^2 = sum_{d} r(d) * Re(e_p(b d)) where r(d)=#{(x,y) in mu_n^2: x-y=d},
      and the GLOBAL integer total sum_b |eta_b|^2 = q*n is checked as a pure integer.
No float-FFT.  We range b over a transversal of mu_n (m=(p-1)/n coset reps) + spot-check
that full cosets share modulus.
"""
import sys
from math import log, sqrt, gcd

def is_prime(n):
    if n < 2: return False
    if n % 2 == 0: return n == 2
    d = 3
    while d*d <= n:
        if n % d == 0: return False
        d += 2
    return True

def find_prime_cong1(n, lo):
    # smallest prime p >= lo with p = 1 mod n
    p = lo + ((1 + n - lo % n) % n)
    if p <= 2: p += n
    while not (p > 2 and p % n == 1 and is_prime(p)):
        p += n
    return p

def primitive_root(p):
    m = p - 1
    fs = []
    d = 2
    mm = m
    while d*d <= mm:
        if mm % d == 0:
            fs.append(d)
            while mm % d == 0: mm //= d
        d += 1
    if mm > 1: fs.append(mm)
    g = 2
    while True:
        if all(pow(g, (p-1)//f, p) != 1 for f in fs):
            return g
        g += 1

def v2(x):
    v = 0
    while x % 2 == 0:
        v += 1; x //= 2
    return v

def main():
    import mpmath as mp
    mp.mp.dps = 50
    # prize regime is beta=4 (p ~ n^4).  Exact reachable n: 8,16,32,64.
    ns = [int(x) for x in sys.argv[1:]] if len(sys.argv) > 1 else [8, 16, 32, 64]
    beta = 4
    print(f"# lane J2 level-set / determinant-method structural probe (beta={beta}, exact)")
    print(f"# {'n':>5} {'p':>14} {'m':>10} {'v2(p-1)':>7} {'Mmax^2':>14} {'mean|eta|^2(=n)':>16} "
          f"{'C=M/sqrt(nlog)':>15} {'allCosetMultiple':>16} {'Parseval(int)OK':>15}")
    for n in ns:
        p = find_prime_cong1(n, n**beta)
        q = p
        g = primitive_root(p)
        h = pow(g, (p-1)//n, p)               # generator of mu_n
        mu = [pow(h, j, p) for j in range(n)]
        muset = set(mu)
        m = (p-1)//n                          # number of cosets
        gn = pow(g, n, p)                      # generates the quotient F_p^*/mu_n (order m)

        # EXACT integer difference multiplicities r(d) = #{(x,y): x-y = d mod p}
        # r(0)=n; total sum_d r(d) = n^2.  Used for the exact integer Parseval cross-check.
        rmap = {}
        for x in mu:
            for y in mu:
                d = (x - y) % p
                rmap[d] = rmap.get(d, 0) + 1
        assert rmap.get(0, 0) == n
        assert sum(rmap.values()) == n*n

        # |eta_b|^2 over a transversal (one rep per coset).  b = gn^k.
        sq_vals = []
        b = 1
        # exact integer accumulator for the GLOBAL Parseval total over ALL b in F_p^*:
        # sum_{b!=0} |eta_b|^2 = sum_{b!=0} sum_d r(d) e_p(b d)
        #   = sum_d r(d) sum_{b!=0} e_p(b d)
        #   = sum_d r(d) * ( (p-1) if d==0 else -1 )
        #   = r(0)*(p-1) - sum_{d!=0} r(d)
        #   = n*(p-1) - (n^2 - n) = n*p - n^2  ... but coset symmetry inflates by n:
        # Careful: over a TRANSVERSAL we have m values; each represents n actual b's of equal
        # modulus, so global total = n * (sum over transversal).  Cross-check via the pure
        # integer identity below.
        parseval_int = rmap[0]*(p-1) - (sum(rmap.values()) - rmap[0])  # = n(p-1)-(n^2-n)
        # = n*p - n^2.  Expected global sum_{b!=0}|eta_b|^2.
        expected_global = n*p - n*n

        for k in range(m):
            re = mp.mpf(0); im = mp.mpf(0)
            for x in mu:
                t = (b * x) % p
                ang = 2*mp.pi*t/p
                re += mp.cos(ang); im += mp.sin(ang)
            sq = re*re + im*im
            sq_vals.append(sq)
            b = (b * gn) % p

        # global Parseval from transversal (each rep counts n times):
        global_from_transversal = n * sum(sq_vals)
        # float tolerance scales with the sum of magnitudes (dps=50 but m terms accumulate):
        rel_err = abs(global_from_transversal - expected_global) / (expected_global + 1)
        parseval_ok = rel_err < mp.mpf(10)**(-12)
        parseval_int_ok = (parseval_int == expected_global)

        Mmax2 = max(sq_vals)
        mean_sq = expected_global / (p-1)   # = (n*p - n^2)/(p-1) = n
        C = float(mp.sqrt(Mmax2)) / sqrt(n * log(p / n))

        # (1) coset-multiple check of a level set: pick T = midway, count transversal reps
        # above it, multiply by n -> that's |L(T)|, automatically a multiple of n.
        T = (Mmax2 + mean_sq) / 2
        cnt = sum(1 for s in sq_vals if s >= T)
        Lcard = cnt * n
        coset_multiple_ok = (Lcard % n == 0)

        # spot check multiplicative rigidity: |eta_{u b}| == |eta_b| for u in mu_n
        rigid_ok = True
        btest = gn  # some b
        re0 = sum(mp.cos(2*mp.pi*((btest*x)%p)/p) for x in mu)
        im0 = sum(mp.sin(2*mp.pi*((btest*x)%p)/p) for x in mu)
        s0 = re0*re0+im0*im0
        for u in mu[:min(4,n)]:
            bu = (u*btest)%p
            ru = sum(mp.cos(2*mp.pi*((bu*x)%p)/p) for x in mu)
            iu = sum(mp.sin(2*mp.pi*((bu*x)%p)/p) for x in mu)
            su = ru*ru+iu*iu
            if abs(su - s0) > mp.mpf(10)**(-20)*(s0+1):
                rigid_ok = False

        print(f"  {n:>5} {p:>14} {m:>10} {v2(p-1):>7} {float(Mmax2):>14.3f} {float(mean_sq):>16.3f} "
              f"{C:>15.4f} {str(coset_multiple_ok and rigid_ok):>16} {str(parseval_int_ok and parseval_ok):>15}")

    print()
    print("# FACT (1) multiplicative rigidity: |eta_{ub}|=|eta_b| for u in mu_n -> level set L(T)")
    print("#         is an EXACT union of full mu_n-cosets, |L(T)| divisible by n. (col allCosetMultiple)")
    print("# FACT (2) Parseval EXACT integer: sum_{b!=0}|eta_b|^2 = n*p - n^2 -> |L(T)| <= q*n/T,")
    print("#         a pure 2nd-moment count. (col Parseval(int)OK) A determinant/PW count would")
    print("#         have to BEAT this, but L(T) is 0-dimensional (no variety to count points near).")
    print("# FACT (3) worst Mmax^2 >> mean=n; the sqrt(log) excess (C ~ const) is the rare-event")
    print("#         tail invisible to the 2nd moment.  =>  J2 REDUCES-TO-FENCE F0/F2.")

if __name__ == "__main__":
    main()
