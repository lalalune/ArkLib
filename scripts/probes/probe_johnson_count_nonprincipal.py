#!/usr/bin/env python3
"""
PROBE (#444): the Johnson-scale frequency COUNT bound re-grounded on the SATISFIABLE
nonprincipal Wick input.

Claim to be formalized:
  Let q=|F|, n=|G|, eta_b = sum_{x in mu_n} psi(b x), M=max_{b!=0}|eta_b|.
  Johnson-scale set  S_r := { b : q <= |eta_b|^2 }.
  IF  n^2 < q   (prize regime beta>2: DC term |eta_0|^2 = n^2 is BELOW Johnson scale q),
  THEN every b in S_r is NONPRINCIPAL (b != 0), so
      #S_r * q^{r-1}  <=  sum_{b != 0} |eta_b|^{2r}.
  Under NonprincipalWickBound  ( sum_{b!=0}|eta_b|^{2r} <= q*(2r-1)!!*n^r ):
      #S_r * q^{r-1}  <=  q*(2r-1)!!*n^r.

This re-grounds card_johnson_scale_frequencies_mul_le_wick (which consumes the FULL,
prize-UNSATISFIABLE GaussianEnergyBound E_r <= (2r-1)!!*n^r) onto the prize-SATISFIABLE
nonprincipal hypothesis. We verify (a) 0 is never Johnson-scale when n^2<q, (b) the count
inequality holds exactly, across proper thin subgroups mu_n in prize-shaped primes.
"""
import cmath, math

def doublefact(m):
    # (2r-1)!! ; for m = 2r-1
    r = 1
    k = m
    while k > 0:
        r *= k
        k -= 2
    return r

def eta(p, n, g, b):
    # g a generator of mu_n (element of order n in F_p^*); coset reps not needed:
    # eta_b = sum over x in mu_n of e_p(b*x)
    s = 0j
    x = 1
    for _ in range(n):
        s += cmath.exp(2j*math.pi*(b*x % p)/p)
        x = (x*g) % p
    return s

def find_subgroup_gen(p, n):
    # find element of order exactly n in F_p^* (n | p-1)
    assert (p-1) % n == 0
    cof = (p-1)//n
    # primitive root search
    for a in range(2, p):
        # a^cof has order n iff a is primitive enough; check order
        g = pow(a, cof, p)
        if g == 1:
            continue
        # verify order divides n and equals n
        ok = True
        x = g
        order = 1
        cur = g
        while cur != 1 and order <= n:
            cur = (cur*g) % p
            order += 1
        if order == n:
            return g
    return None

def test(p, n, rmax=4):
    g = find_subgroup_gen(p, n)
    if g is None:
        return None
    q = p
    betas = math.log(p)/math.log(n)
    # all eta_b, b=1..p-1 ; eta_0 = n
    norms2 = [None]*p
    norms2[0] = float(n*n)
    M2 = 0.0
    for b in range(1, p):
        e = eta(p, n, g, b)
        nb2 = (e*e.conjugate()).real
        norms2[b] = nb2
        if nb2 > M2: M2 = nb2
    results = []
    dc_johnson = (n*n >= q)  # is DC term Johnson-scale?
    for r in range(1, rmax+1):
        S = [b for b in range(p) if norms2[b] >= q]
        S_nonzero = [b for b in S if b != 0]
        zero_in_S = (0 in S)
        cardS = len(S)
        lhs = cardS * (q**(r-1))
        # nonprincipal energy sum_{b!=0} |eta|^{2r}
        npenergy = sum((norms2[b]**r) for b in range(1, p))
        wick = q * doublefact(2*r-1) * (n**r)
        results.append({
            'r': r, 'cardS': cardS, 'zero_in_S': zero_in_S,
            'lhs': lhs, 'npenergy': npenergy, 'wick': wick,
            'count_le_npenergy': lhs <= npenergy + 1e-6,
            'npenergy_le_wick': npenergy <= wick + 1e-6,
            'count_le_wick': lhs <= wick + 1e-6,
        })
    return {'p': p, 'n': n, 'beta': betas, 'n2_lt_q': n*n < q,
            'dc_johnson': dc_johnson, 'M2': M2, 'r': results}

# prize-shaped: n = 2^a thin, q = p ~ n^beta, beta in 3..5, p prime, n | p-1
cases = [
    (8, 0),    # find p ~ 8^4 = 4096
    (16, 0),
    (32, 0),
    (8, 0),
]
# build concrete (p,n) with n|p-1, beta~4
def find_prime(n, beta_target):
    import sympy
    lo = int(n**(beta_target-0.15)); hi = int(n**(beta_target+0.15))
    # search p = k*n+1 prime in [lo,hi]
    k0 = max(1, lo//n)
    for k in range(k0, hi//n+2):
        p = k*n+1
        if p < lo: continue
        if p > hi: break
        if sympy.isprime(p):
            return p
    return None

try:
    import sympy
    have_sympy = True
except Exception:
    have_sympy = False

if have_sympy:
    print("n | beta | n^2<q | DC-Johnson? | r | cardS | 0inS | count<=npE | npE<=wick | count<=wick")
    for (n, beta) in [(8,3.0),(8,4.0),(8,5.0),(16,3.0),(16,4.0),(32,3.0),(32,4.0),(64,3.0)]:
        if True:
            p = find_prime(n, beta)
            if p is None:
                print(f"n={n} beta~{beta}: no prime"); continue
            res = test(p, n, rmax=4)
            if res is None:
                print(f"n={n} p={p}: no subgroup gen"); continue
            for row in res['r']:
                print(f"{n} | {res['beta']:.2f} | {res['n2_lt_q']} | {res['dc_johnson']} | "
                      f"{row['r']} | {row['cardS']} | {row['zero_in_S']} | "
                      f"{row['count_le_npenergy']} | {row['npenergy_le_wick']} | {row['count_le_wick']}")
else:
    print("sympy not available; install or run manually")
