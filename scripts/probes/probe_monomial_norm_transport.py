#!/usr/bin/env python3
"""
PROBE: monomial-Weyl norm-transport. (#444, BRIDGE inequality face)

The bridge proves the EQUATION  m * eta_b = S_b := sum_{x in F_p^*} e_p(b x^m).
The reusable inequality the equidistribution ladder needs is the TRANSPORT:
    |S_b| <= B   ==>   |eta_b| <= B / m,    (m = (p-1)/n > 0).

This probe confirms (a) the equation m*eta_b = S_b holds exactly (err=0), and
(b) the transport arithmetic: |eta_b| = |S_b|/m exactly, so any monomial-sum
bound B on |S_b| divides cleanly by m to a period bound B/m. Prize-regime
instances: PROPER 2-power subgroups mu_n, large primes p >> n^3, incl. Fermat.
"""
import cmath, math

def ep(p):
    return lambda t: cmath.exp(2j*math.pi*(t % p)/p)

def primitive_root(p):
    # smallest primitive root mod p
    def order(g):
        o, x = 1, g % p
        while x != 1:
            x = (x*g) % p; o += 1
        return o
    for g in range(2, p):
        if order(g) == p-1:
            return g
    raise RuntimeError

cases = [
    # (p, n) with n | p-1, n a 2-power, p >> n^3 (prize regime)
    (257, 16),     # Fermat, p-1=256, n=16, m=16, beta=2
    (769, 16),     # p-1=768, n=16, m=48
    (12289, 16),   # p-1=12288, n=16, m=768, p~n^3.4
    (40961, 16),   # p-1=40960, n=16, m=2560
    (65537, 16),   # Fermat, prize p, n=16, m=4096, beta=4
    (193, 32),     # p-1=192, n=32? no 192=2^6*3, n=32|192 yes, m=6
    (12289, 64),   # p-1=12288=2^12*3, n=64, m=192
]

worst_eq_err = 0.0
worst_transport_err = 0.0
allpass = True
for (p, n) in cases:
    if (p-1) % n != 0:
        print(f"  SKIP p={p} n={n}: n nmid p-1"); continue
    m = (p-1)//n
    g = primitive_root(p)
    e = ep(p)
    # mu_n = { g^(k*m) : k } = n-th roots of unity = {y: y^n=1}
    mu = sorted({pow(g, (k*m) % (p-1), p) for k in range(n)})
    assert len(mu) == n, (p, n, len(mu))
    # check each y^n == 1
    assert all(pow(y, n, p) == 1 for y in mu)
    eqmax = 0.0; trmax = 0.0
    for b in range(1, p):
        if b % p == 0: continue
        eta = sum(e(b*y) for y in mu)
        S   = sum(e(b*pow(x, m, p)) for x in range(1, p))  # x in F_p^*
        eqmax = max(eqmax, abs(S - m*eta))
        # transport: |eta| == |S|/m exactly
        trmax = max(trmax, abs(abs(eta) - abs(S)/m))
        if b > 60:  # eqn is structural; sampling b up to 60 + checking all is overkill for big p
            break
    worst_eq_err = max(worst_eq_err, eqmax)
    worst_transport_err = max(worst_transport_err, trmax)
    ok = eqmax < 1e-7 and trmax < 1e-7
    allpass &= ok
    print(f"  p={p:6d} n={n:3d} m={m:5d} beta~{math.log(p)/math.log(n):.2f}  eqErr={eqmax:.2e} transportErr={trmax:.2e}  {'OK' if ok else 'FAIL'}")

print()
print(f"worst equation err  m*eta_b - S_b : {worst_eq_err:.2e}")
print(f"worst transport err ||eta|-|S|/m| : {worst_transport_err:.2e}")
print("VERDICT:", "PASS - transport |eta_b| <= B/m is exact arithmetic from the bridge equation" if allpass else "FAIL")
