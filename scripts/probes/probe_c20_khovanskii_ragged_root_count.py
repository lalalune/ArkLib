"""
Probe C20: Khovanskii fewnomial real-analogue + char-faithful complexification.

C20 claims: the ragged (non-coset) mu_n-roots of a (k+2)-nomial are bounded by
Khovanskii's count 2^{C(k+2,2)}(k+2), which is n,p-INDEPENDENT. Hence s* <= core(n/2)+const(n),
giving delta*=1/2 past Johnson for rho<1/4.

THE TEST. Khovanskii bounds POSITIVE REAL roots (a degree-free count). Over a field with
roots of unity, the count of roots of a t-nomial is NOT bounded by any function of t alone:
it is bounded by the DEGREE. We test the literal claim:

   "a single (k+2)-nomial f(X) = X^a + gamma X^b - h(X)  (deg h < k, support size m=k+2)
    has at most 2^{C(m,2)} m  ROOTS in mu_n (genuinely ragged ones)."

Counterexample family (already in-tree as _RThinSqrtNKRefuted, here verified over a PRIZE prime):
   f(X) = (X^m + 1)(X - 1) = X^{m+1} - X^m + X - 1,  k=2, support {0,1,m,m+1}, so t = k+2 = 4.
   Its mu_{2m}-root set = {x : x^m = -1} U {1}, size m+1, GENUINELY RAGGED (coeff at X^1 is nonzero).
   m+1 grows LINEARLY in n=2m, while Khovanskii's bound 2^{C(4,2)}*4 = 2^6 * 4 = 256 is CONSTANT.

So for n large enough (m > 255), the ragged root count EXCEEDS the alleged constant cap.
We verify the roots actually live in mu_{2m} over a proper subgroup of F_p*, p prime, p >> n^3,
n = 2^mu (dyadic), NEVER n = p-1.
"""

import sympy

def find_prime(n, beta=4):
    # want p prime, p ≡ 1 mod n (so mu_n subgroup exists), p >> n^3, n < p^{1/4}
    # take p ~ n^beta, the prize band
    target = n**beta
    # search p = c*n + 1 prime, c chosen so p ~ target and p > n^3
    c = max(target // n, n**2 + 1)
    while True:
        p = c*n + 1
        if p > n**3 and sympy.isprime(p):
            return p
        c += 1

def test(mu, beta=4):
    n = 2**mu              # dyadic domain mu_n, n = 2^mu
    m = n // 2             # k=2 family: f = (X^m+1)(X-1), support {0,1,m,m+1}
    p = find_prime(n, beta)
    assert p % n == 1, "need mu_n subgroup"
    assert p > n**3, "need p >> n^3"
    assert n != p - 1, "NEVER n = p-1"
    # check n < p^{1/4} (prize band, n << sqrt(q))
    band_ok = n**4 < p

    g = sympy.primitive_root(p)
    # generator of mu_n: g^((p-1)/n)
    zeta_n = pow(g, (p-1)//n, p)          # primitive n-th root of unity in F_p
    # mu_n = { zeta_n^j : j }
    mu_n = set(pow(zeta_n, j, p) for j in range(n))
    assert len(mu_n) == n, f"mu_n size {len(mu_n)} != {n}"
    # f(X) = X^{m+1} - X^m + X - 1 ; count its roots inside mu_n
    def f(x):
        return (pow(x, m+1, p) - pow(x, m, p) + x - 1) % p
    roots = sorted(x for x in mu_n if f(x) == 0)
    nroots = len(roots)

    # ragged certificate: the root product Q_S = (X^m+1)(X-1) has nonzero X^1 coeff
    # => NOT a mu_{d'}-coset-union for any d'>1  (factorization rigidity).
    ragged = True   # by construction; coeff(X^1) = +1 != 0

    # Khovanskii constant cap for a t-nomial, t = k+2 = 4 :  2^{C(t,2)} * t
    t = 4
    from math import comb
    khov_cap = (2 ** comb(t, 2)) * t

    print(f"mu={mu:2d} n={n:6d} m={m:6d} p={p}  (p/n^3={p/n**3:.1f}, n<p^1/4:{band_ok})")
    print(f"   ragged mu_n-root count of the (k+2)=4-nomial = {nroots}  (predicted m+1 = {m+1})")
    print(f"   Khovanskii CONSTANT cap 2^C(4,2)*4 = {khov_cap}")
    print(f"   VIOLATION (count > cap)? {nroots > khov_cap}")
    print(f"   genuinely ragged (non-coset)? {ragged}    Johnson sqrt(n*k)=sqrt({n}*2)={ (2*n)**0.5:.2f}")
    print()
    return nroots, khov_cap, m+1

if __name__ == "__main__":
    print("=== C20 PROBE: Khovanskii constant cap vs actual ragged mu_n-root count ===\n")
    # Khovanskii cap for k=2 is 256. We need m+1 > 256, i.e. m >= 256, n = 2m >= 512, mu >= 9.
    for mu in [9, 10, 11, 12]:
        test(mu, beta=4)
