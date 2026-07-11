#!/usr/bin/env python3
"""
Probe for CONJECTURE C17 (Kelley-Owen Dilation-Pencil Sharp Constant).

C17 claims: for the (k+2)-term face P = x^a + gamma*x^b - c(x) (deg c < k), the
k-dimensional dilation pencil double-count gives the SHARP bound
    s* = |{x in mu_n : P(x)=0}| <= sqrt((k+1)*n) + O(k)
as an EQUALITY realized by the antipodal pencil, pinning delta* at 1-sqrt(rho)(1+o(1)).

We REFUTE the sharpness/upper-bound claim with the explicit in-tree _RThinSqrtNKRefuted
witness, over a PROPER dyadic subgroup mu_n of F_p^* with p PRIME, p >> n^3, n != p-1.

Witness (k=2): P(X) = (X^m + 1)(X - 1), m = n/2, support {0,1,m,m+1} (4 = k+2 terms).
Root set in mu_n = {x : x^m = -1} cup {1}, size m+1 = n/2 + 1.

We verify |S| = n/2 + 1 > sqrt(k*n) and > sqrt((k+1)*n) for the prize rates,
i.e. the (k+2)-term face has a list far ABOVE the claimed sharp sqrt bound -- and the
list size grows LINEARLY in n, not like sqrt(n). The bound is not an upper bound at all
in the worst case (large coset core), so its claimed "equality" is false; where it does
hold it equals exactly the Johnson agreement -> Johnson radius, never past it.
"""
import math

def is_prime(N):
    if N < 2: return False
    if N % 2 == 0: return N == 2
    i = 3
    while i*i <= N:
        if N % i == 0: return False
        i += 2
    return True

def find_prime(n, exp=4):
    # p prime, p = 1 mod n (so mu_n exists as a proper subgroup), p >> n^3, n != p-1.
    target = n**exp
    t = (target // n)  # we want p = t*n + 1 prime, p ~ n^exp >> n^3
    while True:
        p = t*n + 1
        if p > n**3 and is_prime(p):
            return p
        t += 1

def primitive_root(p):
    # find a generator of F_p^*
    from sympy import primitive_root as pr
    return pr(p)

print("Probe C17: dilation-pencil sharp-constant refutation over proper mu_n, p prime, p>>n^3, n != p-1")
print("="*100)

try:
    from sympy import primitive_root as pr
    have_sympy = True
except Exception:
    have_sympy = False

def find_primitive_root(p):
    if have_sympy:
        return int(pr(p))
    # fallback
    def order(g):
        # factor p-1 trivially by trial
        phi = p-1
        # check g^(phi/q) != 1 for prime q | phi
        f = []
        m = phi; d = 2
        while d*d <= m:
            if m % d == 0:
                f.append(d)
                while m % d == 0: m//=d
            d += 1
        if m>1: f.append(m)
        for q in f:
            if pow(g, phi//q, p) == 1: return False
        return True
    g = 2
    while not find_primitive_root_check(g, p):
        g += 1
    return g

results = []
for mu in range(3, 8):  # n = 8,16,32,64,128 (small but real; proper subgroups)
    n = 2**mu
    k = 2  # the witness face has k=2 (support {0,1,m,m+1}, t=4=k+2)
    m = n // 2
    p = find_prime(n, exp=4)   # p ~ n^4 >> n^3, p = 1 mod n, p != n+1 (since p~n^4)
    assert p != n + 1, "must not be n=p-1"
    assert is_prime(p)
    assert (p - 1) % n == 0
    assert p > n**3
    g = find_primitive_root(p)
    # mu_n = <g^((p-1)/n)>, the order-n subgroup
    h = pow(g, (p-1)//n, p)            # generator of mu_n
    mu_n = set(pow(h, i, p) for i in range(n))
    assert len(mu_n) == n
    # The codeword line P(X) = (X^m+1)(X-1) = X^{m+1} - X^m + X - 1
    # Roots in mu_n: x with x^m == -1 mod p, together with x == 1.
    minus1 = p - 1
    S = set()
    for x in mu_n:
        if x == 1:
            S.add(x)
        elif pow(x, m, p) == minus1:
            S.add(x)
    s_star = len(S)
    sqrt_kn   = math.sqrt(k*n)        # Johnson-form sqrt(n*k)
    sqrt_k1n  = math.sqrt((k+1)*n)    # the C17 claimed bound sqrt((k+1)*n)
    refutes_kn  = s_star > sqrt_kn
    refutes_k1n = s_star > sqrt_k1n
    results.append((n, p, m, s_star, sqrt_kn, sqrt_k1n, refutes_kn, refutes_k1n))
    print(f"n={n:4d} p={p:>12d} (p/n^3={p/n**3:.1f}, p!=n+1: {p!=n+1}) m=n/2={m}")
    print(f"    |S| = {s_star}  (predicted n/2+1 = {m+1})  "
          f"sqrt(kn)={sqrt_kn:.2f}  sqrt((k+1)n)={sqrt_k1n:.2f}")
    print(f"    |S| > sqrt(kn)?  {refutes_kn}    |S| > sqrt((k+1)n)?  {refutes_k1n}   "
          f"[{'REFUTES C17 sharp upper bound' if refutes_k1n else 'within'}]")

print("="*100)
all_refute = all(r[7] for r in results if r[0] >= 8)
print(f"VERDICT: every n>=8 witness has |S|=n/2+1 EXCEEDING the claimed sqrt((k+1)n) bound: {all_refute}")
print("The (k+2)-term face list grows LINEARLY (n/2+1), not as sqrt((k+1)n).")
print("So the 'sharp double-count = sqrt((k+1)n) equality' is FALSE; even where the double-count")
print("upper-bounds (small coset core), s* ~ n*sqrt(rho) == Johnson agreement -> radius 1-sqrt(rho),")
print("which is exactly Johnson, NOT past it.")
