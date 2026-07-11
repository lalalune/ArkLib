# Probe the EXACT algebraic relation between:
#   - the nonprincipal even-moment   E_r' := (1/p) * sum_{b != 0} |eta_b|^{2r}
#   - the in-tree combinatorial moment  E_r  (full-spectrum second-moment style)
#   - the DC-subtracted object  A_r := q*E_r - n^{2r}   (used by DCWick spine)
# where eta_b = sum_{x in mu_n} psi(b*x), q = p (prime field F_p), n = |mu_n|.
#
# Conjecture to verify exactly: sum_{b != 0} |eta_b|^{2r} = sum_{b in F} |eta_b|^{2r} - |eta_0|^{2r},
# and eta_0 = n, so  p * E_r' = (sum_b |eta_b|^{2r}) - n^{2r}.
# If the in-tree E_r is defined as E_r = (1/q) sum_b |eta_b|^{2r} (q=p), then sum_b = q*E_r, so
#   p * E_r' = q*E_r - n^{2r} = A_r   EXACTLY   (with q=p).
# => E_r' = A_r / p   exactly. This is the weld: nonprincipal moment = DC-subtracted moment / p.
import cmath, math, random

def find_primitive_root(p):
    n = p - 1; fac = set(); d = 2
    while d * d <= n:
        while n % d == 0:
            fac.add(d); n //= d
        d += 1
    if n > 1: fac.add(n)
    for g in range(2, p):
        if all(pow(g, (p - 1) // q, p) != 1 for q in fac):
            return g
    return None

def eta(p, n, b, sub):
    # eta_b = sum_{x in mu_n} e_p(b x), e_p(t)=exp(2pi i t/p)
    s = 0+0j
    for x in sub:
        s += cmath.exp(2j*math.pi*(b*x % p)/p)
    return s

def run(p, n):
    g = find_primitive_root(p)
    h = pow(g, (p-1)//n, p)
    sub = [pow(h, i, p) for i in range(n)]
    for r in [1,2,3]:
        full = 0.0
        for b in range(p):
            full += abs(eta(p,n,b,sub))**(2*r)
        eta0 = abs(eta(p,n,0,sub))**(2*r)  # = n^{2r}
        nonprincipal_sum = full - eta0
        Er_prime = nonprincipal_sum / p
        # in-tree style: E_r = (1/q) sum_b |eta_b|^{2r}, q=p
        Er = full / p
        A_r = p*Er - n**(2*r)   # q*E_r - n^{2r}, q=p
        # check E_r' == A_r / p
        lhs = Er_prime
        rhs = A_r / p
        print(f"  n={n} p={p} r={r}: eta0^2r={eta0:.1f} (n^2r={n**(2*r)}) | E_r'={lhs:.4f} A_r/p={rhs:.4f} match={abs(lhs-rhs)<1e-6} | E_r'/((2r-1)!!*n^r)={lhs/(dfact(2*r-1)*n**r):.4f}")

def dfact(m):
    r=1
    while m>1:
        r*=m; m-=2
    return r

random.seed(1)
for p,n in [(4129,8),(8009,8),(65537,16)]:
    if (p-1)%n!=0: continue
    print(f"=== p={p} n={n} ===")
    run(p,n)
