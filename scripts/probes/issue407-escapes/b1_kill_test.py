import sympy, math

# =====================================================================
# CORE QUESTION: Does the CS25/CZ25 near-capacity LOWER bound KILL B1,
# or just restrict the window? B1 wants |bad scalars| <= O(n)/q-level
# bound for plain RS s=1 at delta in window (1-sqrt(rho), 1-rho-Theta(1/log n)).
#
# CS25 Theorem 1 (the explicit proximity-gap-FAILURE construction):
#   if f < n-k and Delta(u1, RS) > f, exists u0 with at least
#       N_lambda = (q-1)*p  bad lambda    where p = Pr[Delta(u0+lam u1) <= f]
#   and CS25 lower-bound p via Cantelli: p >= ... Specifically the bound is
#       N >= n/(f) ... g(...) form. Key: N >= (q-n)/(...) * something
#   The headline: for f in a RANGE (n*(1-Hq(f/n))+... <= k <= n-f-2),
#   epsilon cannot be < 1, i.e. ALL lambda can be bad => bad count = q.
#
# This is the BAD-SIDE: it gives a family with bad-count = Theta(q), i.e.
# eps_mca ~ 1, NOT O(n)/q. The question for B1: at WHICH delta (=f/n) does
# this kick in? If it kicks in BELOW the Kambire edge, B1 is DEAD (the
# Kambire-edge floor is false). If only ABOVE the edge, B1 survives the window.
# =====================================================================

def Hq(x, q):
    # q-ary entropy H_q(x) = x*log_q(q-1) - x*log_q x - (1-x)log_q(1-x)
    if x<=0 or x>=1: return 0.0
    import math
    lq = math.log(q)
    return (x*math.log(q-1) - x*math.log(x) - (1-x)*math.log(1-x))/lq

# CS25 Corollary regime: n(1-Hq(f/n)) + 2 + sqrt(n*Hq(f/n)) - f <= k <= n-f-2
# In this k-range the proximity gap FAILS (eps cannot be < 1).
# Solve: for given n, rho=k/n, what delta=f/n triggers failure?
# The LOWER edge of failure delta: k >= n(1-Hq(delta)) + 2 + sqrt(n Hq(delta)) - n*delta
#   => rho >= 1 - Hq(delta) - delta + o(1)   (drop the +2/sqrt terms, n large)
#   => Hq(delta) >= 1 - rho - delta
# This is EXACTLY the list-decoding-capacity bound (entropy form)!
#   delta_cap solves Hq(delta) = 1 - rho - delta  ... wait, list-decoding
#   capacity for RS is delta s.t. Hq(delta) = 1 - rho (the GV/capacity radius).
# Actually CS25 failure region lower edge: 1 - rho - Hq(delta) - delta <= 0... let me
# compute the actual delta threshold numerically for prize params.

def cs25_failure_lower_delta(n, rho, q):
    """Smallest delta=f/n such that CS25 failure regime is entered (eps cannot be <1).
       Condition (from corollary): k <= n - f - 2 AND
       k >= n(1-Hq(f/n)) + 2 + sqrt(n*Hq(f/n)) - f.
       => need n(1-Hq(delta)) + 2 + sqrt(n Hq(delta)) - n*delta <= k = rho*n <= n - n*delta - 2.
       Find smallest delta where BOTH hold."""
    import math
    k = rho*n
    best=None
    d=0.0
    while d < 1-rho:
        f = d*n
        H = Hq(d, q)
        lo = n*(1-H) + 2 + math.sqrt(max(n*H,0)) - f   # lower edge of k for failure
        hi = n - f - 2                                  # upper edge of k (f < n-k => k < n-f)
        if lo <= k <= hi:
            best = d
            break
        d += 0.001
    return best

# Kambire edge (the B1 target floor): delta* = 1 - rho - H(rho)/(beta*log2 n)
# with beta ~ such that q = n^beta. Prize: q ~ n^4..n^5, eps*=2^-128.
# Compare against:
#  - Johnson:  1 - sqrt(rho)
#  - list-dec capacity (entropy): delta s.t. Hq(delta)=1-rho
#  - CS25 failure lower edge (computed above)
import math
def H2(x):
    if x<=0 or x>=1: return 0.0
    return -x*math.log2(x)-(1-x)*math.log2(1-x)

print(f"{'n':>6} {'rho':>5} {'q~n^b':>8} | {'Johnson':>8} {'Kambire':>8} {'LD-cap':>8} {'CS25-fail':>10}")
for mu in [16, 20, 24, 30]:
    n = 2**mu
    for rho in [0.5, 0.25, 0.125]:
        for beta in [4]:
            q = n**beta
            johnson = 1 - math.sqrt(rho)
            # Kambire edge: 1 - rho - H2(rho)/(beta*log2 n)   (log2 n = mu)
            kambire = 1 - rho - H2(rho)/(beta*mu)
            # LD capacity (q-ary entropy): Hq(delta)=1-rho
            d=0.0; ldcap=None
            while d<1-rho:
                if Hq(d,q) >= 1-rho:
                    ldcap=d; break
                d+=0.0005
            cs25 = cs25_failure_lower_delta(n, rho, q)
            print(f"{mu:>4}({2**0}) {rho:>5} {beta:>8} | {johnson:>8.4f} {kambire:>8.4f} {str(round(ldcap,4)) if ldcap else 'NA':>8} {str(round(cs25,4)) if cs25 else 'NA':>10}")
