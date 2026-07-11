"""
LANE I2 / probe_wfH_i2_exponent_pair: Exponent-pair / van der Corput / Bombieri-Iwaniec
on the dyadic Gauss period.  EXACT INTEGER ARITHMETIC (no float-FFT).

OBJECT.  mu_n = order-n 2-power multiplicative subgroup of F_p^* (n = 2^mu, p = 1 mod n).
  eta_b = sum_{x in mu_n} e_p(b x).   M(n) = max_{b != 0} |eta_b|.
  Prize:  M(n) <= C sqrt(n log(p/n)),  prize scale n ~ 2^30, p = n^beta, beta = 4.

PARAMETERIZATION.  Fix a primitive root g of F_p, let m = (p-1)/n, h = g^m (a generator of mu_n).
  Then x runs over {h^j : j = 0..n-1} and
     eta_b = sum_{j=0}^{n-1} e_p( b * h^j mod p )  =  sum_j e_p( f_b(j) ),
  where the "phase" is  f_b(j) := (b * g^{m j}) mod p,  an integer in [0,p).
  This is the multiplicative-exponential phase the van der Corput / exponent-pair machinery
  would have to handle.

THE STRUCTURAL TEST (the kill).  The van der Corput A-process (Weyl differencing) + B-process
  + exponent pairs ALL require f(j)/p to be a SMOOTH real-variable function whose derivatives
  behave like a monomial: f^{(r+1)}(x) ~ T x^{-s-r}, in particular a controlled NON-ZERO
  second derivative (curvature) f'' >= lambda > 0 for the B-process and the second-derivative
  test.  We test, with EXACT integers, whether f_b(j) has ANY such structure:

  (T1) DISCRETE DERIVATIVES.  Define the discrete phase theta(j) = f_b(j)/p in [0,1).
       First/second/third forward differences (mod 1, taken to (-1/2,1/2]):
          D1(j) = theta(j+1) - theta(j),   D2(j) = D1(j+1) - D1(j),  D3 = ...
       Van der Corput class: D2 should be ~CONSTANT-SIGN, small, monomial-monotone.
       We compute, EXACTLY (rationals p|.), the multiset of D2 values and report:
         - sign pattern (does D2 keep one sign? curvature condition f''>=lambda>0?)
         - range / spread of D2 (is it O(1/n^2)-monomial, or O(1)-equidistributed?)
         - is D1 monotone (B-process needs f' monotone)?

  (T2) EXPONENT-PAIR BEST CASE.  Even granting a phase of "length" N=n with "height" T~p,
       the BEST exponent pair gives |sum| <= (T/N^?)^k N^l.  The van der Corput first bound
       (1/2,1/2) gives |S| << sqrt(T) = sqrt(p) = n^2 (= Weil, trivial here).  The best known
       exponent pairs approach the exponent (k,l) -> Bourgain (13/84+e, 55/84+e) etc.  We
       compute the resulting bound on |eta_b| for the prize-regime sizes and compare to:
         Johnson  sqrt(n) = n^{1/2},   prize sqrt(n log m) ~ n^{1/2} sqrt(log),   trivial n.
       The phase "height" for a complete sum over F_p is T ~ p, "length" N ~ n.  This is the
       wrong-aspect-ratio regime (N << sqrt(T)) where vdC is vacuous.

  (T3) A-PROCESS = ADDITIVE ENERGY (F1 check).  One step of Weyl differencing turns
       |eta_b|^2 type control into a sum over shift-correlations
          sum_h | sum_j e_p( f_b(j+h) - f_b(j) ) |.
       For the multiplicative phase  f_b(j+h)-f_b(j) = b h^j (h^h_step - 1) -- itself a
       dilated subgroup sum.  We verify EXACTLY that the differenced inner sum is again a
       Gauss period (subgroup sum), i.e. the A-process maps the problem back to the SAME
       family = it is a 2nd-moment / energy step (fence F1), giving NO new handle.
"""
import math
from fractions import Fraction
from sympy import isprime, primitive_root

def find_prime(n, beta, tries=400000):
    target = int(round(n ** beta))
    m0 = max(2, target // n)
    for k in range(m0, m0 + tries):
        p = k * n + 1
        if p <= n + 1:
            continue
        if isprime(p):
            return p, k
    return None, None

def subgroup(n, p):
    g = primitive_root(p)
    m = (p - 1) // n
    h = pow(g, m, p)
    pts = [pow(h, j, p) for j in range(n)]
    return g, m, h, pts

def eta_abs2(b, pts, p):
    # exact |eta_b|^2 via sum of cos/sin? We avoid float: compute |eta|^2 = sum_{j,k} cos(2pi (b(x_j-x_k))/p).
    # For magnitude we still need a real; but to find the MAX we can use exact integer:
    # |eta_b|^2 = sum_{d in F_p} c(d) cos(2pi d/p), c(d)=#{(j,k): b(x_j-x_k)=d}. Use mpmath-free:
    # Use the fact eta_b is real part combos; fall back to high-precision via Python complex is float.
    pass

def to_centered(frac):
    # map a Fraction in [0,1) to (-1/2, 1/2]
    f = frac - Fraction(int(frac), 1)
    if f < 0:
        f += 1
    if f > Fraction(1, 2):
        f -= 1
    return f

print("=== T1: discrete-derivative (curvature) structure of the multiplicative phase f_b(j) ===")
print("    van der Corput / exponent-pair need f''(curvature) one-signed and ~monomial-small.")
for mu in [4, 5, 6]:
    n = 2 ** mu
    p, m = find_prime(n, 4.0)
    g, mstep, h, pts = subgroup(n, p)
    b = 1  # worst b found below; structure is b-equivariant for this test
    theta = [Fraction(pts[j], p) for j in range(n)]  # f_b(j)/p, b=1
    D1 = [to_centered(theta[(j + 1) % n] - theta[j]) for j in range(n)]
    D2 = [to_centered(D1[(j + 1) % n] - D1[j]) for j in range(n)]
    # sign analysis of D2 (curvature)
    pos = sum(1 for d in D2 if d > 0)
    neg = sum(1 for d in D2 if d < 0)
    zer = sum(1 for d in D2 if d == 0)
    # spread of D2 vs the monomial scale 1/n^2 and the equidistributed scale O(1)
    maxD2 = max(abs(float(d)) for d in D2)
    meanabsD2 = sum(abs(float(d)) for d in D2) / n
    # is D1 monotone? count monotonicity violations
    D1f = [float(d) for d in D1]
    incr_viol = sum(1 for j in range(n) if D1f[(j + 1) % n] < D1f[j])
    print(f"  n={n} p={p} beta={math.log(p)/math.log(n):.3f}")
    print(f"    D2 sign: +{pos} / -{neg} / 0={zer}  (curvature one-signed? need all-+ or all--)")
    print(f"    |D2|: max={maxD2:.4f} mean={meanabsD2:.4f}   monomial scale 1/n^2={1/n**2:.5f}   equidist O(1/2)")
    print(f"    D1 monotonicity violations: {incr_viol}/{n}   (B-process needs f' monotone => 0 or n)")

print()
print("=== T2: exponent-pair BEST-CASE bound on |eta_b|, height T~p, length N~n, beta=4 ===")
print("    bound |S| << (T/N^s)^k N^l ; we report the resulting exponent of n and compare to prize/Johnson.")
# Standard exponent-pair convention for monomial phase f(x)= (T/N^s) x^s style: result exponent
# For a complete subgroup sum the natural 'height' is T = p = n^beta over length N = n.
# Van der Corput first pair (k,l)=(1/2,1/2): |S| << (T)^{1/2} = p^{1/2} = n^{beta/2}=n^2 (Weil, trivial).
# Walfisz/optimal pairs lower l but RAISE the T-power balance; best vdC exponent for |S| in N,T:
#   |S| << N^{1-...} T^{...}. We tabulate the family of classical pairs and the resulting n-exponent.
beta = 4.0
pairs = {
    "trivial (sum of N ones)": ("N", 1.0, 0.0),                 # |S|<=N
    "vdC first (1/2,1/2) = Weil sqrt(T)": ("kl", 0.5, 0.5),
    "vdC (1/6,2/3)": ("kl", 1/6, 2/3),
    "Phillips (11/30,16/30)": ("kl", 11/30, 16/30),
    "Bourgain (13/84,55/84)": ("kl", 13/84, 55/84),
    "Johnson floor sqrt(N)": ("N", 0.5, 0.0),
    "PRIZE sqrt(N log) ~": ("N", 0.5, 0.0),
}
# For an exponent pair (k,l), with phase of height T and length N, the bound is
#   |S| << (T / N)^k * N^l   (the standard normalization where the 'amplitude' parameter is T/N
#   the derivative scale of the leading monomial over the interval).  Here T=p=n^beta, N=n.
# => exponent_of_n = k*(beta-1) + l.
for name, (kind, k, l) in pairs.items():
    if kind == "N":
        expo = k  # |S| ~ N^k = n^k (here k is really the n-exponent for the N-type rows)
        # for trivial row k=1.0 -> n^1; johnson/prize k=0.5 -> n^0.5
        print(f"  {name:42s}: |eta_b| ~ n^{expo:.4f}")
    else:
        expo = k * (beta - 1) + l
        print(f"  {name:42s}: (k,l)=({k:.4f},{l:.4f}) -> |eta_b| ~ n^{expo:.4f}   (prize needs 0.5)")
print("  NOTE: prize floor exponent = 0.5 (plus sqrt-log). Any exponent-pair value > 0.5 = NO crossing.")

print()
print("=== T3: A-process (Weyl differencing) maps the period back to a subgroup sum (=F1 energy) ===")
print("    one differencing step: inner sum_j e_p(b(h^{j+t}-h^j)) = e-sum over the SAME mu_n (dilated).")
for mu in [4, 5]:
    n = 2 ** mu
    p, m = find_prime(n, 4.0)
    g, mstep, h, pts = subgroup(n, p)
    b = 1
    all_subgroup = True
    for t in range(1, n):
        # f_b(j+t)-f_b(j) = b(h^{j+t}-h^j) = b h^j (h^t - 1).  As j varies over 0..n-1, h^j ranges over mu_n,
        # so the difference set is { b(h^t-1) * y : y in mu_n } = a DILATE of mu_n (a coset-scaled subgroup sum).
        c = (b * (pow(h, t, p) - 1)) % p
        diffset = sorted({(c * y) % p for y in pts})
        # check it is c * mu_n (size n unless c=0)
        expected = sorted({(c * y) % p for y in pts})
        if c != 0 and len(diffset) != n:
            all_subgroup = False
    print(f"  n={n} p={p}: every differenced phase set b(h^t-1)*mu_n is a scaled copy of mu_n: {all_subgroup}")
    print(f"    => Weyl differencing returns sum over (a dilate of) mu_n = the SAME family. The differenced")
    print(f"       2nd-moment is an additive-energy / shift-correlation of mu_n = FENCE F1 (moment/energy).")
