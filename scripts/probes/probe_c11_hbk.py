"""
C11 follow-up: does the HEATH-BROWN-KONYAGIN subgroup-specific bound (not generic Burgess)
or any DEPTH-r amplification change the verdict?

HBK (Heath-Brown-Konyagin 2000) for a multiplicative subgroup H of size t:
  - if t >> p^{1/2}:   |sum_{x in H} e_p(ax)| << t^{3/4} p^{1/8}   (or similar)
  - if t >> p^{1/4}:   |...| << t^{2/3} p^{1/12} ... etc
These are all NONTRIVIAL ONLY for t > p^{1/4}.  Test the crossover threshold directly.

Key test: for the ACTUAL amplification gain to help, the bound on the *single sum* must
be sub-Johnson (< sqrt(n) up to polylog) for the moment consumer.  Equivalently the
DEPTH-r 2r-th-moment Burgess bound on the FULL energy must give E_r < (2r-1)!! n^r.
We check: does the Burgess single-sum bound, fed into the energy via
  E_r >= max_b |eta_b|^{2r}/q-ish ... no -- E_r is an AVERAGE.  The moment consumer goes
the OTHER way: E_r bound -> sup bound.  Burgess gives sup -> can it give E_r?

The honest reduction: the moment method NEEDS an a-priori energy bound E_r <= (2r-1)!! n^r.
Burgess does NOT provide an energy bound; it provides a sup bound.  Feeding sup -> energy
via E_r <= (n^{2r} total mass spread) is the trivial CS floor n^{2r}/q (Reason-3 floor),
which gives sup >= n.  So Burgess is on the WRONG side of the moment ladder.
"""
import math
from sympy import isprime, primitive_root
import cmath

def find_prime(n, beta_target, tries=400000):
    target = int(round(n**beta_target))
    m0 = max(2, target // n)
    for m in range(m0, m0+tries):
        p = m*n + 1
        if p <= n+1: continue
        if isprime(p): return p, m
    return None, None

def double_fact(k):
    r=1; i=k
    while i>0: r*=i; i-=2
    return r

print("=== HBK / Korobov subgroup exponents: nontrivial only for t > p^{1/4}? ===")
print(" Various subgroup sup-bound exponents alpha s.t. M <= t^alpha, as fn of theta=log_p t:")
print(" Konyagin t>p^{1/2}: t^{3/4} p^{... } => for t=p^theta, exponent in t of full bound:")
for theta in [0.5, 0.33, 0.25, 0.215, 0.135]:
    beta = 1/theta
    # Burgess incomplete-sum form (best r): M << t^{1-1/r} p^{(r+1)/(4r^2)}
    best = min((1-1/r) + beta*(r+1)/(4*r*r) for r in range(1,500))
    # HBK/Konyagin large-subgroup: M << t^{3/4} p^{1/8}  -> exponent in t: 3/4 + beta/8
    hbk = 3/4 + beta/8
    print(f"  theta={theta:.3f} (beta={beta:.2f}): Burgess-best exp_in_t={best:.4f}, HBK-3/4 exp_in_t={hbk:.4f} (trivial=1, target=0.5)")

print()
print("=== Direct check: does ANY proven sup-bound, fed to the moment consumer, give R_r<=1? ===")
print(" The consumer needs an ENERGY bound. Burgess gives a SUP bound M. The only way sup->energy")
print(" is the trivial CS mass floor E_r >= n^{2r}/q. There is no proven energy upper bound from Burgess.")
print(" So we confirm the structural fact: the sup-bound side and the energy-bound side are DISJOINT inputs.")
for mu in [4]:
    n=2**mu; p,m=find_prime(n,4.0)
    g=primitive_root(p); mm=(p-1)//n; h=pow(g,mm,p)
    mu_n=[pow(h,i,p)%p for i in range(n)]
    w=2j*math.pi/p
    etas=[abs(sum(cmath.exp(w*((b*x)%p)) for x in mu_n)) for b in range(1,p)]
    q=p
    Mn=max(etas)
    for r in [2,3,5,8]:
        df=double_fact(2*r-1); wick=df*n**r
        Sr=sum(e**(2*r) for e in etas)
        Er=Sr/q  # average energy (= E_r since q-1 nonzero + b=0 spike handled separately)
        floor = n**(2*r)/q
        print(f"  n={n} r={r}: exact E_r(nonzero avg)={Er:.3e}  Wick (2r-1)!!n^r={wick:.3e}  CS-floor n^2r/q={floor:.3e}  R_r={Er/wick:.4f}")
