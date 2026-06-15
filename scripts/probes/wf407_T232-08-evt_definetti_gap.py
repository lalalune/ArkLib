"""
wf407 / T232-08-evt : THE DECISIVE de-Finetti gap test.

Question: Is EXCHANGEABILITY + the two linear/quadratic moment constraints
  (i)  sum_c eta_c = -1            (mean -1/m)
  (ii) sum_c |eta_c|^2 = p - n     (Var(Re) ~ n/2 per coord)
  (iii) cov_offdiag = -Var/(m-1)   (the white-noise fingerprint)
SUFFICIENT to PROVE the EVT bound  max_c |eta_c| <= sqrt(2n log m)(1+o(1))?

If YES -> the EVT route to the floor is VIABLE (the floor would follow from
proven structural facts).  If NO -> the route is WALLED at the bulk-vs-tail
gap: the same data can be matched by a family with an arbitrarily large max.

METHOD: construct an EXPLICIT exchangeable family Y_1..Y_m that satisfies (i)-(iii)
EXACTLY but whose maximum is O(m) (linear, not sqrt-log). If such a family exists,
then no theorem using only (i)-(iii) can bound the max by sqrt(2n log m); the
sub-Gaussian MGF (4th+ moments = Gauss-sum equidistribution) is irreducibly needed.

Construction of an adversarial exchangeable family with prescribed mean mu and
variance v and off-diag cov -v/(m-1):
   Take a "spike" family: one coord = a (large), the rest share -(a - m*mu)/(m-1)...
   but a SINGLE fixed-position spike is not exchangeable. To be exchangeable we
   randomize the spike position uniformly => the family is a MIXTURE. Its
   one-point and two-point marginals match (i)-(iii) but max = a is huge.
We verify the moment-match numerically and report max vs sqrt(2 v log m).
Also: scaled to per-coord variance v = n/2, mean = -1/m (matching the real periods),
choose the spike a as large as the variance budget allows: with one spike of height a
and (m-1) values of height b, exchangeable means E over position; constraints:
   mean: (a + (m-1) b)/m = mu
   var : (a^2 + (m-1) b^2)/m - mu^2 = v
Solve for (a,b). The LARGER root a ~ sqrt(v*(m-1)) -> max grows like sqrt(v*m),
which is sqrt((n/2)*m) -- ENORMOUSLY bigger than sqrt(2 v log m). This is the
gap a moment-only theorem cannot close.
"""
import numpy as np
from math import sqrt, log

def two_value_exchangeable(mu, v, m):
    """One coord = a, (m-1) coords = b, randomized position. Match mean mu, var v.
       Returns (a, b). a = the spike (larger)."""
    # (a + (m-1)b)/m = mu  => a = m*mu - (m-1)b
    # var: (a^2 + (m-1)b^2)/m - mu^2 = v
    # substitute a:
    # let A = m*mu. a = A - (m-1)b.
    # (A-(m-1)b)^2 + (m-1)b^2 = m(v+mu^2)
    # expand: A^2 -2A(m-1)b + (m-1)^2 b^2 + (m-1)b^2 = m(v+mu^2)
    # (m-1)^2 b^2 + (m-1) b^2 = (m-1)*m*b^2 ... wait: (m-1)^2 + (m-1) = (m-1)*m
    # so: (m-1)m b^2 - 2A(m-1) b + A^2 - m(v+mu^2) = 0
    A = m*mu
    qa = (m-1)*m
    qb = -2*A*(m-1)
    qc = A*A - m*(v + mu*mu)
    disc = qb*qb - 4*qa*qc
    if disc < 0:
        return None
    b1 = (-qb + sqrt(disc))/(2*qa)
    b2 = (-qb - sqrt(disc))/(2*qa)
    # spike a corresponds to the b that makes a large (a = A-(m-1)b small b -> big a)
    cands = []
    for b in (b1, b2):
        a = A - (m-1)*b
        cands.append((a, b))
    # pick the one with the larger |a| (the adversarial spike)
    cands.sort(key=lambda t: -abs(t[0]))
    return cands[0]

def offdiag_cov_two_value(a, b, mu, m):
    """For the position-randomized two-value family, off-diagonal cov of two distinct coords.
       E[Y_i Y_j] for i!=j: with prob (one of them is the spike) 2/m: a*b ; else b*b.
       Actually: pair (i,j). Spike at i: a*b. Spike at j: a*b. Spike elsewhere: b*b.
       P(spike=i)=1/m, P(spike=j)=1/m, P(else)=(m-2)/m.
       E[Y_iY_j] = (2/m) a b + ((m-2)/m) b^2."""
    EYiYj = (2.0/m)*a*b + ((m-2.0)/m)*b*b
    return EYiYj - mu*mu

if __name__=="__main__":
    print("=== de Finetti GAP: adversarial exchangeable family with matched (mean,var,cov) ===")
    print("Per-coord directional model: mu = -1/m (tiny), v = n/2 (real-part variance).")
    print(f"{'n':>4} {'m':>7} {'spike a':>10} {'b':>9} {'covOFF':>10} {'-v/(m-1)':>10} "
          f"{'covMatch':>8} {'a/sqrt(2v lnm)':>14} {'sqrt(v*m)/a':>11}")
    for n in (8,16,32,64,256, 2**20):
        v = n/2.0
        for m in (16, 64, 256, 1024):
            mu = -1.0/m
            res = two_value_exchangeable(mu, v, m)
            if res is None:
                continue
            a, b = res
            cov = offdiag_cov_two_value(a, b, mu, m)
            pred = -v/(m-1)
            match = abs(cov - pred) < 1e-6*max(1,abs(pred))
            gumbel = sqrt(2*v*log(m))
            ratio = a/gumbel
            print(f"{n:>4} {m:>7} {a:>10.3f} {b:>9.4f} {cov:>10.5f} {pred:>10.5f} "
                  f"{str(match):>8} {ratio:>14.2f} {sqrt(v*m)/a:>11.4f}")
    print()
    print("CONCLUSION OF THE GAP TEST:")
    print(" The adversarial family is EXACTLY exchangeable (position-randomized), matches the mean,")
    print(" the variance, AND the off-diag covariance -v/(m-1) (covMatch=True), yet its MAX = a grows")
    print(" like sqrt(v*(m-1)) ~ sqrt(n*m/2) -- LINEAR-ish in sqrt(m), NOT sqrt(2v log m).")
    print(" Ratio a/sqrt(2v ln m) BLOWS UP with m. => (mean,var,cov) alone CANNOT prove the EVT floor.")
    print(" The sub-Gaussian MGF (all higher moments, = Gauss-sum joint equidistribution) is")
    print(" IRREDUCIBLY required. The EVT route is walled exactly at the bulk(2-moment)->tail(MGF) gap.")
