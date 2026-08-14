#!/usr/bin/env python3
"""
LANE wf-M1: HEIGHT/MAHLER pre-screen of the char-p spurious-vanishing bound.

REDUCTION (the sufficient lemma):
  M(n) = char-0 moment count <=> spurious char-p vanishing count = 0 to depth r ~ ln q.
  A char-p spurious config at depth r is a subset/signed-subset T, |T| <= 2r, of zeta_n exponents
  with  sigma_T = sum_{i in T} +-zeta_n^i  NONZERO over Z (antipodal-free, by Lam-Leung)
  but  p | N(sigma_T),  N = Norm_{Q(zeta_n)/Q}.

  HOUSE/MAHLER BOUND:  N(sigma_T) = prod over phi(n) conjugates of |sigma_T^(j)|.
  Each conjugate is a sum of <= 2r roots of unity, so |sigma_T^(j)| <= 2r = house.
  Hence  1 <= |N(sigma_T)| <= (2r)^{phi(n)} = (2r)^{n/2}   (phi(2^mu)=n/2).

  SUFFICIENT LEMMA (S-M1):  if  (2r)^{n/2} < p   then NO nonzero sigma_T has p | N(sigma_T)
  for any |sigma_T| at depth <= r  ==>  char-p energy = char-0 energy  ==>  Johnson-beating
  moment bound transfers  ==>  M(n) <= C sqrt(n log(p/n)).

  THE NUMBER TO BEAT: depth r ~ ln q ~ n*beta*ln2.  Prize: n=2^30, beta~4, p~n^4.
  We test:  is (2r)^{n/2} < p  at prize and small params?  i.e. does the CRUDE house bound suffice?
"""
import math

def screen(n, beta):
    # prize prime ~ n^beta
    logp = beta*math.log(n)                 # ln p
    # depth r needed: the meta-route needs r ~ ln q = ln p (deep moments to depth ~ log q)
    r_deep = logp                            # r ~ ln p (the "deep moment" depth)
    r_full = 1.36*n                          # free regime r >~ 1.36 n
    # house bound LHS as a LOG:  (n/2) * ln(2r)
    def loghouse(r):
        return (n/2.0)*math.log(2*r)
    lh_deep = loghouse(r_deep)
    lh_full = loghouse(r_full)
    # threshold r* where (2r)^{n/2} = p :  ln(2r*) = logp/(n/2) = 2 logp / n  => 2r* = exp(2 logp/n)
    twrstar = math.exp(2*logp/n)
    rstar = twrstar/2.0
    return dict(n=n, beta=beta, logp=logp, r_deep=r_deep, lh_deep=lh_deep,
                lh_full=lh_full, rstar=rstar, r_full=r_full)

print("HOUSE-BOUND PRE-SCREEN: need (2r)^(n/2) < p, i.e.  (n/2)ln(2r) < ln p")
print("rstar = largest r for which house bound proves NO spurious = exp(2 ln p / n)/2\n")
print(f"{'n':>12} {'beta':>5} {'lnp':>9} {'r_deep~lnp':>11} {'(n/2)ln(2r_deep)':>16} {'<lnp?':>7} {'rstar':>10}")
for n,beta in [(8,4),(16,4),(32,4),(64,4),(128,4),(256,4),(1024,4),(2**20,4),(2**30,4),(2**30,5)]:
    d = screen(n,beta)
    ok = "YES" if d['lh_deep'] < d['logp'] else "NO"
    print(f"{n:>12} {beta:>5} {d['logp']:>9.3f} {d['r_deep']:>11.3f} {d['lh_deep']:>16.3e} {ok:>7} {d['rstar']:>10.4f}")

print("\nINTERPRETATION:")
print(" rstar = exp(2 ln p/n)/2.  For n large, 2 ln p/n -> 0, so 2 rstar -> 1, rstar -> 1/2.")
print(" => the crude house bound (2r)^(n/2)<p only proves NO-spurious for r < ~1/2  (depth < 1!).")
print(" The needed depth is r ~ ln p >> 1/2.  HOUSE BOUND IS EXPONENTIALLY TOO WEAK.")
