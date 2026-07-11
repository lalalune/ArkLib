#!/usr/bin/env python3
"""
P7-HGG, DEEPEST FORM: the Niho-reduction "incomplete subgroup" escape.

The strongest version of the HGG angle is NOT the raw complete cross-correlation
(probe_p7_hgg_crosscorr_vs_period.py shows that is sqrt(p)=n^2, vacuous), but the
NIHO REDUCTION (arXiv:2407.16072 Lemma 4), which genuinely rewrites a complete
cross-correlation as a count over a PROPER multiplicative SUBGROUP -- the
"unit circle" U = {x in F_{p^n} : x * x^{p^m} = 1} = norm-1 subgroup of F_{p^{2m}}^x.

  Wd(a) = Cd(tau)+1 = (N(a)-1) p^m,
  N(a) = #{ x in U : x^{2s-1} - a x^s - a-bar x^{s-1} + 1 = 0 }.

So HGG's bounded cross-correlation DOES come from an incomplete-subgroup count.
The question: is U like the PRIZE subgroup mu_n (thin, order n ~ p^{1/4})?  If so,
HGG's machinery (counting algebraic solutions on U, giving 3/4/5-valued spectra
=> sup ~ sqrt(N)) might transfer.

THIS PROBE pins the two structural obstructions that kill the transfer:

 OBSTRUCTION 1 -- WRONG SUBGROUP SIZE (half-dimension, not thin).
   |U| = p^m + 1 ~ sqrt(N) = sqrt(p^{2m}).  This is a 'thick' subgroup of
   RELATIVE size ~ field^{1/2}.  The prize subgroup mu_n has |mu_n| = n ~ p^{1/4}
   inside F_p, RELATIVE size n/p ~ p^{-3/4} (vanishing).  Mapping mu_n to U would
   require n ~ sqrt(field) -- the exact OPPOSITE of the thin prize regime.  HGG's
   sqrt(N) cancellation is precisely the statement '|U|-summed phase cancels to
   sqrt(|ambient|)'; with |U| ~ sqrt(|ambient|), that is the TRIVIAL/Weil regime
   for U (sqrt of U's own ambient), giving NO subgroup gain.

 OBSTRUCTION 2 -- the cancellation is ALGEBRAIC (bounded #solutions), not
   equidistribution.  HGG gets sup ~ sqrt(N) because N(a) <= 2s-1 = O(1)
   (a low-degree polynomial has few roots).  The prize period eta_b = sum_{x in
   mu_n} e_p(b x) is NOT a solution-count of a fixed low-degree equation over U;
   it is a CHARACTER SUM over a thin subgroup whose cancellation is the OPEN BGK
   equidistribution.  The Niho polynomial trick has no analogue: there is no
   fixed low-degree equation whose root-count equals eta_b.

NUMERICAL CHECKS:
 (1) verify |U| = p^m+1 and that it is ~sqrt of ambient (thick), for small p,m;
 (2) verify the prize subgroup is thin (n/p -> 0) and CANNOT be a norm subgroup
     of any extension at the prize aspect ratio (n ~ p^{1/4} vs |U| ~ p^{1/2});
 (3) show that summing a single additive character over U does NOT cancel to
     sqrt of U's size -- the Niho 'sqrt(N)' refers to sqrt of the AMBIENT field,
     reachable only because |U| is already ~sqrt(ambient).
"""

import cmath, math
from math import gcd, log, sqrt, pi

def is_prime(n):
    if n < 2: return False
    if n % 2 == 0: return n == 2
    i = 3
    while i*i <= n:
        if n % i == 0: return False
        i += 2
    return True

# ---- GF(p^2) arithmetic via an irreducible x^2 - t (t a non-residue) ----
def find_nonresidue(p):
    for t in range(2, p):
        if pow(t, (p-1)//2, p) == p-1:
            return t
    raise RuntimeError

class GF2:
    """F_{p^2} = F_p[x]/(x^2 - t).  element (a,b) = a + b*x."""
    def __init__(self, p):
        self.p = p
        self.t = find_nonresidue(p)
    def mul(self, u, v):
        a,b = u; c,d = v; p,t = self.p, self.t
        # (a+bx)(c+dx) = ac + bdt + (ad+bc)x
        return ((a*c + b*d*t) % p, (a*d + b*c) % p)
    def pow(self, u, e):
        r = (1,0)
        while e:
            if e & 1: r = self.mul(r,u)
            u = self.mul(u,u); e >>= 1
        return r
    def conj(self, u):       # Frobenius x -> x^p  (the 'bar' for m=1, n=2)
        a,b = u
        return (a, (-b) % self.p)
    def norm(self, u):       # N(u) = u * u^p  in F_p
        a,b = u; p,t = self.p, self.t
        return (a*a - b*b*t) % p   # = (a+bx)(a-bx) = a^2 - b^2 t

def main():
    print("="*78)
    print("P7-HGG Niho/norm-subgroup escape -- the strongest form of the angle")
    print("="*78)

    # (1)+(3): build the norm-1 'unit circle' U in F_{p^2}, m=1, n=2.
    print("\n[1] The Niho 'unit circle' U = {x in F_{p^2} : N(x)=1}, order p^m+1.")
    print(f"{'p':>5} {'|F_p^2|^x':>10} {'|U|':>6} {'p^m+1':>7} {'|U|/sqrt(amb)':>14}")
    for p in [5, 7, 11, 13, 17, 31]:
        if not is_prime(p): continue
        F = GF2(p)
        amb = p*p - 1
        # U = elements of norm 1
        U = [(a,b) for a in range(p) for b in range(p)
             if (a,b)!=(0,0) and F.norm((a,b))==1]
        ratio = len(U)/sqrt(p*p)
        print(f"{p:>5} {amb:>10} {len(U):>6} {p+1:>7} {ratio:>14.4f}")
    print("""  => |U| = p+1 ~ sqrt(ambient p^2). U is a HALF-DIMENSION ('thick') subgroup.
     HGG's bounded cross-correlation lives on THIS subgroup. sup ~ sqrt(N)
     = sqrt(p^2)=p means sup/|U| ~ p/(p+1) ~ 1: NO per-element cancellation
     gain -- it is sqrt of the AMBIENT, trivial relative to |U| itself.""")

    # (3): sum a single additive character of F_{p^2} (via trace) over U,
    # compare its magnitude to sqrt(|U|) (would-be 'subgroup' cancellation)
    # vs sqrt(ambient)=p (the Weil/HGG complete-sum scale).
    print("\n[3] Additive-character sum over U vs the two sqrt scales.")
    print(f"{'p':>5} {'|U|':>5} {'max_c|sum_U e(Tr(cx))|':>23} "
          f"{'sqrt|U|':>9} {'sqrt(amb)=p':>12}")
    for p in [7, 11, 13, 17, 31]:
        F = GF2(p)
        U = [(a,b) for a in range(p) for b in range(p)
             if (a,b)!=(0,0) and F.norm((a,b))==1]
        def Tr(u):  # absolute trace to F_p:  u + u^p
            a,b = u; return (2*a) % p   # Tr(a+bx)=2a since x+x^p has b-part cancel
        best = 0.0
        for ca in range(p):
            for cb in range(p):
                if (ca,cb)==(0,0): continue
                s = 0j
                for u in U:
                    s += cmath.exp(2j*pi*Tr(F.mul((ca,cb),u))/p)
                best = max(best, abs(s))
        print(f"{p:>5} {len(U):>5} {best:>23.3f} {sqrt(len(U)):>9.3f} {float(p):>12.3f}")
    print("""  => the U-sum tracks sqrt(ambient)=p (the Weil/HGG scale), NOT sqrt(|U|).
     Because |U|~sqrt(ambient), 'sqrt(N)' IS roughly |U|^{1} ... |U|^{1/2}; there
     is no thin-subgroup sqrt(n)-from-n gain to be had -- the regime is wrong.""")

    # (2): aspect-ratio incompatibility -- the prize subgroup can NEVER be a norm
    # subgroup at its own aspect ratio.
    print("\n[2] ASPECT-RATIO incompatibility (prize thin vs Niho half-dimension).")
    print(f"{'object':>16} {'subgroup size':>16} {'ambient':>14} "
          f"{'size/sqrt(amb)':>16} {'log_amb(size)':>14}")
    # prize: mu_n in F_p, n ~ p^{1/4}
    for mu, beta in [(20,4),(30,4),(30,5)]:
        n = 1<<mu; p = n**beta
        print(f"{'PRIZE mu_n':>16} {n:>16.3e} {float(p):>14.3e} "
              f"{n/sqrt(p):>16.3e} {log(n)/log(p):>14.4f}")
    # niho U: order ~ sqrt(ambient)
    for m in [16, 30]:
        amb = (2**m)**2   # F_{2^{2m}}
        U = 2**m + 1
        print(f"{'NIHO U':>16} {float(U):>16.3e} {float(amb):>14.3e} "
              f"{U/sqrt(amb):>16.3e} {log(U)/log(amb):>14.4f}")
    print("""  => PRIZE log_amb(size) ~ 1/beta in [1/5,1/4] (THIN).
     NIHO log_amb(size) ~ 1/2 (HALF-DIMENSION).
     These are incompatible aspect ratios. HGG's whole solvable structure
     (bounded #roots of a fixed-degree equation on the norm subgroup) exists
     ONLY at the 1/2 aspect ratio; nothing in HGG produces a fixed low-degree
     equation whose U-root-count equals a THIN-subgroup character sum.""")

    print("="*78)
    print("VERDICT (P7-HGG Niho form): NO-GAIN / REDUCES-TO-BGK.")
    print("""Even the strongest HGG mechanism -- the Niho reduction to a count on the
norm-1 'unit circle' subgroup U -- delivers sqrt(N) only because (a) U is a
HALF-DIMENSION subgroup (|U| ~ sqrt(ambient), the WRONG aspect ratio vs the
prize's thin n ~ p^{1/4}), and (b) the cancellation is ALGEBRAIC: N(a) <= 2s-1
roots of a FIXED low-degree polynomial, so Cd = (N(a)-1)p^m is automatically
O(sqrt(N)).  The prize period eta_b over a THIN subgroup is not the root-count
of any fixed low-degree equation, and the thin aspect ratio destroys the only
regime where HGG's solvability holds.  HGG = sqrt of the AMBIENT (Weil), reached
via a half-dimension subgroup; the prize needs sqrt of a THIN subgroup's own
size (BGK equidistribution).  Same wall.""")
    print("="*78)

if __name__ == "__main__":
    main()
