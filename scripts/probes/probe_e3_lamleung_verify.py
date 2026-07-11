import itertools, cmath, math
from collections import Counter

# The mathematical CORE is: for 2^mu-th roots of unity, 
#   sum_{i} y_i = 0  (y_i in mu_n, n=2^mu)  <=>  class-balanced.
# 
# (<=) balance => zero: trivial, since balanced means we can pair each + with a - in same
#      class, and z + (-z) = 0. Pure algebra, no field theory. SOLID.
#
# (=>) zero => balance: this is LAM-LEUNG specialized. The theorem (Lam-Leung 2000):
#      if sum of N-th roots of unity = 0 with nonneg integer coefficients, then the
#      coefficient vector is a nonneg-integer combination of the "basic relations"
#      = full sets of p-th roots for primes p | N. For N = 2^mu, the ONLY prime is 2,
#      and the basic relation is {z, -z} (sum of both square-roots-of-z^2... i.e. z + (-z)).
#      So any vanishing nonneg combination is a sum of antipodal pairs => class-balanced.
#
# Let me verify (=>) holds at n=16 exhaustively over SMALL support and confirm no 
# counterexample with up to 6 terms (which is all we need for r=3).

def mu_n(n):
    return [cmath.exp(2j*math.pi*k/n) for k in range(n)]

def check_zero_implies_balance(n, maxterms=6):
    pts=mu_n(n); half=n//2
    antip=lambda i:(i+half)%n
    def classsign(i):
        ai=antip(i)
        return (i,+1) if i<ai else (ai,-1)
    bad=0
    # all multisets of size exactly maxterms (with repetition) over n symbols summing to 0
    for combo in itertools.combinations_with_replacement(range(n), maxterms):
        s=sum(pts[i] for i in combo)
        if abs(s)<1e-7:
            net=Counter()
            for i in combo:
                c,sg=classsign(i); net[c]+=sg
            if not all(v==0 for v in net.values()):
                bad+=1
                print("  COUNTEREXAMPLE:", combo)
    return bad

for n in [4,8,16,32]:
    bad=check_zero_implies_balance(n,6)
    print(f"n={n}: zero=>balance counterexamples among 6-multisets = {bad}")
