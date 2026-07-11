# Probe: what is the off-BGK antipodal route's base-rung list bound?
# towerDescent_saving_iff: saving on mu_{2^mu} <=> rootCount(Q, mu_{2^{mu-s}}) < deg Q
# Full telescope s=mu lands on mu_1 = {1} (one-element group).
# Question: on the one-element base group {1}, can rootCount(Q,{1}) < deg Q ever give
# a NONTRIVIAL list saving? And what does "list" mean at base rung mu_1 vs mu_2?
#
# A list of close codewords <-> agreement polynomials P with >= (k+m+1) roots in mu_n.
# At the base group mu_{2^j}, the "list" is the number of degree-<k polys agreeing on the base.
# We probe: for the antipodal (even/odd) worst word x^a+x^b (a,b odd) on mu_n,
# descend the agreement-set root count octave by octave and read the base count.

import itertools, cmath, math

def roots_of_unity(n):
    return [cmath.exp(2j*math.pi*t/n) for t in range(n)]

def agreement_poly_rootcount_on_group(coeffs_exponents, n):
    # word u(x) = sum x^e over exponents; its roots in mu_n
    mu = roots_of_unity(n)
    cnt = 0
    for z in mu:
        val = sum(z**e for e in coeffs_exponents)
        if abs(val) < 1e-9:
            cnt += 1
    return cnt

# Antipodal worst word for mu_n: x^a + x^b, a,b both odd => odd polynomial
# Descend through octaves: rootCount(Q.comp(X^{2^s}), mu_{2^mu}) = 2^s * rootCount(Q, mu_{2^{mu-s}})
# We verify the descent identity AND read the base rung (s = mu-1 -> mu_2, s=mu -> mu_1).

print("=== Antipodal tower base-rung probe ===")
for mu in [3,4,5,6]:  # n = 2^mu = 8,16,32,64
    n = 2**mu
    # odd worst word: pick a=n//2-1 (odd if n//2 even... n//2=2^{mu-1}), b=1
    # need both odd. a = n//4 *2 +1 style. Just pick small odd exps a=3,b=1.
    word = [3,1]  # x^3+x (odd polynomial: u(-x) = -x^3-x = -u)
    rc_full = agreement_poly_rootcount_on_group(word, n)
    # base: the polynomial as composition. x^3+x = x*(x^2+1). Q(y)=y*(?) not a clean comp.
    # Instead read root count at each octave subgroup mu_{2^{mu-s}}:
    print(f"n=2^{mu}={n}: rootcount(x^3+x, mu_n)={rc_full}", end="  ")
    for s in range(1,mu+1):
        sub = 2**(mu-s)
        if sub>=1:
            rc_sub = agreement_poly_rootcount_on_group(word, sub) if sub>=1 else 0
            print(f"[mu_{sub}:{rc_sub}]", end=" ")
    print()
print()
print("Base rung mu_1={1}: u(1)=#exps; for x^3+x at z=1 -> 1+1=2 !=0 so NOT a root => rootcount=0")
print("=> on mu_1, rootCount(Q,{1}) in {0,1}; deg Q >=1 => 'saving' (rc<deg) almost always TRIVIALLY holds")
print("=> the base-rung 'saving' is the degenerate fact deg>0, carrying NO list information.")
