# O149: the halo mechanism verified at the norm level.
# The exotic p=193 halo subset A=(0,1,3,8,11,18,20,21) on mu_32 has
#   N(alpha) = N(beta) = 148996 = 2^2 * 193^2
# (alpha = sum zeta^i, beta = sum zeta^{3i}; norms over Q(zeta_32), computed exactly
#  in Z[zeta_32] via poly arithmetic mod x^16 + 1).
# => its halo-prime set is EXACTLY {193}: monogamous halo membership; both gap-band
#    constraint norms share the prime, explaining the joint vanishing; actual norms
#    (~2^17.2) are minuscule vs the worst-case a^phi(n) = 8^16 = 2^48.
# The per-prime halo is therefore the divisor-counting object
#   halo(p) = {S non-fiber : p | N(alpha_S) and p | N(beta_S)}
# and the one-orbit law is a statement about joint norm-divisibility multiplicity.
A = (0, 1, 3, 8, 11, 18, 20, 21)
def reduce_exp(e):
    e %= 32
    return (e, 1) if e < 16 else (e - 16, -1)
def elt_from_exps(exps):
    v = [0]*16
    for e in exps:
        i, s = reduce_exp(e); v[i] += s
    return tuple(v)
def mul(u, v):
    w = [0]*31
    for i, a in enumerate(u):
        if a:
            for j, b in enumerate(v):
                if b: w[i+j] += a*b
    out = list(w[:16])
    for i in range(16, 31): out[i-16] -= w[i]
    return tuple(out)
def conj(v, t):
    out = [0]*16
    for i, a in enumerate(v):
        if a:
            j, s = reduce_exp(i*t); out[j] += s*a
    return tuple(out)
def norm(v):
    prod = tuple([1] + [0]*15)
    for t in range(1, 32, 2): prod = mul(prod, conj(v, t))
    assert all(x == 0 for x in prod[1:])
    return prod[0]
Na = norm(elt_from_exps(A))
Nb = norm(elt_from_exps([3*i for i in A]))
assert Na == 148996 and Nb == 148996, (Na, Nb)
assert 148996 == 4 * 193 * 193
print("N(alpha) = N(beta) = 148996 = 2^2 * 193^2   [halo mechanism confirmed]")
