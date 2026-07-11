# Probe the EXACT signed period-power-sum <-> count identity for negation-closed mu_n.
# Gauss period eta_b = sum_{x in mu_n} e_p(b x).  Claim (the algebraic/count form of the
# thinness-essential signed sum):
#   sum_{b in F_p} eta_b^r = p * W_r,   where W_r = #{(x_1..x_r) in mu_n^r : x_1+...+x_r = 0}.
# (sum over ALL b incl 0; eta_0 = n.)  Then the NONZERO signed sum is:
#   sum_{b != 0} eta_b^r = p * W_r - n^r.
# This is the DISPROOF_LOG signed-sum-is-a-COUNT identity. Verify EXACTLY (integer eta via
# the full e_p expansion is complex; instead verify the COUNT identity directly: the LHS
# sum_b eta_b^r expands to p * #{r-tuples summing to 0} by orthogonality of additive chars.)
# We verify the integer identity sum_b eta_b^r == p * W_r using exact complex arithmetic
# rounded (eta_b are algebraic integers; eta_b^r summed over b is a rational integer).
import cmath, math, itertools
from sympy import isprime

def mu_n(p, n):
    if (p - 1) % n != 0:
        return None
    def order(a):
        o = 1; x = a % p
        while x != 1:
            x = (x * a) % p; o += 1
        return o
    for g in range(2, p):
        if order(g) == p - 1:
            h = pow(g, (p - 1) // n, p)
            s = []; x = 1
            for _ in range(n):
                s.append(x); x = (x * h) % p
            return sorted(set(s))
    return None

def eta(b, S, p):
    w = 2j * math.pi / p
    return sum(cmath.exp(w * (b * x % p)) for x in S)

def W_r(S, n, r, p):
    # exact count of r-tuples from S summing to 0 mod p
    cnt = 0
    for tup in itertools.product(S, repeat=r):
        if sum(tup) % p == 0:
            cnt += 1
    return cnt

ok = 0; tot = 0
for n in [4, 8]:
    cands = [p for p in range(n + 1, 400)
             if isprime(p) and (p - 1) % n == 0 and (p - 1) // n >= 2]
    for p in cands[:3]:
        S = mu_n(p, n)
        if S is None:
            continue
        for r in [2, 3, 4]:
            if n ** r > 6_000_000:
                continue
            lhs = sum(eta(b, S, p) ** r for b in range(p))
            lhs_int = round(lhs.real)
            Wr = W_r(S, n, r, p)
            rhs = p * Wr
            nonzero_lhs = round((lhs - eta(0, S, p) ** r).real)  # eta_0 = n
            tot += 1
            match = (abs(lhs.imag) < 1e-6 and lhs_int == rhs and nonzero_lhs == p * Wr - n ** r)
            if match:
                ok += 1
            else:
                print(f"  MISMATCH n={n} p={p} r={r}: lhs={lhs_int} p*Wr={rhs} "
                      f"nonzero={nonzero_lhs} p*Wr-n^r={p*Wr-n**r} imag={lhs.imag:.2e}")
print(f"signed period-power-sum = p*W_r identity: {ok}/{tot} EXACT matches")
