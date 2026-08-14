import cmath
import math

# Gauss-period spectrum a_b = |eta_b|^2 over b != 0, eta_b = sum_{x in mu_n} e_p(b*x).
# mu_n = 2-power subgroup of F_p^* of order n=2^a. Test what the mean-floor lower bound
# S_1/S_0 = (sum_b a_b)/(p-1) says about max_b a_b = M(n)^2, in the prize regime.
# Question: is the mean floor sub-Johnson (vacuous, << n) or does it have teeth?

def subgroup(p, n):
    # find generator g of F_p^*, take g^((p-1)/n)^k
    # naive: find element of order n
    for h in range(2, p):
        # order of h
        o = 1
        v = h % p
        while v != 1:
            v = (v * h) % p
            o += 1
            if o > p:
                break
        if o == n:
            return [pow(h, k, p) for k in range(n)]
    return None

def gauss(p, n):
    mu = subgroup(p, n)
    if mu is None:
        return None
    a = []
    for b in range(1, p):
        s = 0j
        for x in mu:
            s += cmath.exp(2j * math.pi * (b * x % p) / p)
        a.append(abs(s) ** 2)
    return a

cases = [(17, 8), (41, 8), (97, 16), (65537, 16)]  # prize-ish: large p, thin n=2^a
for p, n in cases:
    a = gauss(p, n)
    if a is None:
        print("p=%d n=%d : no subgroup" % (p, n))
        continue
    S0 = len(a)
    S1 = sum(a)
    mean = S1 / S0
    M2 = max(a)
    johnson = n  # Johnson/Weil sqrt(n) => M^2 ~ n
    print("p=%d n=%d beta=%.2f : mean=S1/S0=%.3f  max=M^2=%.3f  n(Johnson M^2)=%d  mean/n=%.4f  M^2/n=%.3f" %
          (p, n, math.log(p) / math.log(n), mean, M2, johnson, mean / n, M2 / n))
