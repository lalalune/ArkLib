# Probe: E3(mu_n) over F_p at prize scale p ~ n^4 vs char-0 count-balanced value 15n^3-45n^2+40n.
# mu_n = unique subgroup of order n=2^a in F_p^* (needs n | p-1).
# E3 = #{(x1..x6) in mu_n^6 : x1+x2+x3+x4+x5+x6 = 0 in F_p}.
# char-0 value (count-balanced solutions only) = 15n^3-45n^2+40n.
# If char-p E3 > char-0 value => EXTRA char-p relations => t3=3 near-Sidon input FAILS at this p.
import itertools, sys

def find_prime_with_subgroup(n, beta_target):
    # want p prime, n | p-1, p ~ n^beta_target. search p = k*n+1.
    import sympy
    target = int(round(n**beta_target))
    # search around target for p = k*n+1 prime
    k0 = max(1, target // n)
    for dk in range(0, 20000):
        for k in (k0+dk, k0-dk):
            if k < 1: continue
            p = k*n + 1
            if p > 2 and sympy.isprime(p):
                return p
    return None

def subgroup_of_order(n, p):
    # find generator g of full group, then h = g^((p-1)/n) generates order-n subgroup
    import sympy
    g = sympy.primitive_root(p)
    h = pow(g, (p-1)//n, p)
    sub = []
    x = 1
    for _ in range(n):
        sub.append(x)
        x = (x*h) % p
    return sub

def e3_count(sub, p):
    n = len(sub)
    # count 6-tuples summing to 0 mod p. Use convolution on sum distribution of 3-tuples? 
    # E3 = sum over s of (#3-tuples summing to s)*(#3-tuples summing to -s)... but that's for x1+x2+x3 = -(x4+x5+x6).
    # Actually sum of 6 = 0 <=> (x1+x2+x3) = -(x4+x5+x6). So E3 = sum_s T3(s)*T3(-s) where T3(s)=#3-tuples sum=s.
    from collections import defaultdict
    T3 = defaultdict(int)
    for a in sub:
        for b in sub:
            ab = (a+b)%p
            for c in sub:
                T3[(ab+c)%p]+=1
    tot = 0
    for s,cnt in T3.items():
        tot += cnt * T3[(-s)%p]
    return tot

import sympy
for a in [2,3,4]:
    n = 2**a
    for beta in [4.0, 5.0]:
        p = find_prime_with_subgroup(n, beta)
        if p is None: 
            print(f"n={n} beta={beta}: no prime found"); continue
        sub = subgroup_of_order(n,p)
        assert len(sub)==n
        # sanity: not n=q-1 (full group). p-1 must be >> n
        if p-1 == n:
            print(f"n={n} p={p}: SKIP full group"); continue
        charp = e3_count(sub,p)
        char0 = 15*n**3 - 45*n**2 + 40*n
        beta_actual = (p.bit_length()-1)/ (a)  # rough log_n p
        excess = charp - char0
        print(f"n={n:3d} p={p:8d} (p~n^{__import__('math').log(p,n):.2f}) | E3_charp={charp:8d} | char0={char0:8d} | excess={excess:+d} | ratio={charp/char0:.4f}")
