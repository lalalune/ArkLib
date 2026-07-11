#!/usr/bin/env python3
"""
Probe: after removing the inversion fixed points 1 and -1, the off-diagonal
pointwise-autocorrelation shift spectrum has zero total imaginary part on proper
thin dyadic root subgroups, while a random same-size thin set does not.
"""
import cmath, math, random

random.seed(4443200)

def is_prime(p):
    if p < 2: return False
    if p % 2 == 0: return p == 2
    d = 3
    while d*d <= p:
        if p % d == 0: return False
        d += 2
    return True

def factor(n):
    fs=[]; d=2
    while d*d<=n:
        if n%d==0:
            fs.append(d)
            while n%d==0: n//=d
        d+=1 if d==2 else 2
    if n>1: fs.append(n)
    return fs

def primitive_root(p):
    fs=factor(p-1)
    for g in range(2,p):
        if all(pow(g,(p-1)//r,p)!=1 for r in fs): return g
    raise RuntimeError

def subgroup(p,n):
    g=primitive_root(p)
    h=pow(g,(p-1)//n,p)
    xs=[]; x=1
    for _ in range(n):
        xs.append(x); x=(x*h)%p
    assert len(set(xs))==n and x==1
    return xs

def eta(p,S,c):
    return sum(cmath.exp(2j*math.pi*((c*x)%p)/p) for x in S)

def check_case(p,n):
    G=subgroup(p,n)
    assert (p-1)//n >= 4 and n < p-1 and (p-1)%n==0
    minus_one=p-1
    assert minus_one in G and minus_one != 1
    reps=[1,2,3,5,7,11,13,17,19,23]
    max_im=0.0
    max_random=0.0
    for b in sorted(set(x%p for x in reps if x%p)):
        s=sum(eta(p,G,(b*(z-1))%p).imag for z in G if z not in (1,minus_one))
        max_im=max(max_im,abs(s))
        R=set(random.sample(range(1,p), n))
        # choose the same numeric exclusions to test the subgroup-specific cancellation is not generic
        sr=sum(eta(p,R,(b*(z-1))%p).imag for z in R if z not in (1,minus_one))
        max_random=max(max_random,abs(sr))
    return max_im,max_random

def first_prime_congruent(start,n):
    p=max(3,start)
    r=(p-1)%n
    if r: p += n-r
    if p%2==0: p += n
    while not is_prime(p): p += n
    return p

cases=[]
for n,beta in [(8,4),(8,5),(16,4),(16,5),(32,4),(32,5),(64,4)]:
    cases.append((first_prime_congruent(n**beta+1,n),n))
# structured Fermat/proth style proper cases
cases += [(257,8),(257,16),(65537,16),(65537,32),(65537,64)]

print("=== off-diagonal imaginary cancellation, proper thin mu_n only ===")
overall=0.0; random_seen=False
for p,n in cases:
    if (p-1)%n or (p-1)//n < 4 or n>=p-1: continue
    mi,mr=check_case(p,n)
    overall=max(overall,mi)
    random_seen = random_seen or mr > 1e-3
    print(f"p={p:<9} n={n:<3} m={(p-1)//n:<7} offdiag_max_im={mi:.3e} random_control_max_im={mr:.3e}")
assert overall < 1e-8, overall
assert random_seen, "random control unexpectedly always zero"
print(f"PASS max offdiag imag {overall:.3e}; random control nonzero")
