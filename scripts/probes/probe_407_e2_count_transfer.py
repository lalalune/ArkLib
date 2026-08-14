# Verify the AGGREGATE count-transfer theorem is non-vacuous and the equality is genuine:
# over the bounded-width family {U subset range(2^k) : |U| <= w}, the count of mod-p e2=0 sets
# EQUALS the count of char-0 e2=0 sets, for p above the uniform threshold (w^2+w)^{2^{k-1}}.
# Also report the actual char-0 count (should be >0 and q-independent) so the theorem isn't vacuous.
import itertools, cmath, sympy, random

def e2_complex(U, k):
    z = cmath.exp(2j*cmath.pi/(2**k))
    pts = [z**i for i in U]
    e1 = sum(pts); p2 = sum(x*x for x in pts)
    return (e1*e1 - p2)/2

def e2cond_modp(U, g, p):
    e1 = sum(pow(g,i,p) for i in U) % p
    p2 = sum(pow(g,2*i,p) for i in U) % p
    return (e1*e1 - p2) % p == 0

def e2cond_c(U, k):
    return abs(e2_complex(U,k)) < 1e-9

def primitive_2k_root(p,k):
    order=2**k
    if (p-1)%order!=0: return None
    h=(p-1)//order
    for _ in range(400):
        a=random.randrange(2,p-1); g=pow(a,h,p)
        if pow(g,order,p)==1 and pow(g,order//2,p)!=1: return g
    return None

random.seed(11)
for k in [2,3,4]:
    nn=2**k
    for w in [2,3,4,nn]:
        Tunif=(w*w+w)**(2**(k-1))
        # char-0 count over the bounded-width family
        c0count=sum(1 for r in range(2,w+1) for U in itertools.combinations(range(nn),r) if e2cond_c(U,k))
        # pick a prime above the uniform threshold (capped feasibility)
        target=min(Tunif, 2_000_003)
        p=sympy.nextprime(target)
        while (p-1)%nn!=0: p=sympy.nextprime(p)
        g=primitive_2k_root(p,k)
        above = p > Tunif
        cpcount=sum(1 for r in range(2,w+1) for U in itertools.combinations(range(nn),r) if e2cond_modp(U,g,p))
        eq = (c0count==cpcount)
        print(f"k={k} n={nn} w={w} Tunif={Tunif} p={p} above_thr={above} char0_count={c0count} modp_count={cpcount} EQUAL={eq}")
