import cmath, math
# Faithful prize regime: p PRIME, n=2^mu | p-1, p >> n^3, m=(p-1)/n > 1, NEVER n=p-1.
def is_prime(x):
    if x<2: return False
    i=2
    while i*i<=x:
        if x%i==0: return False
        i+=1
    return True

def find_prime(n, beta):
    # want p ~ n^beta, p prime, p = 1 mod n
    target = int(n**beta)
    # search p = 1 + k*n >= target
    k = max(1, (target-1)//n)
    while True:
        p = 1 + k*n
        if p > target and is_prime(p) and (p-1)//n > 1:
            return p
        k += 1

def gen(p):
    # find a multiplicative generator
    fac = []
    x = p-1; d=2
    while d*d<=x:
        if x%d==0:
            fac.append(d)
            while x%d==0: x//=d
        d+=1
    if x>1: fac.append(x)
    for g in range(2,p):
        if all(pow(g,(p-1)//q,p)!=1 for q in fac):
            return g
    return None

def subgroup(p, n):
    g = gen(p)
    h = pow(g, (p-1)//n, p)  # generator of mu_n
    S = []
    x = 1
    for _ in range(n):
        S.append(x); x = x*h % p
    return S, g

def M_and_argmax(p, n):
    S,g = subgroup(p,n)
    best = 0; bestb=None
    for b in range(1,p):
        s = sum(cmath.exp(2j*math.pi*(b*x % p)/p) for x in S)
        a = abs(s)
        if a > best:
            best=a; bestb=b
    return best, bestb, S, g

for (n,beta) in [(8,4),(16,4),(32,4)]:
    p = find_prime(n,beta)
    M,bstar,S,g = M_and_argmax(p,n)
    floor = math.sqrt(n*math.log(p/n))
    # multiplication-by-2 orbit of b* in F_p^*: b*, 2 b*, 4 b*, ... 
    # Note |eta_{2b}| relation: 2b acts; check orbit of dilation by elements of mu_n on b (gives same |eta|)
    print(f"n={n} p={p} m={(p-1)//n} M={M:.4f} floor=sqrt(n log p/n)={floor:.4f} M/floor={M/floor:.4f} b*={bstar}")
