"""
Probe: the inversion-involution FIXED POINT zeta=-1 (n even) gives an EXACTLY REAL
difference-set period eta_{b(zeta-1)} = eta_{-2b}, an exact REAL singleton in the shift-sum S(b).

For zeta=-1 in mu_n: b(zeta-1) = -2b, and inversion sends zeta=-1 to itself ((-1)^{-1}=-1),
so by eta_invShift_eq_conj: eta_{-2b} = conj(eta_{-2b}) => eta_{-2b} is REAL.

Verify (exact over C, proper thin 2-power mu_n, m=(p-1)/n >= 4, NEVER n=q-1):
 1. eta_{-2b} is exactly real (|im| ~ 0) for the worst b and several b.
 2. CONTROL (rule 3): a random non-subgroup thin set S of same size does NOT force eta real.
"""
import cmath, math, random

def is_prime(p):
    if p < 2: return False
    for q in (2,3,5,7,11,13,17,19,23,29,31,37):
        if p % q == 0: return p == q
    d = p-1; r = 0
    while d % 2 == 0: d//=2; r+=1
    for a in (2,3,5,7,11,13,17,19,23,29,31,37):
        x = pow(a,d,p)
        if x==1 or x==p-1: continue
        for _ in range(r-1):
            x = x*x % p
            if x==p-1: break
        else:
            return False
    return True

def primitive_root(p):
    phi = p-1; x = phi; fac = []; d = 2
    while d*d <= x:
        if x % d == 0:
            fac.append(d)
            while x % d == 0: x//=d
        d += 1
    if x>1: fac.append(x)
    for g in range(2,p):
        if all(pow(g,(p-1)//q,p)!=1 for q in fac):
            return g
    return None

def find_prime(n, beta_target):
    lo = max(int(n**beta_target), 4*n+1)
    p = lo + ((1 - lo) % n)  # make p ≡ 1 mod n
    if p <= lo: p += n
    while True:
        if is_prime(p) and (p-1)//n >= 4:
            return p
        p += n

def eta_subgroup(p, n, b, g, m):
    mun = [pow(g, m*k, p) for k in range(n)]
    return sum(cmath.exp(2j*math.pi*((b*x) % p)/p) for x in mun)

def eta_set(p, S, b):
    return sum(cmath.exp(2j*math.pi*((b*x) % p)/p) for x in S)

cases = [(8,4),(8,5),(16,4),(16,5),(32,4),(64,4)]
print("=== FIXED-POINT zeta=-1 gives REAL eta_{-2b} on proper thin mu_n ===")
allpass = True
for (n,beta) in cases:
    p = find_prime(n, beta)
    m = (p-1)//n
    assert m >= 4 and n != p-1
    g = primitive_root(p)
    maxim = 0.0; worstb = 1
    for b in range(1, min(p, 400)):
        s = eta_subgroup(p,n,b,g,m)
        if abs(s) > maxim:
            maxim = abs(s); worstb=b
    bad = 0
    for b in [worstb, 1, 2, 3, max(1,worstb//2)]:
        c = (-2*b) % p
        s = eta_subgroup(p,n,c,g,m)
        if abs(s.imag) > 1e-6:
            bad += 1
    random.seed(n*1000+p)
    S = random.sample(range(1,p), n)
    c = (-2*worstb) % p
    sc = eta_set(p, S, c)
    ctrl_im = abs(sc.imag)
    status = "PASS" if bad==0 else "FAIL"
    if bad: allpass=False
    print(f"n={n} beta~{beta} p={p} m={m} worstb={worstb} |eta|max={maxim:.3f} | eta_-2b real-fails={bad} | CONTROL rand-set |im|={ctrl_im:.3f} {status}")
print("ALLPASS" if allpass else "SOMEFAIL")
