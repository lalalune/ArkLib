"""
Probe the FULL real orbit decomposition of the pointwise-autocorrelation shift-sum under inversion.

Base (proven in-tree): ||eta_b||^2 = |mu_n| + S(b), S(b) = sum_{zeta != 1} eta_{b(zeta-1)}.
Involution zeta<->zeta^{-1} on mu_n\{1}:
  - off-diagonal orbits {zeta, zeta^{-1}} (zeta != +-1): eta_{b(zeta-1)} + eta_{b(zeta^{-1}-1)}
       = eta_{b(zeta-1)} + conj(eta_{b(zeta-1)}) = 2*Re(eta_{b(zeta-1)}).
  - fixed point zeta = -1 (n even): eta_{-2b} (REAL singleton).
So:  ||eta_b||^2 = |mu_n| + eta_{-2b} + 2 * sum_{orbit reps zeta, zeta != +-1} Re(eta_{b(zeta-1)}).

Verify EXACT over C on PROPER thin mu_n (m=(p-1)/n >= 4, n=2^a, never n=q-1).
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
    p = lo + ((1 - lo) % n)
    if p <= lo: p += n
    while True:
        if is_prime(p) and (p-1)//n >= 4:
            return p
        p += n

def ep(t,p): return cmath.exp(2j*math.pi*((t)%p)/p)

cases = [(8,4),(8,5),(16,4),(16,5),(32,4),(64,4)]
print("=== FULL inversion orbit decomposition of ||eta_b||^2 ===")
allpass = True
for (n,beta) in cases:
    p = find_prime(n,beta); m=(p-1)//n
    assert m>=4 and n != p-1
    g = primitive_root(p)
    sub = [pow(g, m*k, p) for k in range(n)]   # mu_n
    subset = set(sub)
    # worst b
    maxim=0.0; worstb=1
    for b in range(1,min(p,400)):
        s = sum(ep(b*x,p) for x in sub)
        if abs(s)>maxim: maxim=abs(s); worstb=b
    def eta(b):
        return sum(ep(b*x,p) for x in sub)
    worst_err = 0.0
    for b in [worstb,1,2,3,max(1,worstb//2)]:
        lhs = abs(eta(b))**2
        # build orbits of inversion on mu_n\{1}
        seen=set(); pair_re_sum=0.0; fixed=0.0
        for zeta in sub:
            if zeta==1: continue
            if zeta in seen: continue
            zinv = pow(zeta, p-2, p)  # inverse mod p
            if zinv==zeta:
                # fixed point (zeta=-1 for n even); contributes real eta_{b(zeta-1)}
                c = (b*((zeta-1)%p))%p
                fixed += eta(c).real
                seen.add(zeta)
            else:
                c = (b*((zeta-1)%p))%p
                pair_re_sum += eta(c).real
                seen.add(zeta); seen.add(zinv)
        rhs = n + fixed + 2*pair_re_sum
        err = abs(lhs-rhs)
        worst_err = max(worst_err, err)
    status="PASS" if worst_err<1e-6 else "FAIL"
    if worst_err>=1e-6: allpass=False
    print(f"n={n} beta~{beta} p={p} m={m} worstb={worstb} |eta|max={maxim:.3f} decomp max|err|={worst_err:.2e} {status}")
print("ALLPASS" if allpass else "SOMEFAIL")
