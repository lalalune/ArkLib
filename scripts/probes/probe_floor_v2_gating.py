import sympy, cmath, math
def musub(n,p):
    g=sympy.primitive_root(p); h=pow(g,(p-1)//n,p); return [pow(h,j,p) for j in range(n)]
def M(n,p):
    G=musub(n,p); g=sympy.primitive_root(p); m=(p-1)//n; w=2*math.pi/p; mx=0.0; rep=1
    for c in range(m):
        s=sum(cmath.exp(1j*w*((rep*x)%p)) for x in G); a=abs(s)
        if a>mx: mx=a
        rep=(rep*g)%p
    return mx
def v2(t):
    v=0
    while t%2==0: t//=2; v+=1
    return v
def prime_with_v2(v, near):
    # p = 2^v * odd + 1, prime, p>=near, minimal odd
    base=2**v; m=max(1,(near-1)//base)
    if m%2==0: m+=1
    for _ in range(2000000):
        p=base*m+1
        if sympy.isprime(p) and v2(p-1)==v: return p
        m+=2
    return None
n=64; near=60000
print(f"n={n}: floor ratio R=M/sqrt(2n ln p) vs v2(p-1), p near {near} (beta~{math.log(near)/math.log(n):.2f}):")
for v in (6,8,10,12,16):   # v2 from minimal(6) to Fermat(16)
    p=prime_with_v2(v, near)
    if not p: print(f"  v2={v}: none"); continue
    mm=M(n,p); R=mm/math.sqrt(2*n*math.log(p)); be=math.log(p)/math.log(n)
    print(f"  v2={v}: p={p:>8} beta={be:.2f} M={mm:5.1f} R={R:.3f} [{'FALSE' if R>1 else 'true'}]")

# RESULT (2026-06-14): the floor M(n)<=sqrt(2n log p) failure [c.157] is v2(p-1)-GATED, not beta-gated.
# Fixed n=64, beta~2.65, R=M/sqrt(2n ln p) vs v2(p-1):
#   v2=6(min) 0.679 | v2=8 0.700 | v2=10 0.705 | v2=12 0.747 | v2=16(Fermat 2^16+1) 1.158 FALSE
# At SAME beta, minimal-2-adic primes (v2=log2 n, index m odd = the PRIZE structure per issue-body 0)
# give R~0.67 (TRUE); only near-pure-2-power (Fermat) primes cross 1. So the proof constraint sharpens
# from "thinness-essential" to "MINIMAL-2-ADIC-essential": prize primes have v2(p-1)=log2 n (mu_n takes
# the full 2-part, m odd, DFT on coprime odd Z/m) and are robustly in the floor-TRUE zone. The bad
# (Fermat, high-v2) cases are excluded by the prize's prime structure.
