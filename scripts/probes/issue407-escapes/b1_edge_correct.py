import math

# CS25 Corollary 1: proximity gap FAILS (every lambda bad) when:
#   n(1-Hq(f/n)) + 2 + sqrt(n*Hq(f/n) - f) <= k <= n - f - 2
# Here u^(1) = eval(x^k) = THE LOW MONOMIAL (settles comment 100 vs 125: it's the low one).
# Hq = q-ary entropy. The failure LOWER edge in delta=f/n:
#   k >= n(1 - Hq(delta)) + lower-order   <=>   rho >= 1 - Hq(delta) + o(1)
#   <=>  Hq(delta) >= 1 - rho   <=>  delta >= delta_LDcap (list-dec capacity radius).
# So CS25 failure starts EXACTLY at list-decoding capacity Hq(delta)=1-rho.
# Below that (delta < delta_LDcap) CS25 does NOT force failure.
#
# Compare delta_LDcap vs Kambire edge vs (1-rho). The question: is Kambire BELOW
# delta_LDcap (=> floor consistent, B1 alive in window) or ABOVE (=> B1 dead)?

def Hq(x,q):
    if x<=0 or x>=1: return 0.0
    lq=math.log(q)
    return (x*math.log(q-1)-x*math.log(x)-(1-x)*math.log(1-x))/lq
def H2(x):
    if x<=0 or x>=1: return 0.0
    return -x*math.log2(x)-(1-x)*math.log2(1-x)

def delta_ldcap(rho,q):
    # solve Hq(delta)=1-rho
    lo,hi=0.0,1-1e-9
    for _ in range(200):
        mid=(lo+hi)/2
        if Hq(mid,q)<1-rho: lo=mid
        else: hi=mid
    return (lo+hi)/2

def delta_cs25_exact(n,rho,q):
    # smallest delta with n(1-Hq(d))+2+sqrt(max(n*Hq(d)*ln stuff... use H2 form per proof))
    # Use the EXACT corollary inequality with q-ary entropy:
    #   k >= n(1-Hq(d)) + 2 + sqrt(n*Hq(d) - f)   AND  k <= n - f - 2
    k=rho*n
    d=0.0
    while d<1-rho:
        f=d*n
        H=Hq(d,q)
        nHmf = n*H - f
        if nHmf < 0: 
            d+=0.0005; continue
        lo = n*(1-H)+2+math.sqrt(nHmf)
        hi = n-f-2
        if lo<=k<=hi:
            return d
        d+=0.0005
    return None

print(f"{'mu':>3} {'rho':>6} {'b':>2} | {'Johnson':>8} {'Kambire':>8} {'LDcap':>8} {'CS25fail':>9} | {'Kam<LDcap?':>10} {'Kam<CS25?':>9}")
for mu in [16,20,24,30]:
    n=2**mu
    for rho in [0.5,0.25,0.125]:
        beta=4; q=n**beta
        johnson=1-math.sqrt(rho)
        kambire=1-rho-H2(rho)/(beta*mu)
        ldc=delta_ldcap(rho,q)
        cs=delta_cs25_exact(n,rho,q)
        kam_lt_ldc = kambire < ldc
        kam_lt_cs = (cs is not None) and (kambire < cs)
        print(f"{mu:>3} {rho:>6} {beta:>2} | {johnson:>8.4f} {kambire:>8.4f} {ldc:>8.4f} {str(round(cs,4)) if cs else 'NA':>9} | {str(kam_lt_ldc):>10} {str(kam_lt_cs):>9}")

print()
print("KEY: 1-rho (capacity) vs LDcap (Hq(d)=1-rho) vs Kambire:")
for mu in [24]:
    n=2**mu; beta=4; q=n**beta
    for rho in [0.5,0.25,0.125]:
        print(f"  rho={rho}: 1-rho={1-rho:.4f}  LDcap={delta_ldcap(rho,q):.4f}  Kambire={1-rho-H2(rho)/(beta*mu):.4f}  Johnson={1-math.sqrt(rho):.4f}")
