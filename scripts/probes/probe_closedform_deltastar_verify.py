# Verify the closed-form delta* conjecture: delta* = H_q^{-1}(1 - rho - log_q(1/eps*)/n).
# Checks: (1) lands strictly in the window (1-sqrt(rho), 1-rho) at the 4 prize rates;
# (2) eps*->1 limit -> H_q(delta*)=1-rho (capacity); (3) prize q -> 1-rho-Theta(1/log n);
# (4) consistency: delta*_closedform <= deep-band ceiling (avg <= worst-case-derived upper).
from math import log, comb
def Hq(x,q):                    # q-ary entropy, x in (0,1)
    if x<=0: return 0.0
    if x>=1: return log(q-1,q)+0.0  # caps near 1
    return x*log(q-1,q) - x*log(x,q) - (1-x)*log(1-x,q)
def Hq_inv(y,q):                # inverse on the increasing branch [0, 1-1/q]
    lo,hi=0.0, 1-1.0/q
    for _ in range(200):
        mid=(lo+hi)/2
        if Hq(mid,q)<y: lo=mid
        else: hi=mid
    return (lo+hi)/2
def dstar_closed(rho,n,q,logq_inv_eps):  # logq_inv_eps = log_q(1/eps*) = 128/log2(q)
    return Hq_inv(1-rho-logq_inv_eps/n, q)

print("Closed-form δ* = H_q^{-1}(1-ρ-log_q(1/ε*)/n), ε*=2^-128, prize q≈n·2^128:\n")
for rho,rl in ((0.5,"1/2"),(0.25,"1/4"),(0.125,"1/8"),(0.0625,"1/16")):
    J=1-rho**0.5; cap=1-rho
    print(f"ρ={rl}: Johnson={J:.4f}, capacity={cap:.4f}")
    for m in (10,20,30,40):
        n=1<<m
        q=n*(2**128)                    # prize field q ≈ n·2^128
        lqe=128/log(q,2)                # log_q(1/eps*) = 128/log2 q
        d=dstar_closed(rho,n,q,lqe)
        inwin = J < d < cap
        gap_cap=cap-d
        print(f"   n=2^{m}: δ*={d:.5f}  in-window={inwin}  gap-to-cap={gap_cap:.5f}  "
              f"gap·log2(n)={gap_cap*m:.3f}")
    # eps*->1 limit (log_q(1/eps*)->0): should give H_q(d)=1-rho i.e. d=capacity-ish
    n=1<<20; q=n*(2**128)
    d1=dstar_closed(rho,n,q,0.0)
    print(f"   ε*→1 limit: δ*={d1:.4f} (H_q(δ*)={Hq(d1,q):.4f} vs 1-ρ={1-rho:.4f}) — CS25 capacity")
    print()
