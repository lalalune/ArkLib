import math
# Dyadic/self-improving no-go: can M_r <= Gaussian be bootstrapped from a base sup-norm bound B<=B0?
# Split b by |eta_b|: small part (<=T) bounded by L^2; large part (#<=pn/T^2) bounded by B0^{2r}.
# M_r <= T^{2r-2}*(p n) + (p n / T^2) * B0^{2r}.  Optimize T; ask: is result <= Gaussian p (2r-1)!! n^r ?
def double_fact(m):
    r=1;k=m
    while k>0: r*=k;k-=2
    return r
def viable(logp, logn, r, logB0):  # all in log2; logB0 = log2 of base sup-norm bound
    # work in log2. small part exponent best at T^2 ~ (r-1 choose..) -> just scan T
    best=math.inf
    for logT2 in [x*0.25 for x in range(0, int(2*logp*4)+1)]:  # logT2 = log2(T^2)
        logsmall = (r-1)*logT2 + logp + logn         # T^{2r-2} p n
        loglarge = logp + logn - logT2 + 2*r*logB0   # (pn/T^2) B0^{2r}
        logM = max(logsmall, loglarge) + (1 if abs(logsmall-loglarge)<1 else 0)
        best=min(best, logM)
    logGauss = logp + math.log2(double_fact(2*r-1)) + r*logn
    return best, logGauss, best<=logGauss

print("Prize regime: log2 p=192, log2 n=30, r=ln p=133")
logp, logn = 192.0, 30.0
r=int(math.log(2**192))  # ln p
for label,logB0 in [("trivial Weil  B<=sqrt(p)", 192/2),
                    ("subgroup      B<=sqrt(np)", (30+192)/2),
                    ("HALF-WAY      B<=p^{1/4}n^{1/2}", 192/4+30/2),
                    ("PRIZE TARGET  B<=sqrt(2n ln p)", 0.5*math.log2(2*(2**30)*math.log(2**192)))]:
    best,logG,ok = viable(logp,logn,r,logB0)
    print(f"  base {label:34s} (log2 B0={logB0:6.2f}): bootstrap M_r ~2^{best:7.1f} vs Gaussian 2^{logG:7.1f}  -> {'CLOSES' if ok else 'FAILS'}")
print("\n=> bootstrap closes ONLY if you ALREADY assume B near the target. No sub-sqrt(p) base case exists.")
