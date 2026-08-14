# PROBE: relationship between the I031 SubGaussianTailBound (finset tail-count Prop)
# and the #407 pointwise ConstantIndexSubGaussianPeriodBound (max period bound).
# Question: does pointwise M <= sqrt(2 n log m) IMPLY the tail Prop
#   #{v in S : v > s} <= m * exp(-s^2/(2C))  for all s>0, for C = n?
# And what IS the actual empirical tail of {||eta_b||} for thin proper mu_n?
# EXACT F_p, PROPER thin mu_n (n=2^a), p == 1 mod n, (p-1)/n >= 2, NEVER n=q-1.
import cmath, math

def primitive_root(p):
    if p==2: return 1
    fac=set(); pm=p-1; d=2
    while d*d<=pm:
        if pm%d==0:
            fac.add(d)
            while pm%d==0: pm//=d
        d+=1
    if pm>1: fac.add(pm)
    for g in range(2,p):
        if all(pow(g,(p-1)//f,p)!=1 for f in fac): return g
    return None

def eta_norms(p, n):
    # mu_n = unique order-n subgroup; m = (p-1)//n orbit count (index)
    g = primitive_root(p)
    m = (p-1)//n
    # mu_n generator = g^m
    h = pow(g, m, p)
    mun = set()
    x=1
    for _ in range(n):
        mun.add(x); x=(x*h)%p
    mun=sorted(mun)
    w = cmath.exp(2j*math.pi/p)
    norms=[]
    for b in range(1,p):  # nonzero freqs
        s=sum(w**((b*y)%p) for y in mun)
        norms.append(abs(s))
    return norms, m

def tail_check(p,n):
    norms,m = eta_norms(p,n)
    # distinct magnitudes (periodMagnitudes is the IMAGE finset)
    # round to dedupe floating
    distinct = sorted(set(round(v,7) for v in norms))
    M = max(norms)
    C = n  # variance proxy
    sqrt_bound = math.sqrt(2*n*math.log(m)) if m>1 else float('inf')
    # check pointwise
    pointwise_ok = M <= sqrt_bound + 1e-9
    # check the tail Prop on the DISTINCT-magnitude finset (that's what periodMagnitudes is)
    worst_violation = None
    for s_i in [v*(1-1e-9) for v in distinct] + [0.5*sqrt_bound, 0.9*sqrt_bound]:
        if s_i<=0: continue
        cnt = sum(1 for v in distinct if s_i < v)
        rhs = m*math.exp(-(s_i**2)/(2*C))
        if cnt > rhs + 1e-9:
            viol = cnt - rhs
            if worst_violation is None or viol>worst_violation[0]:
                worst_violation=(viol, s_i, cnt, rhs)
    return M, sqrt_bound, pointwise_ok, len(distinct), m, worst_violation

print(f"{'p':>6} {'n':>3} {'m':>5} {'M':>8} {'sqrt(2nlnm)':>11} {'PWok':>5} {'#distinct':>9} {'tailViol(cnt-rhs,s)':>22}")
for (p,n) in [(17,4),(41,4),(73,8),(97,8),(193,8),(337,16),(521,8),(257,16),(641,16),(769,16),(4129,16)]:
    if (p-1)%n!=0 or (p-1)//n<2: continue
    M,sb,pw,nd,m,wv = tail_check(p,n)
    wvs = "none" if wv is None else f"{wv[0]:.2f}@s={wv[1]:.2f}(c={wv[2]},r={wv[3]:.2f})"
    print(f"{p:>6} {n:>3} {m:>5} {M:>8.3f} {sb:>11.3f} {str(pw):>5} {nd:>9} {wvs:>22}")
