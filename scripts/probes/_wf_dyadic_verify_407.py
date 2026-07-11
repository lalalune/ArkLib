# DECISIVE verification of the PROVEN theorem, fast (cyclic-shift characterization).
# Claim proven: For S subset Z/N (N=2^mu), let t = max gap with p_1..p_{t-1}=0.
#   Then t = smallest power of 2 tau such that p_tau != 0, AND S closed under +N/tau.
# Test directly: compute gap t via power sums; verify (a) t is power of 2,
#   (b) S closed under +N/t, (c) p_j=0 for ALL j with t∤j (the stronger conclusion).
import itertools, cmath, math
def ispow2(x): return x>0 and (x&(x-1))==0
def gap(idx,N):
    t=1
    while t<N:
        ps=sum(cmath.exp(2j*math.pi*t*i/N) for i in idx)
        if abs(ps)<1e-7: t+=1
        else: break
    return min(t,len(idx))  # gap below leading coeff (e_1..e_{t-1}=0)
def closed_under_shift(idx,step,N):
    S=set(idx); return all((x+step)%N in S for x in idx)
def all_nonmult_vanish(idx,N,t):
    # check p_j = 0 for all 1<=j<N with t ∤ j
    for j in range(1,N):
        if j%t==0: continue
        ps=sum(cmath.exp(2j*math.pi*j*i/N) for i in idx)
        if abs(ps)>1e-7: return False
    return True
for N,amax in [(8,8),(16,16),(32,9),(64,6)]:
    bad_pow2=bad_shift=bad_strong=total=0
    for a in range(1,amax+1):
        for idx in itertools.combinations(range(N),a):
            t=gap(idx,N)
            if t<2: continue
            total+=1
            if not ispow2(t): bad_pow2+=1
            if not closed_under_shift(idx,N//t,N): bad_shift+=1
            if not all_nonmult_vanish(idx,N,t): bad_strong+=1
    print(f"N={N} a<={amax}: gap>=2 sets={total} | NOT-pow2={bad_pow2} | NOT-shift-closed={bad_shift} | NOT-strong-vanish={bad_strong}")
print("THEOREM HOLDS iff all three counts are 0.")
