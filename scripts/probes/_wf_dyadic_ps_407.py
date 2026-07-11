# Fast: use POWER SUMS p_j = sum zeta^{j*i}. Condition e_1..e_{t-1}=0 <=> p_1..p_{t-1}=0 (Newton).
import itertools, numpy as np
from collections import defaultdict
def ispow2(x): return x&(x-1)==0
def run(N, amax):
    w = np.exp(2j*np.pi*np.arange(N)/N)
    # precompute powers: P[j,i] = w[i]^j = exp(2pi i j i /N) = w[(j*i)%N]
    table=defaultdict(lambda: defaultdict(int)); total=0; nonpow2=0; s_ne_t=0
    def gap(idx):
        t=1
        while t<len(idx):
            ps=sum(np.exp(2j*np.pi*t*np.array(idx)/N))
            if abs(ps)<1e-7: t+=1
            else: break
        return t
    def maxs(idx):
        Sset=set(idx); best=1
        for s in range(1,N+1):
            if N%s: continue
            if all((x+N//s)%N in Sset for x in idx): best=max(best,s)
        return best
    for a in range(2,amax+1):
        for idx in itertools.combinations(range(N),a):
            t=gap(idx)
            if t<2: continue
            total+=1; s=maxs(idx); table[t][s]+=1
            if not ispow2(t): nonpow2+=1
            if s!=t: s_ne_t+=1
    print(f"N={N} weight<={amax}: total(gap>=2)={total} nonpow2={nonpow2} s!=t={s_ne_t}")
    for t in sorted(table): print(f"  gap t={t:2d}: dist={dict(table[t])}")
run(32,7)
