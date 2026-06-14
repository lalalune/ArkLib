import itertools, cmath, math
def ispow2(x): return x>0 and (x&(x-1))==0
def gap(idx,N,W):
    t=1
    while t<len(idx):
        if abs(sum(W[(t*i)%N] for i in idx))<1e-7: t+=1
        else: break
    return t
def closed(idx,step,N):
    S=set(idx); return all((x+step)%N in S for x in idx)
for N,amax in [(32,9),(64,6)]:
    W=[cmath.exp(2j*math.pi*k/N) for k in range(N)]
    bp=bs=tot=0
    for a in range(2,amax+1):
        for idx in itertools.combinations(range(N),a):
            t=gap(idx,N,W)
            if t<2: continue
            tot+=1
            if not ispow2(t): bp+=1
            if not closed(idx,N//t,N): bs+=1
    print(f"N={N} a<={amax}: gap>=2={tot} NOT-pow2={bp} NOT-shift={bs}")
