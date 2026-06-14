import itertools, random
def rou(q,n):
    for g in range(2,q):
        x=1;s=set()
        for _ in range(q-1): x=x*g%q;s.add(x)
        if len(s)==q-1: o=pow(g,(q-1)//n,q);return [pow(o,i,q) for i in range(n)]
def maxagree(mu,vals,q,k,n,inv):
    best=0
    for sub in itertools.combinations(range(n),k):
        xs=[mu[i] for i in sub]; ys=[vals[i] for i in sub]; c=0
        for t in range(n):
            xt=mu[t];acc=0
            for j in range(k):
                num=1;den=1
                for l in range(k):
                    if l!=j: num=num*(xt-xs[l])%q; den=den*(xs[j]-xs[l])%q
                acc=(acc+ys[j]*num*inv[den%q])%q
            if acc==vals[t]:
                c+=1
        if c>best: best=c
    return best
def nbad(mu,u0,u1,q,k,n,a,inv):
    c=0
    for g in range(q):
        v=[(u0[i]+g*u1[i])%q for i in range(n)]
        if maxagree(mu,v,q,k,n,inv)>=a: c+=1
    return c
def run(q,n,k,w,nsamp):
    inv=[0]*q
    for x in range(1,q): inv[x]=pow(x,q-2,q)
    mu=rou(q,n);a=n-w;J=1-(k/n)**.5;d=w/n
    mon=[[pow(mu[i],e,q) for i in range(n)] for e in range(n)]
    Imono=0
    for b in range(n):
        for c in range(n):
            if b!=c and maxagree(mu,mon[c],q,k,n,inv)<a:
                v=nbad(mu,mon[b],mon[c],q,k,n,a,inv)
                if v>Imono: Imono=v
    rng=random.Random(5);vals=[];tried=0;Imax=0
    for _ in range(nsamp):
        u0=[rng.randrange(q) for _ in range(n)];u1=[rng.randrange(q) for _ in range(n)]
        if maxagree(mu,u1,q,k,n,inv)>=a: continue
        tried+=1;v=nbad(mu,u0,u1,q,k,n,a,inv);vals.append(v)
        if v>Imax: Imax=v
    avg=sum(vals)/len(vals) if vals else 0
    print(f"n={n:2d} q={q:3d}(q/n={q/n:.0f}) k={k} w={w} d={d:.3f}{'A' if d>J else 'b'} a={a} | "
          f"mono={Imono:3d} avg={avg:5.1f} worst={Imax:3d} | worst/avg={Imax/avg if avg else 0:.2f} "
          f"worst/mono={Imax/Imono if Imono else 0:.2f}",flush=True)
print("TREND of concentration (worst/avg) and mono-suboptimality (worst/mono) vs n, above Johnson:\n",flush=True)
run(257,8,4,3,120)    # q/n=32 d=0.375
run(41,10,5,3,120)    # q/n=4  d=0.300
run(61,12,6,4,90)     # q/n=5  d=0.333
run(43,14,7,5,60)     # q/n=3  d=0.357
print("done",flush=True)
