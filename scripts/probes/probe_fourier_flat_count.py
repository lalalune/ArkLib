import itertools
def fhat(A,j,n,h):
    v=[0]*h
    for a in A:
        e=(j*a)%n
        if e<h: v[e]+=1
        else: v[e-h]-=1
    return tuple(v)
def count_flat(n,k,m):
    h=n//2; w=k+m; vals=set(); ns=0
    Z=tuple([0]*h)
    for A in itertools.combinations(range(n),w):
        ok=True
        for j in range(1,m):
            if fhat(A,j,n,h)!=Z: ok=False;break
        if ok: vals.add(fhat(A,m,n,h)); ns+=1
    return ns,len(vals)
n=16
for k,m in [(8,2),(8,3),(8,4),(6,2),(6,3),(4,2)]:
    ns,nv=count_flat(n,k,m)
    print(f"n=16 k={k} m={m} (t={k+m},δ={1-(k+m)/n:.3f}): #flatsets={ns} #bad=#distinct-fhat(m)={nv}",flush=True)
