import itertools
def primes_for(n, lo, cnt):
    out=[]; q=max(n+1,lo)
    while len(out)<cnt:
        if all(q%p for p in range(2,int(q**.5)+1)) and (q-1)%n==0: out.append(q)
        q+=1
    return out
def gen(q,n):
    for g in range(2,q):
        if all(pow(g,d,q)!=1 for d in range(1,q-1)) and pow(g,q-1,q)==1:
            return pow(g,(q-1)//n,q)
def orbits(n,q,w=4):
    z=gen(q,n); roots=[pow(z,i,q) for i in range(n)]
    e1set=set()
    for S in itertools.combinations(range(n),w):
        vals=[roots[i] for i in S]; e1=sum(vals)%q
        p2=sum(v*v%q for v in vals)%q
        if (e1*e1-p2)%q==0 and e1!=0: e1set.add(e1)
    seen=set();orb=0
    for e in e1set:
        if e in seen:continue
        orb+=1;x=e
        for _ in range(n): seen.add(x);x=x*z%q
    return orb, len(e1set)
print("n  #orbits  #distinct_e1  d/n  d/n^2",flush=True)
for n in [8,16,32,64,128]:
    qs=primes_for(n,20*n, 2 if n>=128 else 3)
    rs=[orbits(n,q) for q in qs]
    o=[r[0] for r in rs]; d=[r[1] for r in rs]
    dm=sum(d)/len(d)
    print(f"{n}: orbits={o} distinct={d}  d/n={dm/n:.2f} d/n^2={dm/n/n:.3f}",flush=True)
