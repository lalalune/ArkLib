import cmath, math
def primfind(n, lo):
    q=max(n+1,lo)
    while True:
        if all(q%p for p in range(2,int(q**.5)+1)) and (q-1)%n==0:
            for g in range(2,q):
                if all(pow(g,d,q)!=1 for d in range(1,q-1)) and pow(g,q-1,q)==1:
                    return q,g
        q+=1
def periods(n,p,g):
    z=pow(g,(p-1)//n,p); G=[pow(z,i,p) for i in range(n)]; m=(p-1)//n
    out=[];b=1
    for i in range(m):
        s=sum(cmath.exp(2j*math.pi*(b*x%p)/p) for x in G); out.append(s.real); b=b*g%p
    return out,m
def dblfact(k):
    r=1
    for j in range(1,k+1,2): r*=j
    return r
# focus on the prize-regime borderline: n=32 at growing beta, deep r vs log m
for (n,lo) in [(32,300000),(32,30000000)]:
    p,g=primfind(n,lo)
    eta,m=periods(n,p,g)
    beta=math.log(p)/math.log(n); lm=math.log(m)
    mx=max(abs(e) for e in eta)
    print(f"\nn={n} p={p} beta={beta:.2f} log m={lm:.1f} (need sub-G to r~{lm:.0f})  max|eta|={mx:.1f} vs sqrt(2n log m)={math.sqrt(2*n*lm):.1f}",flush=True)
    crossed=None
    for r in range(2,17):
        Er=(n*sum(e**(2*r) for e in eta)+n**(2*r))/p
        ratio=Er/(dblfact(2*r-1)*n**r)
        mark=" <== crosses 1" if ratio>1 and crossed is None else ""
        if ratio>1 and crossed is None: crossed=r
        print(f"  r={r}: E_r/Gauss={ratio:.3f}{mark}",flush=True)
    print(f"  --> relation threshold r*={crossed}, need r~{lm:.0f}: {'SUB-G holds past needed depth' if (crossed is None or crossed>lm) else 'CROSSES before needed depth'}",flush=True)
