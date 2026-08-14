import cmath, math
def fac(m):
    f=set();d=2
    while d*d<=m:
        while m%d==0:f.add(d);m//=d
        d+=1
    if m>1:f.add(m)
    return f
def primroot(p):
    fs=fac(p-1)
    for g in range(2,p):
        if all(pow(g,(p-1)//q,p)!=1 for q in fs): return g
def check(n,p):
    assert all(p%d for d in range(2,int(p**.5)+1)), "p not prime"
    assert (p-1)%n==0 and n<p-1
    g=primroot(p); m=(p-1)//n; z=pow(g,m,p); G=[pow(z,i,p) for i in range(n)]
    mx=0.0; ssq=0.0; b=1
    for i in range(m):
        s=sum(cmath.exp(2j*math.pi*(b*x%p)/p) for x in G).real
        ssq+=s*s
        if abs(s)>mx: mx=abs(s)
        b=b*g%p
    floor=math.sqrt(2*n*math.log(m))
    return mx, floor, mx/floor, ssq, p-n, m
for (n,p) in [(64,16778497),(32,1048609),(16,65537)]:
    mx,fl,R,ssq,pn,m=check(n,p)
    print(f"n={n} p={p} beta={math.log(p)/math.log(n):.3f} m={m}: max={mx:.3f} floor=sqrt(2n ln m)={fl:.3f} R={R:.4f}  sum|eta|^2={ssq:.0f} (=p-n={pn}? {abs(ssq-pn)<1})  {'>1 REFUTES sharp const' if R>1 else 'R<1'}",flush=True)
