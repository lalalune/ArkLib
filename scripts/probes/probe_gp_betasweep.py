import cmath, math
def isprime(q):
    if q<2: return False
    if q%2==0: return q==2
    for p in range(3,int(q**.5)+1,2):
        if q%p==0: return False
    return True
def factor(m):
    f=set(); d=2
    while d*d<=m:
        while m%d==0: f.add(d); m//=d
        d+=1 if d==2 else 2
    if m>1: f.add(m)
    return f
def primroot(p):
    fs=factor(p-1)
    for g in range(2,p):
        if all(pow(g,(p-1)//q,p)!=1 for q in fs): return g
def maxratio(n,p):
    g=primroot(p); m=(p-1)//n
    z=pow(g,m,p); G=[pow(z,i,p) for i in range(n)]
    mx=0.0; b=1
    for i in range(m):
        v=abs(sum(cmath.exp(2j*math.pi*(b*x%p)/p) for x in G))
        if v>mx: mx=v
        b=b*g%p
    return mx/math.sqrt(2*n*math.log(m))
def firstprime(n, target):
    q=target
    while not(isprime(q) and (q-1)%n==0): q+=1
    return q
for n in [16,32]:
    row=[]
    for beta in [4,5,6]:
        p=firstprime(n, n**beta)
        if (n**beta) > 4_000_000 and n==32: continue  # cap cost
        row.append((beta, round(maxratio(n,p),3)))
    print(f"n={n}: max|eta|/sqrt(2n log m) by beta = {row}",flush=True)
