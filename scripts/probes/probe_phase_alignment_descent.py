import cmath, math
def primfind(n, lo):
    q=max(n+1,lo)
    while True:
        if all(q%p for p in range(2,int(q**.5)+1)) and (q-1)%n==0:
            for g in range(2,q):
                if all(pow(g,d,q)!=1 for d in range(1,q-1)) and pow(g,q-1,q)==1:
                    return q,g
        q+=1
def M_and_bstar(n,p,g):
    z=pow(g,(p-1)//n,p); G=[pow(z,i,p) for i in range(n)]
    best=0;bs=1
    for b in range(1,p):
        v=abs(sum(cmath.exp(2j*math.pi*(b*x%p)/p) for x in G))
        if v>best:best=v;bs=b
    return best,bs,z,G
def Sb(b,G,p): return abs(sum(cmath.exp(2j*math.pi*(b*x%p)/p) for x in G))
print("n  M(n)  M(n/2)  ratio  |h1@b*| |h2@b*|  (each vs M(n/2))",flush=True)
for n in [16,32,64,128]:
    p,g=primfind(n,8000)
    Mn,bs,z,G=M_and_bstar(n,p,g)
    half=[pow(z,2*i,p) for i in range(n//2)]
    # M(n/2) over same p: mu_{n/2}=half
    Mh=0
    for b in range(1,p):
        v=Sb(b,half,p)
        if v>Mh:Mh=v
    h1=Sb(bs,half,p); h2=Sb((bs*z)%p,half,p)
    print(f"{n}: M={Mn:.2f} M(n/2)={Mh:.2f} ratio={Mn/Mh:.3f}  h1={h1:.2f}({h1/Mh:.2f}M') h2={h2:.2f}({h2/Mh:.2f}M')  √2={math.sqrt(2):.3f}",flush=True)
