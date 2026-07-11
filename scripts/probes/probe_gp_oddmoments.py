# Test: odd moments of Gaussian periods of mu_{2^mu}: sum_i eta_i^{2k+1} = -n^{2k} (prize regime beta>2k+1).
# Derivation: sum_{b!=0} S_b^{2k+1} = p*T_{2k+1} - n^{2k+1}, T = #{(2k+1)-tuples of mu_n summing to 0 mod p}.
# For n=2^mu, no odd-length all-+ vanishing sum of 2-power roots (relations are antipodal pairs => even),
# so T_{2k+1}=0 in char-0 (beta>2k+1) => sum_i eta_i^{2k+1} = (p*0 - n^{2k+1})/n = -n^{2k}.
import cmath, math
def isprime(q):
    if q<2: return False
    if q%2==0: return q==2
    for p in range(3,int(q**.5)+1,2):
        if q%p==0: return False
    return True
def primeat(n,beta):
    q=int(n**beta)
    while not(isprime(q) and (q-1)%n==0): q+=1
    return q
def fac(m):
    f=set();d=2
    while d*d<=m:
        while m%d==0:f.add(d);m//=d
        d+=1
    if m>1:f.add(m)
    return f
def periods(n,p):
    fs=fac(p-1); g=2
    while not all(pow(g,(p-1)//q,p)!=1 for q in fs): g+=1
    m=(p-1)//n; z=pow(g,m,p); G=[pow(z,i,p) for i in range(n)]
    out=[];b=1
    for i in range(m):
        out.append(sum(cmath.exp(2j*math.pi*(b*x%p)/p) for x in G).real); b=b*g%p
    return out
for n in [8,16,32]:
    # need beta > 2k+1 for k up to 3 => beta>7; use beta=7.5
    p=primeat(n,7.5); eta=periods(n,p)
    print(f"n={n} p={p} beta={math.log(p)/math.log(n):.2f}:",flush=True)
    for k in [0,1,2,3]:
        s=sum(e**(2*k+1) for e in eta)
        pred=-(n**(2*k)) if k>0 else -1  # k=0: sum eta = -1
        print(f"   sum eta^{2*k+1} = {s:.1f}   predicted -n^{2*k}={pred}   match={abs(s-pred)<0.5}",flush=True)
