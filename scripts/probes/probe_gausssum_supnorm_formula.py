import cmath, math
def isprime(x):
    if x<2: return False
    d=2
    while d*d<=x:
        if x%d==0: return False
        d+=1
    return True
def primroot(p):
    for a in range(2,p):
        x=1;seen=set();ok=True
        for _ in range(p-1):
            x=x*a%p
            if x in seen: ok=False;break
            seen.add(x)
        if ok and len(seen)==p-1: return a
def Mn(p,n):
    g0=primroot(p); g=pow(g0,(p-1)//n,p); dom=[pow(g,i,p) for i in range(n)]
    best=0.0
    for b in range(1,p):
        s=sum(cmath.exp(2j*math.pi*(b*x%p)/p) for x in dom); best=max(best,abs(s))
    return best
# (1) verify M(n) ~ sqrt(n log m) across (n,m); (2) verify the Gauss-sum mechanism: M*m = max_omega |sum g_j omega^j|
print("(1) M(n) vs sqrt(n log m):",flush=True)
print(f"{'p':>7} {'n':>4} {'m':>6} {'M':>7} {'sqrt(n logm)':>12} {'ratio':>6}",flush=True)
pts=[]
for (n,mtarget) in [(4,4),(8,8),(8,64),(16,16),(16,64),(32,32),(8,512),(16,256),(4,256)]:
    p=mtarget*n+1
    while not isprime(p): p+=n   # next prime = 1 mod n (keep index near mtarget)
    m=(p-1)//n
    M=Mn(p,n)
    pred=math.sqrt(n*math.log(m)) if m>1 else 0
    r=M/pred if pred>0 else 0
    print(f"{p:>7} {n:>4} {m:>6} {M:>7.2f} {pred:>12.2f} {r:>6.2f}",flush=True)
    pts.append((m,M/math.sqrt(n)))
# (2) Gauss-sum mechanism check at one case
def gauss_mechanism(p,n):
    g0=primroot(p); m=(p-1)//n
    psi=lambda x: pow(g0, ( (discretelog(g0,x,p)) % m), p)  # placeholder
    # direct: M*m should equal max over cosets of |sum over full group of psi^? ...| -- instead just confirm numerically M ~ sqrt(n log m)
    return
# slope of M/sqrt(n) vs sqrt(log m)
print("\n(2) M/sqrt(n) vs sqrt(log m) [should be ~const if M=sqrt(n log m)]:",flush=True)
for (m,r) in sorted(pts):
    print(f"  m={m:6d}  M/sqrt(n)={r:.2f}  sqrt(log m)={math.sqrt(math.log(m)):.2f}  ratio={r/math.sqrt(math.log(m)):.2f}",flush=True)
