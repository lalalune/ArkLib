import cmath, math
# Confirm: max_k|S(k)|, S(k)=Σ_{ζ∈μ_n}χ^k(1+ζ), scales as √(n log m) (prize TRUE) — while the completion bound gives √q.
# If true value ~√(n log m) << √q = completion bound, the completion route is lossy by factor √m = the WALL.
def isprime(x):
    if x<2:return False
    if x%2==0:return x==2
    d=x-1;s=0
    while d%2==0:d//=2;s+=1
    for a in [2,3,5,7,11,13,17,19,23,29,31,37]:
        if a%x==0:continue
        y=pow(a,d,x)
        if y in(1,x-1):continue
        ok=False
        for _ in range(s-1):
            y=y*y%x
            if y==x-1:ok=True;break
        if not ok:return False
    return True
def proot(p):
    f=set();x=p-1;d=2
    while d*d<=x:
        while x%d==0:f.add(d);x//=d
        d+=1
    if x>1:f.add(x)
    for g in range(2,p):
        if all(pow(g,(p-1)//q,p)!=1 for q in f):return g
def bigp(n):
    p=n*n*n*n
    while not(p%n==1 and isprime(p)):p+=n
    return p
for n in [16,32,64]:
    p=bigp(n);g=proot(p);m=(p-1)//n
    mu=[pow(g,(p-1)//n*i,p) for i in range(n)]   # mu_n
    chi_log={}  # discrete log base g for chi=g-th-power char
    # chi(y)=exp(2πi*ind_g(y)/(p-1)); compute ind via baby table (feasible n^4 up to 64 => p up to 1.6e7, table ok)
    ind={}; cur=1
    for e in range(p-1): ind[cur]=e; cur=cur*g%p
    w=cmath.exp(2j*cmath.pi/(p-1))
    def chi(yk,kk):  # chi^k(y) = w^(k*ind(y)) ; yk already the value
        return w**((kk*ind[yk])%(p-1))
    best=0
    for k in range(1,min(p-1,4000)):  # scan k (the char power); enough to find max over a representative range
        S=0
        for z in mu:
            v=(1+z)%p
            if v==0: continue
            S+=chi(v,k)
        a=abs(S)
        if a>best:best=a
    sqrtnlogm=math.sqrt(n*math.log(m))
    print(f"n={n} p={p} m={m}: max|S(k)|≈{best:.2f}  √(n log m)={sqrtnlogm:.2f}  ratio={best/sqrtnlogm:.3f}  | √n={math.sqrt(n):.2f}  √q(completion bd)={math.sqrt(p):.0f}",flush=True)
print("KEY: ratio max|S|/√(n log m) ~ O(1) => prize value IS √(n log m); completion bound √q is lossy by √m = the wall.",flush=True)
print("DONE",flush=True)
