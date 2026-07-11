import math
def is_prime(m):
    if m<2: return False
    i=2
    while i*i<=m:
        if m%i==0: return False
        i+=1
    return True
def find_prime(n,lo):
    p=lo
    while True:
        if (p-1)%n==0 and is_prime(p): return p
        p+=1
def subgroup(p,n):
    for g0 in range(2,p):
        g=pow(g0,(p-1)//n,p)
        if len({pow(g,i,p) for i in range(n)})==n:
            return sorted(pow(g,i,p) for i in range(n))
    return None
def dfact(m):
    r=1;k=m
    while k>0:r*=k;k-=2
    return r

def Er_counts(H, p, rmax):
    """Return E_r over Z (no wrap) and over F_p (wrap), for r=1..rmax, via convolution."""
    n=len(H)
    # integer convolution: distribution of r-fold sums as dict
    # f_int: array index = actual integer sum
    L=rmax*p+1
    f=[0]*(L); 
    for h in H: f[h]+=1
    fp=[0]*p
    for h in H: fp[h]+=1
    EZ=[];EP=[]
    cur=f[:]; curp=fp[:]
    for r in range(1,rmax+1):
        EZ.append(sum(c*c for c in cur))
        EP.append(sum(c*c for c in curp))
        if r<rmax:
            # convolve cur with base H (integer)
            nxt=[0]*(L)
            for t,c in enumerate(cur):
                if c:
                    for h in H:
                        nxt[t+h]+=c
            cur=nxt
            # convolve curp with base (mod p)
            nxtp=[0]*p
            for t,c in enumerate(curp):
                if c:
                    for h in H:
                        nxtp[(t+h)%p]+=c
            curp=nxtp
    return EZ,EP

for (n) in [8,16]:
    for mult in [3,4]:
        p=find_prime(n, n**mult)
        H=subgroup(p,n)
        rmax=10 if n==8 else 8
        EZ,EP=Er_counts(H,p,rmax)
        print(f"\n n={n} p={p} (~n^{mult}) log_n p={math.log(p)/math.log(n):.2f} ln p={math.log(p):.1f}")
        print(f"  {'r':>2} {'E_r(Z) genuine':>16} {'E_r(Fp)':>14} {'spurious':>12} {'spur/genuine':>12} {'Gaussian(2r-1)!!n^r':>20}")
        for i,r in enumerate(range(1,rmax+1)):
            spur=EP[i]-EZ[i]; gauss=dfact(2*r-1)*n**r
            print(f"  {r:>2} {EZ[i]:>16d} {EP[i]:>14d} {spur:>12d} {spur/EZ[i]:>12.4f} {gauss:>20.3e}")
