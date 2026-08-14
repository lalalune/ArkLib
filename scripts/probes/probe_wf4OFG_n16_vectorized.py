"""
wf-OFG (#444): vectorized n=16 confirmation that the over-det binding radius δbind floor
`epsMCA(C,δbind) <= eps*` is DOMINATED by a non-monomial (under-det) direction, hence not
provable from the over-det monomial count.

For each γ-forcing subset R (size s*) we precompute, for a batch of directions, the forced
γ = -d0/d1 and whether the line lands in RS[k]. We count distinct mcaEvent-bad γ per direction.
Vectorize over the BATCH OF DIRECTIONS (256 monomial + many 2-term) with numpy mod-p arithmetic.
"""
import itertools, numpy as np

def isprime(x):
    if x<2:return False
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
def find_prime(n,lo):
    p=lo-lo%n+1
    while True:
        if p>lo and isprime(p):return p
        p+=n
def fac(x):
    f={};dd=2
    while dd*dd<=x:
        while x%dd==0:f[dd]=f.get(dd,0)+1;x//=dd
        dd+=1
    if x>1:f[x]=f.get(x,0)+1
    return f
def proot(p):
    fs=set(fac(p-1))
    for g in range(2,p):
        if all(pow(g,(p-1)//q,p)!=1 for q in fs):return g
def setup(n,p):
    g=proot(p);h=pow(g,(p-1)//n,p);return [pow(h,i,p) for i in range(n)]

def run(n):
    p=find_prime(n,n**4*4); mu=setup(n,p); k=n//4; sstar=n//2-1; p=int(p)
    print(f"n={n} p={p} k={k} s*={sstar} budget={n}",flush=True)
    muA=np.array(mu,dtype=object)
    # direction batch: U0[d], U1[d] are length-n eval vectors (python-int arrays mod p)
    dirs=[]; labels=[]
    for a in range(n):
        for b in range(n):
            if a==b: continue
            u0=[pow(x,a,p) for x in mu]; u1=[pow(x,b,p) for x in mu]
            dirs.append((u0,u1)); labels.append(("mono",a,b))
    for b in range(n):
        for bp in range(n):
            if b==bp: continue
            for cf in (1,p-1,2):
                u1=[(pow(x,b,p)+cf*pow(x,bp,p))%p for x in mu]
                u0=[pow(x,(b+1)%n,p) for x in mu]
                dirs.append((u0,u1)); labels.append(("2term",b,bp,cf))
    D=len(dirs)
    U0=np.array([d[0] for d in dirs],dtype=object)  # D x n
    U1=np.array([d[1] for d in dirs],dtype=object)
    badsets=[set() for _ in range(D)]
    inv=lambda z:pow(int(z)%p,p-2,p)
    pts_all=mu
    # divided-difference order-k on a set of k+1 points -> last coeff; in_RS = all windows zero
    def ddk(vals,xs):
        vs=list(vals);
        for j in range(1,k+1):
            for i in range(k,j-1,-1):
                vs[i]=(vs[i]-vs[i-1])*inv((xs[i]-xs[i-j])%p)%p
        return vs[k]
    def in_RS_vec(M,xs):
        # M: D x s  -> bool array length D : every length-(k+1) window has ddk==0
        s=len(xs); res=np.ones(D,dtype=bool)
        for st in range(s-k):
            xw=xs[st:st+k+1]
            for d in range(D):
                if not res[d]: continue
                if ddk([int(M[d,st+t]) for t in range(k+1)],xw)!=0: res[d]=False
        return res
    subs=list(itertools.combinations(range(n),sstar))
    for R in subs:
        xs=[pts_all[i] for i in R]
        A0=U0[:,list(R)]; A1=U1[:,list(R)]   # D x s
        u1R=in_RS_vec(A1,xs);
        u0R=in_RS_vec(A0,xs)
        for d in range(D):
            if u1R[d]:
                continue  # u1|S in RS: either whole-line (joint, skip) or no single γ
            # joint clause: joint iff u0R and u1R; here u1R false so joint false -> clause OK
            d0=ddk([int(A0[d,t]) for t in range(sstar)],xs)
            d1=ddk([int(A1[d,t]) for t in range(sstar)],xs)
            if d1%p==0: continue
            gm=(-d0*inv(d1))%p
            line=[(int(A0[d,t])+gm*int(A1[d,t]))%p for t in range(sstar)]
            if ddk_all_windows(line,xs,k,p,inv): badsets[d].add(gm)
    counts=[len(b) for b in badsets]
    import numpy as _np
    cm=_np.array(counts)
    mono_idx=[i for i,l in enumerate(labels) if l[0]=="mono"]
    two_idx=[i for i,l in enumerate(labels) if l[0]=="2term"]
    mbest=max(counts[i] for i in mono_idx); marg=labels[mono_idx[_np.argmax([counts[i] for i in mono_idx])]]
    tbest=max(counts[i] for i in two_idx); targ=labels[two_idx[_np.argmax([counts[i] for i in two_idx])]]
    print(f"MONOMIAL_MAX={mbest} at {marg} budget={n}",flush=True)
    print(f"TWOTERM_MAX={tbest} at {targ} budget={n}",flush=True)
    print(f"FLOOR epsMCA<=eps* at δbind: {'HOLDS' if max(mbest,tbest)<=n else 'FAILS (max>budget)'}",flush=True)

def ddk_all_windows(vals,xs,k,p,inv):
    s=len(xs)
    if s<=k: return True
    for st in range(s-k):
        vs=[int(v) for v in vals[st:st+k+1]]; xw=xs[st:st+k+1]
        for j in range(1,k+1):
            for i in range(k,j-1,-1):
                vs[i]=(vs[i]-vs[i-1])*inv((xw[i]-xw[i-j])%p)%p
        if vs[k]!=0: return False
    return True

if __name__=="__main__":
    run(16)
    print("DONE16",flush=True)
