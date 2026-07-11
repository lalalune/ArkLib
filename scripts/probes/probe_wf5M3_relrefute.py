import numpy as np
from sympy import primitive_root
def setup(p,n):
    g=primitive_root(p);h=pow(g,(p-1)//n,p)
    G=[];x=1
    for _ in range(n):G.append(x);x=(x*h)%p
    return sorted(G)
def df(k):
    pr=1
    while k>0:pr*=k;k-=2
    return pr
# Is the RELATIVE form cross_r <= 2rn E_r ever violated where ceiling E_r<=(2r-1)!!n^r holds?
# Use n=16, faithful p=12289, check both at each r.
p,n=12289,16
G=setup(p,n)
f=np.zeros(p,dtype=object)
for s in G:f[s]=1
print(f"n={n} p={p} (faithful): rel-form cross<=2rn*E vs ceiling E<=(2r-1)!!n^r")
for r in range(1,8):
    if r>1:
        fn=np.zeros(p,dtype=object)
        for s in G:fn+=np.roll(f,s)
        f=fn
    e=int((f.astype(object)**2).sum())
    tot=0
    for s in G:
        for t in G:tot+=int((f*np.roll(f,-((s-t)%p))).sum())
    cr=tot-n*e
    ceil=df(2*r-1)*n**r
    rel_ok = cr<=2*r*n*e
    abs_ok = cr<=2*r*df(2*r-1)*n**(r+1)
    ceil_ok = e<=ceil
    print(f"  r={r}: ceiling {'OK' if ceil_ok else 'VIOL'}({e/ceil:.3f}) | REL(2rn) {'OK' if rel_ok else 'VIOL'}({cr/e:.1f}vs{2*r*n}) | ABS {'OK' if abs_ok else 'VIOL'}({cr/(2*r*df(2*r-1)*n**(r+1)):.3f})")
