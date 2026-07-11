import sympy
from collections import Counter

def dyadic(k, beta):
    n=1<<k
    base=n**beta; m=(base-1)//n
    while True:
        p=m*n+1; m+=1
        if sympy.isprime(p):
            g=int(sympy.primitive_root(p)); z=pow(g,(p-1)//n,p)
            return set(pow(z,j,p) for j in range(n)),p,n

def maxrep_nonzero(H,p):
    cnt=Counter()
    for a in H:
        for b in H:
            s=(a+b)%p
            if s!=0: cnt[s]+=1
    return (max(cnt.values()) if cnt else 0)

print("max_{c!=0} r(c) at prize scale p~n^beta. ME (mu_n fiber over C) was <=2; does it hold at small p?")
print(f"{'k':>2} {'n':>4} {'b=4 maxr':>9} {'b=5 maxr':>9} {'b=8(huge)':>10}")
for k in (3,4,5,6,7):
    n=1<<k
    row=[]
    for beta in (4,5,8):
        if n**beta > 5e9 and beta==8 and n>=64: row.append('-'); continue
        H,p,_=dyadic(k,beta); row.append(maxrep_nonzero(H,p))
    print(f"{k:>2} {n:>4} {str(row[0]):>9} {str(row[1]):>9} {str(row[2]):>10}")
print("=> if b=4/5 columns stay 2 like b=8: r(c)<=2 SURVIVES at prize scale (closure direction!).")
print("   if they grow: the GV->const gap is open at prize scale.")
