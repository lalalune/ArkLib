import cmath, math
# Independently verify the army's load-bearing witnesses: explicit weight-6 excess relations.
def isprime(x):
    if x<2:return False
    d=x-1;s=0
    while d%2==0:d//=2;s+=1
    for a in [2,3,5,7,11,13,17,19,23,29,31,37]:
        if a%x==0: continue
        y=pow(a,d,x)
        if y in(1,x-1):continue
        ok=False
        for _ in range(s-1):
            y=y*y%x
            if y==x-1:ok=True;break
        if not ok:return False
    return True
def fac(x):
    f={};d=2
    while d*d<=x:
        while x%d==0:f[d]=f.get(d,0)+1;x//=d
        d+=1
    if x>1:f[x]=f.get(x,0)+1
    return f
def proot(p):
    fs=set(fac(p-1))
    for g in range(2,p):
        if all(pow(g,(p-1)//q,p)!=1 for q in fs):return g
def check(p,n,terms,label):
    assert isprime(p), f"{p} not prime"
    assert (p-1)%n==0, "n does not divide p-1"
    g=proot(p); h=pow(g,(p-1)//n,p)
    assert pow(h,n,p)==1 and all(pow(h,n//q,p)!=1 for q in set(fac(n))), "h not primitive n-th root"
    # mod p sum
    s=sum(sgn*pow(h,c,p) for (sgn,c) in terms)%p
    # C value
    cval=sum(sgn*cmath.exp(2j*math.pi*c/n) for (sgn,c) in terms)
    w=len(terms)
    floor_target=2*math.ceil(math.log2((p-1)//n))
    print(f"{label}: n={n} p={p} weight={w}",flush=True)
    print(f"   sum eps_i h^c_i mod p = {s}   ({'VANISHES' if s==0 else 'NONZERO -- BAD'})",flush=True)
    print(f"   |D|_C = {abs(cval):.4f}   ({'nonzero over C — GENUINE EXCESS' if abs(cval)>1e-9 else 'zero over C -- trivial'})",flush=True)
    print(f"   weight {w}  vs  target 2*ceil(log2 m) = {floor_target}   => {'REFUTES (w << target)' if w<floor_target else 'ok'}",flush=True)
    print(flush=True)
    return s==0 and abs(cval)>1e-9 and w<floor_target
# G2/G5/R1 witness: n=64, p=16778497, D = z^0+z^1+z^7 -z^9-z^10-z^61
ok1=check(16778497,64,[(1,0),(1,1),(1,7),(-1,9),(-1,10),(-1,61)],"G2/R1 n=64 wt6")
# G1 witness n=128, p=268440449, D = z^34+z^38+z^67+z^73+z^78+z^83 (all +1)
ok2=check(268440449,128,[(1,34),(1,38),(1,67),(1,73),(1,78),(1,83)],"G1 n=128 wt6")
# G1 witness n=256, p=4294968833, D = z^81+z^94-z^130-z^144-z^145+z^254
ok3=check(4294968833,256,[(1,81),(1,94),(-1,130),(-1,144),(-1,145),(1,254)],"G1 n=256 wt6")
print("ALL THREE WITNESSES VALID:", ok1 and ok2 and ok3)
