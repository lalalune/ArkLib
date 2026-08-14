import itertools
def fhat(A,jj,n,h):
    v=[0]*h
    for a in A: 
        e=(jj*a)%n; v[e%h]+= (1 if e<h else -1)
    return tuple(v)
def cf(n,k,m):
    h=n//2; w=k+m; vals=set(); Z=tuple([0]*h)
    if w>n or w<0 or k<0: return None
    for A in itertools.combinations(range(n),w):
        if all(fhat(A,j,n,h)==Z for j in range(1,m)): vals.add(fhat(A,m,n,h))
    vals.discard(Z); return len(vals)
print("recursion #bad_16(k,2m') == #bad_8(k/2,m'):")
ok=True
for k in range(2,16,2):
    for mp in range(1,5):
        m=2*mp
        a=cf(16,k,m); b=cf(8,k//2,mp)
        if a is None or b is None: continue
        s="ok" if a==b else "MISMATCH"
        if a!=b: ok=False
        print(f"  k={k} m={m}: 16->{a}  8(k/2,{mp})->{b}  {s}")
print("ALL HOLD" if ok else "mismatches")
print("odd m (=0?):", [cf(16,8,m) for m in [3,5,7]])
