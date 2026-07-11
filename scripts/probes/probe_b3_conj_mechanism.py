import itertools, cmath, math

def roots_of_unity(n):
    return [cmath.exp(2j*math.pi*k/n) for k in range(n)]

def esymm(vals, h):
    es = [0j]*(h+1); es[0]=1+0j
    for v in vals:
        for k in range(h,0,-1):
            es[k]+=es[k-1]*v
    return es[1:]

# For triples a,b,c of roots of unity (|x|=1, so conj(x)=1/x):
#   e1 = a+b+c, e2 = ab+ac+bc, e3 = abc
#   conj(e1) = 1/a+1/b+1/c = (bc+ac+ab)/(abc) = e2/e3
# So  e2 = conj(e1) * e3.  Thus fixing e1 fixes e2 ONCE e3 is fixed.
# Mechanism check: does e2 == conj(e1)*e3 hold exactly for all root-of-unity triples?

def test_conj(n):
    R = roots_of_unity(n)
    maxerr=0.0
    cnt=0
    for t in itertools.combinations_with_replacement(range(n),3):
        vals=[R[i] for i in t]
        e1,e2,e3 = esymm(vals,3)
        lhs = e2
        rhs = e3 * complex(e1.real, -e1.imag)   # conj(e1)*e3
        maxerr=max(maxerr, abs(lhs-rhs)); cnt+=1
    return maxerr,cnt

# Now: claim is equal e1 AND equal e3 force equal triple (since e2 then equal via conj relation,
# and equal e1,e2,e3 => same monic cubic => same roots).
# But the probe above used e1,e2 (not e3). Test e1+e3 version too.
def multiset_eq(A,B,tol=1e-6):
    B=list(B)
    for a in A:
        ok=False
        for i,b in enumerate(B):
            if abs(a-b)<tol: B.pop(i); ok=True; break
        if not ok: return False
    return True

from collections import defaultdict
def test_e1e3(n):
    R=roots_of_unity(n)
    by=defaultdict(list)
    for t in itertools.combinations_with_replacement(range(n),3):
        vals=[R[i] for i in t]
        e1,e2,e3=esymm(vals,3)
        if abs(e1)<1e-7: continue
        key=(round(e1.real,6),round(e1.imag,6),round(e3.real,6),round(e3.imag,6))
        by[key].append(t)
    coll=0;pairs=0
    for ts in by.values():
        for a,b in itertools.combinations(ts,2):
            pairs+=1
            if not multiset_eq([R[i] for i in a],[R[i] for i in b]): coll+=1
    return coll,pairs

for n in [4,8,16,32]:
    err,cnt=test_conj(n)
    c,p=test_e1e3(n)
    print(f"n={n:3d}: e2==conj(e1)*e3 maxerr={err:.2e} ({cnt} triples) | e1,e3-fixed collisions={c}/{p}")
