#!/usr/bin/env python3
"""Probe: Lam-Leung brick B (minimal-element weight law), direct enumeration.

Pre-registered: every MINIMAL vanishing N-multiset of pqr-th roots of unity has
weight in {p,q,r} or weight >= p*(q-1)+r-q.

Tests:
 1. n=30 (2,3,5), bound 6: exhaustive 0/1 sums weight<=7 + multiplicity patterns of
    weight<=6; expect minimals only at weights {2,3,5,6}; the LL asymmetric witness
    (weight 6) must appear.
 2. n=105 (3,5,7), bound 14: the first gap-relevant claim = NO vanishing sums of
    weight 4 at all (0/1 and all multiplicity patterns); weight {1,2} trivially none.
Exit 0 iff law holds everywhere.
"""
import itertools, sys

def poly_divmod_exact(num, den):
    num = num[:]; dd = len(den)-1
    while num and num[-1] == 0: num.pop()
    while len(num)-1 >= dd and any(num):
        c = num[-1]; k = len(num)-1-dd
        for i, dco in enumerate(den): num[k+i] -= c*dco
        while num and num[-1] == 0: num.pop()
    return num

def cyclotomic(n, _c={}):
    if n in _c: return _c[n]
    num = [-1]+[0]*(n-1)+[1]
    for d in range(1, n):
        if n % d == 0:
            den = cyclotomic(d); q=[0]*(len(num)-len(den)+1); rem=num[:]
            dd=len(den)-1
            while len(rem)-1 >= dd and any(rem):
                c=rem[-1]; k=len(rem)-1-dd; q[k]=c
                for i,dco in enumerate(den): rem[k+i]-=c*dco
                while rem and rem[-1]==0: rem.pop()
            assert not rem
            num = q
            while num and num[-1]==0: num.pop()
    _c[n]=num; return num

def vanishes(cells_mults, n, phi):
    v=[0]*n
    for (c,m) in cells_mults: v[c]+=m
    return not poly_divmod_exact(v, phi)

def minimal(cells_mults, n, phi):
    # proper nonzero submultisets
    ranges=[range(m+1) for (_,m) in cells_mults]
    tot=sum(m for _,m in cells_mults)
    for combo in itertools.product(*ranges):
        s=sum(combo)
        if s==0 or s==tot: continue
        if vanishes([(c,mm) for ((c,_),mm) in zip(cells_mults,combo) if mm], n, phi):
            return False
    return True

def enum_weighted(n, weight, phi):
    """all multisets of given total weight (cells with multiplicities), up to rotation
    (fix: cell 0 has multiplicity >= 1 after rotating min cell to 0 -- enumerate with
    first chosen cell = 0)."""
    out=[]
    # partitions of weight into parts (multiplicities) over distinct cells, first cell = 0
    def parts(rem, maxpart):
        if rem==0: yield []
        for pp in range(min(rem,maxpart),0,-1):
            for rest in parts(rem-pp, pp): yield [pp]+rest
    for pat in parts(weight, weight):
        kcells=len(pat)
        # distinct sorted multiplicities pattern over cells; cell0 fixed = 0 (rotation rep)
        for rest in itertools.combinations(range(1,n), kcells-1):
            cells=(0,)+rest
            # assign pattern multiplicities to cells: all distinct permutations
            for perm in set(itertools.permutations(pat)):
                cm=list(zip(cells,perm))
                if vanishes(cm,n,phi): out.append(cm)
    return out

def main():
    ok=True
    # --- n=30 ---
    n=30; phi=cyclotomic(n); p,q,r=2,3,5; bound=p*(q-1)+r-q
    found={}
    for wgt in range(1,8):
        for cm in enum_weighted(n,wgt,phi):
            if minimal(cm,n,phi):
                found.setdefault(wgt,0); found[wgt]+=1
                if not (wgt in (p,q,r) or wgt>=bound):
                    print("VIOLATION n=30 weight",wgt,cm); ok=False
    print("n=30 minimal census by weight (rotation reps):",found)
    if 6 not in found: print("MISSING LL witness at weight 6"); ok=False
    if 4 in found or 1 in found: print("UNEXPECTED minimal at weight 1/4"); ok=False
    # --- n=105 weight 4: expect NO vanishing at all ---
    n=105; phi=cyclotomic(n)
    cnt=0
    for wgt in [1,2,4]:
        for cm in enum_weighted(n,wgt,phi):
            cnt+=1; print("VIOLATION n=105 vanishing weight",wgt,cm); ok=False
    print("n=105 weights {1,2,4}: vanishing sums found:",cnt,"(expect 0)")
    print("PROBE", "PASS" if ok else "FAIL")
    sys.exit(0 if ok else 1)

main()
