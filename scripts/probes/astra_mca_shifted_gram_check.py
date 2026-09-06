#!/usr/bin/env python3
"""Finite exact controls; see accompanying written proof and scope limits."""
from itertools import combinations
from math import comb
import json

P = 365375409332725729550921208179070755120141565953
BLOCKS = [set(a) for a in [
 [2,3,5,6,8,13,14,19,20,30,32,34,36,37,41,45,46,50,51,54,57],
 [1,2,3,5,6,7,11,12,17,24,27,32,33,35,36,37,46,56,60,61,63],
 [2,4,6,11,14,16,20,25,26,32,33,35,41,46,47,49,54,55,58,60,62],
 [1,5,10,17,24,25,26,28,30,31,32,33,35,37,38,48,49,52,53,55,57],
 [2,5,9,12,14,18,19,25,26,29,34,35,36,40,41,42,48,49,51,56,59],
 [5,7,9,11,14,15,17,18,21,25,27,32,34,39,43,45,48,52,53,56,62],
 [9,12,13,14,24,25,26,27,28,29,30,40,42,44,46,47,52,54,58,62,63]
]]

def rank(a,p):
    a=[[x%p for x in row] for row in a]
    if not a: return 0
    r=0
    for j in range(len(a[0])):
        z=next((z for z in range(r,len(a)) if a[z][j]),None)
        if z is None: continue
        a[r],a[z]=a[z],a[r]
        inv=pow(a[r][j],-1,p)
        a[r]=[x*inv%p for x in a[r]]
        for z in range(len(a)):
            if z!=r and a[z][j]:
                b=a[z][j]
                a[z]=[(x-b*y)%p for x,y in zip(a[z],a[r])]
        r+=1
        if r==len(a): break
    return r

def gram(g,w,p):
    k=len(g[0])
    return [[sum(w[z]*g[z][i]*g[z][j] for z in range(len(g)))%p
             for j in range(k)] for i in range(k)]

def nullspace(a,p):
    a=[[x%p for x in row] for row in a]
    n=len(a[0]); r=0; pivots=[]
    for j in range(n):
        z=next((z for z in range(r,len(a)) if a[z][j]),None)
        if z is None: continue
        a[r],a[z]=a[z],a[r]
        inv=pow(a[r][j],-1,p)
        a[r]=[x*inv%p for x in a[r]]
        for z in range(len(a)):
            if z!=r and a[z][j]:
                b=a[z][j]
                a[z]=[(x-b*y)%p for x,y in zip(a[z],a[r])]
        pivots.append(j); r+=1
        if r==len(a): break
    ans=[]
    for j in range(n):
        if j in pivots: continue
        v=[0]*n;v[j]=1
        for i,c in enumerate(pivots): v[c]=-a[i][j]%p
        ans.append(v)
    return ans

def matching(rows,neighbors):
    rows=set(rows); owner={}
    def aug(c,seen):
        for r in sorted(rows & neighbors[c]):
            if r in seen: continue
            seen.add(r)
            if r not in owner or aug(owner[r],seen):
                owner[r]=c; return True
        return False
    for c in range(len(neighbors)): aug(c,set())
    return len(owner)

def support_audit():
    mins=[min(len(set().union(*(BLOCKS[i] for i in s)))
              for s in combinations(range(7),h)) for h in range(1,8)]
    assert mins==[21,34,43,49,53,57,61]
    for h,u in enumerate(mins,1):
        assert u>=2*h and max(0,u-32)+2>=2*h
    neighbors=[BLOCKS[j//2] for j in range(14)]+[set(range(64)) for _ in range(20)]
    assert matching(range(64),neighbors)==34
    errors=[]
    for b in BLOCKS:
        for x in b:
            e=b-{x}; a=set(range(64))-e
            assert len(a)==44 and matching(a,neighbors)==33
            errors.append(tuple(sorted(e)))
    assert len(set(errors))==147
    base_bound=34*comb(64,32)+34+147*33+7*comb(21,2)*2+147*2+4*comb(147,2)
    double_bound=32*comb(128,64)+64
    square_double_bound=2*double_bound
    assert max(base_bound,square_double_bound)<P
    assert 128-2*20==88 and 147>128
    return dict(union_minima=mins,base_rays=147,base_degree_bound=base_bound,
                doubled_degree_bound=double_bound,
                squared_parameter_degree_bound=square_double_bound,
                doubled_n=128,doubled_k=64,doubled_threshold=88)

def exact_non_rs_control():
    # C0=RS_2 on 1,2,3,4. B is a basis of its ordinary orthogonal code.
    p=257
    a=[[1,x] for x in [1,2,3,4]]
    b=[[1,2],[-2,-3],[1,0],[0,1]]
    assert all(sum(a[z][i]*b[z][j] for z in range(4))%p==0
               for i in range(2) for j in range(2))
    for m in [a,b]:
        assert all(rank([m[z] for z in s],p)==2 for s in combinations(range(4),2))
    omega=[pow(3,32*j,p) for j in range(8)]
    assert len(set(omega))==8 and all(pow(x,8,p)==1 for x in omega)
    answer=None
    for ts in combinations(range(1,16),4):
        theta=[t*t%p for t in ts]
        g=[a[i]+[(sign*theta[i]*x)%p for x in b[i]]
           for sign in [1,-1] for i in range(4)]
        weights=[sign*pow(theta[i],-1,p)%p for sign in [1,-1] for i in range(4)]
        if not all(rank([g[z] for z in s],p)==4 for s in combinations(range(8),4)):
            continue
        assert rank(gram(g,weights,p),p)==0
        shifted=gram(g,[weights[i]*omega[i]%p for i in range(8)],p)
        if rank(shifted,p)<=1: continue
        roots=[]
        for i in range(8):
            ratio=weights[i]*pow(omega[i],-1,p)%p
            roots.append(next(s for s in range(1,p) if s*s%p==ratio))
        gs=[[roots[i]*c%p for c in g[i]] for i in range(8)]
        assert rank(gram(gs,omega,p),p)==0
        assert rank(gram(gs,[x*x%p for x in omega],p),p)>1
        assert all(rank([gs[z] for z in s],p)==4 for s in combinations(range(8),4))
        answer=dict(p=p,theta=theta,domain=omega,generator_rows=gs,
                    weighted_gram_rank=0,first_shifted_gram_rank=rank(shifted,p),
                    mds_minors_checked=comb(8,4))
        break
    assert answer is not None
    return answer

def rs_shift_audit():
    # Exact basis Gram matrices, including all shifts in the proved range.
    controls=[]
    for p,n,generator in [(257,8,3),(257,16,3),(257,64,3),(P,16,303645430271030343624574566109998498685964493478)]:
        k=n//2
        gen=pow(generator,(p-1)//n,p) if p==257 else pow(generator,(2**30)//n,p)
        xs=[pow(gen,j,p) for j in range(n)]
        assert len(set(xs))==n
        g=[[pow(x,j,p) for j in range(k)] for x in xs]
        for s in range(k+1):
            actual=gram(g,[pow(x,s+1,p) for x in xs],p)
            expected=[[n%p if i+j==n-s-1 else 0 for j in range(k)] for i in range(k)]
            assert actual==expected and rank(actual,p)==s
        # Recover an orbit generator from the code alone, using a scrambled
        # basis and nonconstant coordinate signs (which preserve beta=x).
        gp=[[(-1)**i*sum(g[i][d]*(1 if d==j else d+j+1 if d>j else 0)
                         for d in range(k))%p for j in range(k)] for i in range(n)]
        equations=[]
        for j in range(1,k):
            equations.extend(gram(gp,[pow(x,j+1,p) for x in xs],p))
        ns=nullspace(equations,p)
        assert len(ns)==1
        v=[sum(gp[i][j]*ns[0][j] for j in range(k))%p for i in range(n)]
        assert all(v)
        orbit=[[v[i]*pow(xs[i],j,p)%p for j in range(k)] for i in range(n)]
        assert rank(orbit,p)==k
        assert rank([gp[i]+orbit[i] for i in range(n)],p)==k
        assert len(set(x*x%p for x in v))==1
        gu=[[(-1)**i*c%p for c in gp[i]] for i in range(n)]
        # All finite residues of the 2-by-2 Cauchy determinant, not merely
        # its value at a few field points. The two columns are independent.
        invn=pow(n,-1,p)
        for i,x in enumerate(xs):
            residue=0
            for j,y in enumerate(xs):
                if i==j: continue
                minor=(gu[i][0]*gu[j][1]-gu[i][1]*gu[j][0])%p
                residue += y*invn*minor*minor*pow(x-y,-1,p)
            assert residue%p==0
        # Verify the full residue identity at three non-domain parameters,
        # directly in the finite field, after a dense basis change.
        checked=0
        for t in range(p):
            if t in xs: continue
            weights=[x*pow(n,-1,p)*pow(t-x,-1,p)%p for x in xs]
            # Values of gp's polynomial columns include its signs, so the
            # signed code itself has beta=x, but the rational identity in
            # (4) applies to ordinary RS values. Use unsigned basis.
            h=[sum(pow(t,d,p)*(1 if d==j else d+j+1 if d>j else 0)
                   for d in range(k))%p for j in range(k)]
            actual=gram(gu,weights,p)
            expected=[[h[i]*h[j]*pow((pow(t,n,p)-1)%p,-1,p)%p
                       for j in range(k)] for i in range(k)]
            assert actual==expected and rank(actual,p)<=1
            checked+=1
            if checked==3: break
        controls.append(dict(p=p,n=n,shifts_checked=k+1,
                             reconstructed_krylov_basis_rank=k,
                             squared_minor_residues_checked=n,
                             residue_evaluation_checks=checked))
    return controls

if __name__=='__main__':
    print(json.dumps(dict(status='PASS_EXACT_FINITE_CONTROLS_WRITTEN_GENERAL_PROOFS',
       support=support_audit(),non_rs_control=exact_non_rs_control(),
       rs_shift_controls=rs_shift_audit(),
       scope='No numerical 128-length code matrix, no RS counterexample, no production count bound, no Lean proof.'),sort_keys=True))
