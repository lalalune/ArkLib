#!/usr/bin/env python3
"""Exact controls for the restricted locator exclusion; no prize closure."""
from itertools import combinations, product
import json

PRIME = 365375409332725729550921208179070755120141565953
GENERATOR = 303645430271030343624574566109998498685964493478


def rank(rows, p):
    a = [[x % p for x in row] for row in rows]
    if not a:
        return 0
    r = 0
    for j in range(len(a[0])):
        z = next((z for z in range(r, len(a)) if a[z][j]), None)
        if z is None:
            continue
        a[r], a[z] = a[z], a[r]
        inv = pow(a[r][j], -1, p)
        a[r] = [x*inv % p for x in a[r]]
        for z in range(r+1, len(a)):
            s = a[z][j]
            a[z] = [(x-s*y) % p for x, y in zip(a[z], a[r])]
        r += 1
        if r == len(a):
            break
    return r


def projective(d, p):
    # Exactly one representative per nonzero vector modulo scalars.
    return [tuple([0]*i+[1]+list(tail))
            for i in range(d) for tail in product(range(p), repeat=d-i-1)]


def norm(v, p):
    z = next(x for x in v if x % p)
    inv = pow(z, -1, p)
    return tuple(x*inv % p for x in v)


def tensor_sections(p):
    p1 = projective(2, p)
    graphs = unions = 0
    for h in projective(4, p):
        H = [h[:2], h[2:]]
        hrank = rank(H, p)
        points = [(u, v) for u in p1 for v in p1
                  if sum(u[i]*H[i][j]*v[j] for i in range(2) for j in range(2)) % p == 0]
        if hrank == 2:
            assert len(points) == p+1
            assert all(sum(u == q for u, v in points) == 1 for q in p1)
            assert all(sum(v == q for u, v in points) == 1 for q in p1)
            graphs += 1
        else:
            assert hrank == 1 and len(points) == 2*p+1
            fixed_u = [u for u in p1 if all((u, v) in points for v in p1)]
            fixed_v = [v for v in p1 if all((u, v) in points for u in p1)]
            assert len(fixed_u) == len(fixed_v) == 1
            assert all(u == fixed_u[0] or v == fixed_v[0] for u, v in points)
            unions += 1
    assert graphs+unions == p**3+p**2+p+1
    assert unions == (p+1)**2
    # Three independent factors: all proportionality-class possibilities,
    # including three distinct but linearly dependent factors on the other side.
    e0, e1, e2 = (1,0,0), (0,1,0), (0,0,1)
    cases = [([e0,e0,e0], p*p+p+1), ([e0,e0,e1], p+2),
             ([e0,e1,(1,1,0)], 3), ([e0,e1,e2], 3)]
    for factors, expected in cases:
        pure = 0
        for alpha in projective(3, p):
            matrix = [[alpha[i]*x % p for x in factors[i]] for i in range(3)]
            active = [factors[i] for i in range(3) if alpha[i]]
            assert rank(matrix, p) == rank(active, p)
            is_pure = len({norm(v,p) for v in active}) == 1
            assert (rank(matrix,p) == 1) == is_pure
            assert rank(matrix,p) == rank(list(zip(*matrix)),p)
            pure += is_pure
        assert pure == expected
    return {"field": p, "hyperplanes": graphs+unions,
            "projective_graphs": graphs, "opposite_ruling_unions": unions,
            "three_factor_span_cases": len(cases)}


def trim(a, p):
    a = [x % p for x in a]
    while len(a)>1 and not a[-1]:
        a.pop()
    return a or [0]


def add(a, b, p, scale=1):
    return trim([(a[i] if i<len(a) else 0)+scale*(b[i] if i<len(b) else 0)
                 for i in range(max(len(a),len(b)))],p)


def mul(a, b, p):
    c = [0]*(len(a)+len(b)-1)
    for i,x in enumerate(a):
        for j,y in enumerate(b):
            c[i+j] += x*y
    return trim(c,p)


def divmod_poly(a,b,p):
    a=trim(a,p); b=trim(b,p)
    q=[0]*max(1,len(a)-len(b)+1)
    while a != [0] and len(a)>=len(b):
        j=len(a)-len(b); s=a[-1]*pow(b[-1],-1,p)%p
        q[j]=s
        a=add(a,[0]*j+[s*x%p for x in b],p,-1)
    return trim(q,p),a


def gcd(a,b,p):
    while b != [0]:
        a,b=b,divmod_poly(a,b,p)[1]
    return trim([x*pow(a[-1],-1,p)%p for x in a],p)


def lcm(a,b,p):
    q,r=divmod_poly(a,gcd(a,b,p),p)
    assert r == [0]
    return mul(q,b,p)


def compose(f, psi, p):
    a=[0]
    for c in reversed(f):
        a=add(mul(a,psi,p),[c],p)
    return a


def locator(roots,p):
    a=[1]
    for x in roots:
        a=mul(a,[-x,1],p)
    return a


def root_controls():
    p=PRIME
    z=pow(GENERATOR,2**30//16,p)
    assert pow(z,16,p)==1 and pow(z,8,p)==p-1
    omega=[pow(z,j,p) for j in range(16)]
    V=[p-1]+[0]*15+[1]
    assert locator(omega,p)==V
    candidates=[]
    for s in range(4):
        orbit={s+4*j for j in range(4)}
        F=[-pow(z,4*s,p)%p,1]
        for tail in combinations(sorted(set(range(16))-orbit),2):
            Q=locator([omega[j] for j in tail],p)
            W=mul(compose(F,[0,0,0,0,1],p),Q,p)
            roots=orbit|set(tail)
            assert W==locator([omega[j] for j in sorted(roots)],p)
            assert divmod_poly(V,W,p)[1]==[0]
            candidates.append((s,roots,W))
    assert len(candidates)==264 and len({tuple(v[2]) for v in candidates})==264
    forbidden_same_F=0
    for x,y in combinations(candidates,2):
        if x[0]==y[0]:
            assert len(x[1]&y[1])>=4>3
            forbidden_same_F+=1
    # Therefore any pair-gcd<=3 family has at most one per each of four F's.
    assert forbidden_same_F==4*(66*65//2)

    # Positive fixed-Q line control on the actual 28th roots of F113.
    p=113
    z=next(x for x in range(1,p) if pow(x,28,p)==1 and pow(x,14,p)!=1 and pow(x,4,p)!=1)
    omega=[pow(z,j,p) for j in range(28)]
    ys=[pow(z,4*j,p) for j in range(7)]
    psi=[0,0,0,0,1]
    Q=locator([omega[6],omega[13]],p)
    Fs=[locator([ys[0],ys[j]],p) for j in range(1,6)]
    Ws=[mul(compose(F,psi,p),Q,p) for F in Fs]
    V=[p-1]+[0]*27+[1]
    assert all(divmod_poly(V,W,p)[1]==[0] for W in Ws)
    assert rank([w+[0]*(11-len(w)) for w in Ws],p)==2
    for F,G,W,U in [(Fs[i],Fs[j],Ws[i],Ws[j]) for i,j in combinations(range(5),2)]:
        assert gcd(W,U,p)==mul(Q,compose(gcd(F,G,p),psi,p),p)
        assert len(gcd(W,U,p))-1==6>5
    common=[1]
    for W in Ws:
        common=lcm(common,W,p)
    assert len(common)-1==26==5*10-4*6
    return {"length16_field": PRIME,"length16_candidate_count":264,
            "length16_same_F_pairs_rejected":forbidden_same_F,
            "length16_pair_bound_family_max":4,
            "length28_field":113,"length28_line_points":5,
            "length28_pair_gcd_degree":6,"length28_allowed_pair_gcd":5,
            "length28_lcm_degree":26}


def composition_controls():
    rows=[]
    # Include characteristics dividing ell: no separability is needed.
    for p in (2,3,5,7):
        for psi in ([1,1,0,0,1],[1,0,0,0,1]):
            ell,a,r=4,2,2
            columns=[compose([0]*j+[1],psi,p) for j in range(a+1)]
            columns=[[0]*t+v for v in columns for t in range(r+1)]
            matrix=[[v[i] if i<len(v) else 0 for v in columns] for i in range(ell*a+r+1)]
            assert rank(matrix,p)==(a+1)*(r+1)==9
            F=[1,1,1]; H=mul(F,[1,0,1],p)
            V=compose(H,psi,p)
            assert divmod_poly(V,compose(F,psi,p),p)[1]==[0]
            A=mul(F,[0,1],p); B=mul(F,[1,1],p); Q=[1,1,1]
            assert gcd(mul(Q,compose(A,psi,p),p),mul(Q,compose(B,psi,p),p),p)==mul(Q,compose(F,psi,p),p)
            rows.append({"field":p,"psi":psi,"composition_basis_rank":9,
                         "inseparable_composition":p==2 and psi[1]==0})
    return rows


def quadratic_controls():
    rows=[]
    for p in (2,3,5,7):
        # F2-F1=Y and F3-F1=1 yield an explicit degree-one syzygy.
        Fs=[[0,0,0,1],[0,1,0,1],[1,0,0,1]]
        As=[[-1,1],[1],[0,-1]]
        psi=[1,1,1]
        ws=[compose(f,psi,p) for f in Fs]
        syz=[compose(a,psi,p) for a in As]
        value=[0]
        for w,a in zip(ws,syz):
            value=add(value,mul(w,a,p),p)
        assert value==[0] and max(len(a)-1 for a in syz)==2<3
        assert rank([w+[0]*(7-len(w)) for w in ws],p)==3
        cols=[[0]*j+w for w in ws for j in range(3)]
        mat=[[v[i] if i<len(v) else 0 for v in cols] for i in range(9)]
        assert rank(mat,p)==8<9
        rows.append({"field":p,"b":3,"lifted_syzygy_degree":2,
                     "balanced_test_size":9,"balanced_test_rank":8})
    b=178956971; q=(b-1)//2
    assert b%2==1 and q==89478485
    assert 3*(q+1)==268435458 and b+q+1==268435457
    assert 2*q==178956970<b
    return {"finite":rows,"production_q":q,"production_source_dimension":3*(q+1),
            "production_target_dimension":b+q+1,"production_lifted_degree_bound":2*q}


def production():
    n=2**30; b=(n+2)//6
    out=[]
    for h in range(2,29):
        ell=2**h; c=1 if h%2==0 else 2
        assert (2**(30-h)-c)%3==0 and (c*ell+2)%3==0
        a=(2**(30-h)-c)//3; r=(c*ell+2)//3
        assert a>=1 and 0<r<ell
        assert ell*(3*a+c)==n and ell*a+r==2*b and 6*b==n+2
        assert ell*a>b
        assert 6*a>3*a+c
        out.append({"h":h,"ell":ell,"a":a,"c":c,"remainder_degree":r,
                    "full_lift_degree":ell*a,"pair_gcd_bound":b,
                    "five_line_lcm_lower_bound":6*b,
                    "available_domain_degree":n,
                    "graph_lcm_required":6*a,"outer_domain_degree":3*a+c})
    assert len(out)==27
    return out


if __name__=='__main__':
    print(json.dumps({"status":"PASS_NEAR_POWER_LOCATOR_EXCLUSION_CONTROLS",
                      "production_levels":production(),
                      "tensor_sections":[tensor_sections(p) for p in (2,3,5,7)],
                      "common_domain_controls":root_controls(),
                      "composition_controls":composition_controls(),
                      "quadratic_controls":quadratic_controls(),
                      "scope":"Written theorem for restricted common-composition locators; no Lean or prize closure."},indent=2))
