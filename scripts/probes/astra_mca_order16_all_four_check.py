"""Exact production-field census for four degree-seven source optimality.

Only the common-factor/carrier mechanism is bounded; this is not universal MCA
safety. See docs/kb/astra_mca_order16_all_four-2026-09-08.md.
Standard library only. Use --output to retain a reproducible census receipt.

Factorization removes the four-root A factor from the compatibility equation:
W1=AB, W2=lambda AC, W3=BC L. At the two D nodes lambda=B/C
must agree, and L is the unique interpolant of A/C there.
"""
from pathlib import Path
from itertools import combinations
from collections import Counter
from fractions import Fraction
import argparse, json, time
P=365375409332725729550921208179070755120141565953
G=303645430271030343624574566109998498685964493478
eta=pow(G,2**26,P);xs=[pow(eta,j,P) for j in range(16)]
HERE=Path(__file__).resolve().parent
assert pow(eta,8,P)==P-1 and len(set(xs))==16

def mul(a,b):
    c=[0]*(len(a)+len(b)-1)
    for i,v in enumerate(a):
        for j,w in enumerate(b):c[i+j]=(c[i+j]+v*w)%P
    return c

def ev(w,x):
    r=0
    for a in reversed(w):r=(r*x+a)%P
    return r

def roots(ids):
    w=[1]
    for j in ids:w=mul(w,[-xs[j],1])
    return w

def tab(d):
    out={}
    for ids in combinations(range(16),d):
        w=roots(ids)
        out[ids]=(sum(1<<j for j in ids),w,[ev(w,x) for x in xs])
    return out

def partition(vals):
    out=[]
    for j in range(16):
        ds={}
        for i in range(4):ds.setdefault(vals[i][j],[]).append(i)
        out.append(tuple(tuple(g) for g in ds.values()))
    return tuple(out)

def uniform_bound(ps):
    best=None;certificate=None
    for lam in (Fraction(1,2),Fraction(1),Fraction(3,2),Fraction(2),Fraction(3),Fraction(4),Fraction(6)):
        beta=[max(1+lam*max(map(len,gs)),len(gs)) for gs in ps]
        root_extra=max(Fraction(0),4*lam-min(beta))
        for b,gs in zip(beta,ps):
            assert b>=len(gs)  # uncovered direction count
            assert all(b>=int(len(gs)>1)+lam*len(g) for g in gs)
            assert b+root_extra>=4*lam  # common-root credit
        bound=(sum(beta)+root_extra-16)/(4*lam)
        if best is None or bound<best:
            best=bound
            certificate={'lambda':str(lam),'beta':list(map(str,beta)),
                'root_extra':str(root_extra),'bound':str(bound)}
    return best,certificate

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, help="Write the exact census receipt here")
    args=parser.parse_args()
    started=time.time();stats=Counter();hist=Counter()
    threes=tab(3);fours=tab(4)
    triples=list(threes)
    seen={};bound_cache={}
    for bi,Bids in enumerate(triples):
        bm,B,Bv=threes[Bids]
        for Cids in triples[bi+1:]:
            cm,C,Cv=threes[Cids]
            if bm&cm:continue
            stats['disjoint_unordered_B_C']+=1
            left=[j for j in range(16) if not (bm|cm)&(1<<j)]
            for d0,d1 in combinations(left,2):
                stats['ratio_tests']+=1
                if (Bv[d0]*Cv[d1]-Bv[d1]*Cv[d0])%P:continue
                stats['ratio_equal_D_pairs']+=1
                lam=Bv[d0]*pow(Cv[d0],-1,P)%P
                assert lam and Bv[d1]==lam*Cv[d1]%P
                cinv=[pow(Cv[j],-1,P) for j in (d0,d1)]
                xiv=pow(xs[d1]-xs[d0],-1,P)
                remaining=[j for j in left if j not in (d0,d1)]
                third_D=[j for j in remaining if (Bv[j]*Cv[d0]-Bv[d0]*Cv[j])%P==0]
                # B-lambda C is a nonzero cubic, so its level has <=3 nodes.
                assert len(third_D)<=1
                for Aids in combinations(remaining,4):
                    stats['factor_assignments']+=1
                    am,A,Av=fours[Aids]
                    lv=[Av[j]*iv%P for j,iv in zip((d0,d1),cinv)]
                    slope=(lv[1]-lv[0])*xiv%P
                    L=[(lv[0]-slope*xs[d0])%P,slope]
                    quad=any(ev(L,xs[j])==0 for j in Aids)
                    extra_D=any(j not in Aids and Cv[j]*ev(L,xs[j])%P==Av[j] for j in third_D)
                    if not quad and not extra_D:
                        # Other triple types cannot grow: the four A nodes plus
                        # any fourth B or C node would give eight roots to a
                        # nonzero degree-seven source. Thus T=12 and F=0.
                        # Exact local dual: 2D+3 sum(C_i) <=164s+4r.
                        # With r<=s-2,D>=16s+1 this excludes an improving core.
                        stats['triple_count_dual_prunes']+=1
                        continue
                    stats['quad_or_thirteenth_triple']+=1
                    stats['has_quadruple']+=int(quad)
                    stats['has_thirteenth_required_triple']+=int(extra_D)
                    vals=[[0]*16,
                          [a*b%P for a,b in zip(Av,Bv)],
                          [lam*a*c%P for a,c in zip(Av,Cv)],
                          [b*c*ev(L,x)%P for b,c,x in zip(Bv,Cv,xs)]]
                    if len(set(map(tuple,vals)))<4:
                        stats['coincident_sources']+=1;continue
                    ps=partition(vals)
                    # The six pair-equality bits uniquely identify a partition.
                    pairs=list(combinations(range(4),2))
                    key=bytes(sum(1<<k for k,(a,b) in enumerate(pairs) if any(a in g and b in g for g in gs)) for gs in ps)
                    if key in seen:
                        stats['repeat_partitions']+=1;continue
                    seen[key]=1
                    profile=tuple(sorted((max(map(len,gs)),len(gs)) for gs in ps))
                    if profile not in bound_cache:
                        canonical_ps=tuple(sorted(ps,key=lambda gs:(max(map(len,gs)),len(gs))))
                        bound_cache[profile]=uniform_bound(canonical_ps)
                    ub,certificate=bound_cache[profile]
                    hist[str(ub)]+=1
                    assert ub <= Fraction(67,6), "New exceptional profile needs a certificate"
                    stats['uniform_dual_cannot_improve']+=1
    receipt={'scope':'Exact exhaustive seed compatibility for disjoint triple sets of sizes (4,3,3,2) on production mu16; every possible nonzero distinct tuple in this specified factor family is represented up to common scalar. The finite degree/root constraints and common-carrier allocation are the only claims.',
        'prime':P,'eta16':eta,'stats':dict(stats),'unique_partition_uniform_upper_histogram':dict(hist),
        'exceptional_profile_certificates':[{'profile':profile,**cert} for profile,(bound,cert) in bound_cache.items()],
        'seconds':time.time()-started}
    assert stats['ratio_tests']==3603600
    assert stats['factor_assignments']==616000
    assert stats['triple_count_dual_prunes']==609280
    assert stats['has_quadruple']==6720
    assert stats['has_thirteenth_required_triple']==0
    assert sum(hist.values())==6720
    if args.output:
        args.output.write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps(receipt,indent=2),flush=True)

if __name__=='__main__':main()
