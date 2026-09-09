"""Independent exact boundary and singleton-list controls; standard library."""
from fractions import Fraction
from itertools import combinations
import json

P=365375409332725729550921208179070755120141565953
G=303645430271030343624574566109998498685964493478
N=2**30
s=N//4
k=N//2
t=3*s-1
assert P//2**128==N
assert 5*t*t-N*(t+4*(k-1))==s*s-10*s+5>0
assert 4*t*t-(N-1)*(t+3*(k-1))==s>0
assert 3*t-N>2*k-2
assert Fraction(s+1,N)==Fraction(1,4)+Fraction(1,N)
assert Fraction(313174699,N)==Fraction(7,24)+Fraction(1,3*N)
assert (N+4)*2**128-P==1361129467683753853853498429520914415615

def mul(a,b):
    out=[0]*(len(a)+len(b)-1)
    for i,x in enumerate(a):
        for j,y in enumerate(b): out[i+j]=(out[i+j]+x*y)%P
    return out

def ev(poly,x):
    out=0
    for c in reversed(poly): out=(out*x+c)%P
    return out

def interp(points,values):
    out=[0]*len(points)
    for i,(x,y) in enumerate(zip(points,values)):
        if not y: continue
        term=[1]
        denom=1
        for j,z in enumerate(points):
            if i!=j:
                term=mul(term,[-z,1])
                denom=denom*(x-z)%P
        factor=y*pow(denom,-1,P)%P
        for j,c in enumerate(term): out[j]=(out[j]+factor*c)%P
    return tuple(out)

def control(n):
    ss,kk=n//4,n//2
    tt=3*ss-1
    gg=pow(G,N//n,P)
    dom=[pow(gg,i,P) for i in range(n)]
    assert len(set(dom))==n and pow(gg,n,P)==1
    rr=dom[:kk-1]
    aa=dom[kk-1:kk-1+ss]
    spike=aa[0]
    c=[1]
    for x in rr: c=mul(c,[-x,1])
    u={x:ev(c,x) if x in aa else 0 for x in dom}
    # Every high-core q has >=tt-1 zero constraints, forcing q=0.
    assert tt-1>=kk
    eligible=[x for x in dom if x!=spike]
    candidates={interp(xs,[u[x] for x in xs]) for xs in combinations(eligible,kk)}
    high=[p for p in candidates if sum(ev(p,x)==u[x] for x in eligible)>=tt]
    assert high==[(0,)*kk]
    support0=[x for x in dom if u[x]==ev(c,x)]
    assert len(support0)==tt and spike in support0
    assert len(support0)-1>=kk
    covered_gamma=(-u[spike])%P
    assert covered_gamma!=0
    support1=[x for x in dom if (u[x]+(covered_gamma if x==spike else 0))%P==0]
    assert len(support1)==tt+2 and spike in support1
    assert len(support1)-1>=kk
    return {'n':n,'interpolated_candidates':len(candidates),'high_core_pairs':1,
            'zero_is_uncovered_bad':True,'covered_bad_count':1,
            'gamma0_support':len(support0),'covered_support':len(support1)}

print(json.dumps({'production_arithmetic_passed':True,
                  'controls':[control(n) for n in (8,16)]},indent=2))
