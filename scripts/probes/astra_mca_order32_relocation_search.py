"""Exact bounded production-field search extending the earlier two-root relocation.

Only the selected output directory is written. No small-field filter is used.
"""
from pathlib import Path
from itertools import combinations
from collections import Counter
import json, time, argparse

P=365375409332725729550921208179070755120141565953
G=303645430271030343624574566109998498685964493478
eta=pow(G,2**25,P)
xs=[pow(eta,j,P) for j in range(32)]
assert pow(eta,16,P)==P-1 and pow(eta,32,P)==1 and len(set(xs))==32
types=[0,1,-1,2,3,0,-1,3,1,1,-1,2,2,0,-1,3]*2
inside=[j for j,t in enumerate(types) if t>=0]
outside=[j for j,t in enumerate(types) if t<0]
edges=[[(0,1),(0,2)],[(0,1),(0,3)],[(0,2),(0,3)],[(1,2),(1,3)]]

def equations(j,t):
    out=[]
    powers=[pow(xs[j],k,P) for k in range(16)]
    for a,b in edges[t]:
        row=[0]*48
        for i,sgn in ((a,1),(b,-1)):
            if i:row[(i-1)*16:i*16]=[sgn*v%P for v in powers]
        out.append(row)
    return out

eqs=[[equations(j,t) for t in range(4)] for j in range(32)]

def nullspace(a,n):
    a=[r[:] for r in a];piv=[]
    for j in range(n):
        r=len(piv)
        ii=next((i for i in range(r,len(a)) if a[i][j]),None)
        if ii is None:continue
        a[r],a[ii]=a[ii],a[r]
        iv=pow(a[r][j],-1,P);a[r]=[v*iv%P for v in a[r]]
        for i in range(len(a)):
            if i!=r and a[i][j]:
                c=a[i][j];a[i]=[(v-c*w)%P for v,w in zip(a[i],a[r])]
        piv.append(j)
    ker=[]
    for j in range(n):
        if j in piv:continue
        v=[0]*n;v[j]=1
        for i,k in enumerate(piv):v[k]=-a[i][j]%P
        ker.append(v)
    return ker

def add(rows,pivs,ar,d):
    rows=rows[:];pivs=pivs[:]
    for a in ar:
        a=a[:]
        for r,p in zip(rows,pivs):
            if a[p]:
                c=a[p];a=[(v-c*w)%P for v,w in zip(a,r)]
        p=next((j for j,v in enumerate(a) if v),None)
        if p is None:continue
        iv=pow(a[p],-1,P);a=[v*iv%P for v in a]
        rows.append(a);pivs.append(p)
        if len(rows)==d:return None
    return rows,pivs

def ev(w,x):
    ans=0
    for c in reversed(w):ans=(ans*x+c)%P
    return ans

def canonical(v):
    first=next(x for x in v if x)
    iv=pow(first,-1,P)
    return tuple(x*iv%P for x in v)

def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--remove',type=int,default=3)
    ap.add_argument('--add',type=int,default=5)
    ap.add_argument('--limit',type=int,default=0)
    ap.add_argument('--relabel',action='store_true')
    ap.add_argument('--output-dir',type=Path,default=Path('.'))
    args=ap.parse_args()
    stats=Counter();dims=Counter();hits=[];seeds={};start=time.time()
    for removed in combinations(inside,args.remove):
        base=[r for j in inside if j not in removed for r in eqs[j][types[j]]]
        ker=nullspace(base,48);d=len(ker);dims[d]+=1
        eligible=sorted(outside+list(removed)) if args.relabel else outside
        obs={j:[[[sum(v*w for v,w in zip(row,b))%P for b in ker]
                   for row in eqs[j][t]] for t in range(4)] for j in eligible}
        counts=[6]*4
        for j in removed:counts[types[j]]-=1
        def rec(depth,start_idx,rows,pivs,cs,chosen):
            if depth==args.add:
                vs=nullspace(rows,d)
                mapped=[[sum(v[i]*ker[i][k] for i in range(d))%P for k in range(48)] for v in vs]
                # A whole solution space is admissible iff it is not contained in
                # any source-coincidence subspace. Test that condition exactly.
                badpair=next(((a,b) for a,b in combinations(range(4),2)
                    if all(all((0 if a==0 else w[(a-1)*16+k]) ==
                               (0 if b==0 else w[(b-1)*16+k])
                               for k in range(16)) for w in mapped)),None)
                stats['nonzero_tuple_hits']+=1
                if badpair is not None:
                    stats['coincident_space_hits']+=1;return
                assert mapped
                # At most six scalar values per extension are forbidden. The
                # seven deterministic combinations below therefore suffice.
                v=[0]*48
                for w in mapped:
                    choices=[[ (a+c*b)%P for a,b in zip(v,w)] for c in range(7)]
                    def distinct_pairs(q):
                        sources=[(0,)*16]+[tuple(q[i*16:(i+1)*16]) for i in range(3)]
                        return len(set(sources))
                    v=max(choices,key=distinct_pairs)
                # Use polynomial-in-coefficient parameter if the greedy choice
                # did not separate all pairs; each pair excludes <=d-1 choices.
                if distinct_pairs(v)<4:
                    for c in range(6*max(1,d-1)+1):
                        v=[sum(pow(c,i,P)*w[k] for i,w in enumerate(mapped))%P for k in range(48)]
                        if distinct_pairs(v)==4:break
                assert distinct_pairs(v)==4
                v=canonical(v)
                W=[[0]]+[list(v[i*16:(i+1)*16]) for i in range(3)]
                ps=[]
                for j,x in enumerate(xs):
                    groups={}
                    for i,w in enumerate(W):groups.setdefault(ev(w,x),[]).append(i)
                    ps.append(list(groups.values()))
                for j,t in [(j,types[j]) for j in inside if j not in removed]+chosen:
                    assert all(ev(W[a],xs[j])==ev(W[b],xs[j]) for a,b in edges[t])
                record={'removed':removed,'added':chosen,'nullity':len(vs),'polynomials':W,'partitions':ps}
                hits.append(record);seeds.setdefault(v,record)
                return
            for idx in range(start_idx,len(eligible)-(args.add-depth)+1):
                j=eligible[idx]
                for t in range(4):
                    if args.relabel and j in removed and t==types[j]:continue
                    ns=cs[:];ns[t]+=1
                    if any(ns[a]+ns[b]>15 for a,b in combinations(range(4),2)):
                        stats['degree_prunes']+=1;continue
                    stats['rank_extension_attempts']+=1
                    result=add(rows,pivs,obs[j][t],d)
                    if result is None:
                        stats['full_rank_prunes']+=1;continue
                    rec(depth+1,idx+1,*result,ns,chosen+[(j,t)])
        rec(0,0,[],[],counts,[])
        stats['removed_supports']+=1
        if stats['removed_supports']%100==0:
            print('progress',dict(stats),'distinct_seeds',len(seeds),'seconds',round(time.time()-start,2),flush=True)
        if args.limit and stats['removed_supports']>=args.limit:break
    receipt={'scope':'Exact production-field bounded relocation census; no claim about all order32 sources or universal MCA safety.',
        'prime':P,'eta32':eta,'degree_bound':15,'reference_types':types,
        'remove_count':args.remove,'add_count':args.add,'relabel_removed':args.relabel,
        'support_limit':args.limit,'stats':dict(stats),'retained_kernel_nullity_histogram':dict(dims),
        'unique_distinct_seeds':list(seeds.values()),'admissible_hits':hits,'seconds':time.time()-start}
    path=args.output_dir / f'receipt-r{args.remove}-a{args.add}-relabel{int(args.relabel)}-limit{args.limit}.json'
    path.write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps({k:v for k,v in receipt.items() if k not in ('unique_distinct_seeds','admissible_hits')},indent=2),flush=True)

if __name__=='__main__':main()
