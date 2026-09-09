"""Independent full-partition census: no imports from either source checker.

Use cached inverse evaluations and equal-ratio buckets; evaluate all 16 nodes
of every compatible assignment before classifying, with no algebraic pruning.
"""
from itertools import combinations, product
from collections import Counter, defaultdict
from fractions import Fraction
import json, time

P = 365375409332725729550921208179070755120141565953
G = 303645430271030343624574566109998498685964493478
X = [pow(G, (1 << 26)*j, P) for j in range(16)]
assert len(set(X)) == 16 and pow(X[1], 8, P) == P-1

def table(degree):
    ans = {}
    for ids in combinations(range(16), degree):
        values = []
        for x in X:
            val = 1
            for i in ids:
                val = val * (x-X[i]) % P
            values.append(val)
        ans[ids] = values
    return ans

def set_partitions(n):
    if n == 0:
        yield []
    else:
        for part in set_partitions(n-1):
            yield part+[[n-1]]
            for k in range(len(part)):
                yield [block+[n-1] if i == k else block for i,block in enumerate(part)]

def run():
    start = time.time()
    danger = []
    for f in range(8):
        for h in product(range(8), repeat=4):
            if h != tuple(sorted(h, reverse=True)):
                continue
            if all(f+h[i]+h[j] <= 7 for i,j in combinations(range(4),2)):
                if 3*sum(h)+4*f > 36:
                    danger.append((f,h))
    assert danger == [(0,(4,3,3,3)), (1,(3,3,3,2)), (1,(3,3,3,3))]
    state_count = 0
    for blocks in set_partitions(4):
        sizes = list(map(len,blocks))
        beta = 8+3*(3 in sizes)+4*(4 in sizes)
        nonroot_states = [(int(len(blocks)>1),size) for size in sizes]
        nonroot_states.append((len(blocks),0))
        for d,c in nonroot_states:
            assert 2*d+3*c <= beta
            state_count += 1
        # At a Q root, the received pair either equals the zero source pair
        # or agrees with none of the four identical source pairs.
        for d,c in [(0,4),(1,0)]:
            assert 2*d+3*c <= beta+4
            state_count += 1
    threes, fours = table(3), table(4)
    inverse = {ids:[pow(v,-1,P) if v else 0 for v in vals] for ids,vals in threes.items()}
    items = list(threes)
    counts = Counter()
    incidences = Counter()
    exceptional_profiles = Counter()
    for bi,bids in enumerate(items):
        bv = threes[bids]
        bset = set(bids)
        for cids in items[bi+1:]:
            if bset.intersection(cids):
                continue
            counts['unordered_B_C'] += 1
            cv, ci = threes[cids], inverse[cids]
            free = sorted(set(range(16)).difference(bids,cids))
            buckets = defaultdict(list)
            for d in free:
                buckets[bv[d]*ci[d] % P].append(d)
            counts['all_D_pairs'] += len(free)*(len(free)-1)//2
            for lam, bucket in buckets.items():
                for d,e in combinations(bucket,2):
                    counts['compatible_D_pairs'] += 1
                    avail = [j for j in free if j not in (d,e)]
                    dxinv = pow(X[e]-X[d],-1,P)
                    for aids in combinations(avail,4):
                        counts['all_full_partitions'] += 1
                        av = fours[aids]
                        yd, ye = av[d]*ci[d] % P, av[e]*ci[e] % P
                        slope = (ye-yd)*dxinv % P
                        intercept = (yd-slope*X[d]) % P
                        assert slope or intercept
                        triple_types = Counter()
                        quads = 0
                        profile = []
                        for j,x in enumerate(X):
                            values = (0, av[j]*bv[j] % P, lam*av[j]*cv[j] % P,
                                      bv[j]*cv[j]*(intercept+slope*x) % P)
                            groups = defaultdict(list)
                            for source,value in enumerate(values):
                                groups[value].append(source)
                            for group in groups.values():
                                if len(group)==3:
                                    triple_types[tuple(group)] += 1
                                if len(group)==4:
                                    quads += 1
                            profile.append((max(map(len,groups.values())),len(groups)))
                        h = tuple(sorted((triple_types[t] for t in combinations(range(4),3)), reverse=True))
                        incidences[(quads,h)] += 1
                        if quads or sum(h)>12:
                            exceptional_profiles[tuple(sorted(profile))] += 1
    assert dict(counts) == {'unordered_B_C':80080,'all_D_pairs':3603600,
                            'compatible_D_pairs':8800,'all_full_partitions':616000}
    assert dict(incidences) == {(0,(4,3,3,2)):609280,(1,(3,3,3,2)):6720}
    certificates=[]
    for profile,count in exceptional_profiles.items():
        lam=Fraction(3)
        beta=[max(Fraction(classes),int(classes>1)+lam*m) for m,classes in profile]
        z=max(Fraction(0),4*lam-min(beta))
        for (m,classes),b in zip(profile,beta):
            assert b>=classes and b>=int(classes>1)+lam*m
            assert b+z>=4*lam and b+z>=1
        cap=(sum(beta)+z-16)/(4*lam)
        assert cap<=Fraction(67,6)
        certificates.append({'profile':profile,'count':count,'lambda':str(lam),
                             'beta':list(map(str,beta)),'root_extra':str(z),'bound':str(cap)})
    s=1<<26
    assert (136*s-10)//12 == 760567124
    result={'status':'PASS_INDEPENDENT_FULL_PARTITION_CENSUS','counts':dict(counts),
            'incidence_profiles':[{'F':f,'sorted_h':h,'count':count} for (f,h),count in incidences.items()],
            'dangerous_profiles':danger,'local_states_including_root_uncovered':state_count,
            'exceptional_certificates':certificates,'integer_main_core_bound':(136*s-10)//12,
            'elapsed_seconds':time.time()-start}
    print(json.dumps(result,indent=2))

if __name__ == '__main__':
    run()
