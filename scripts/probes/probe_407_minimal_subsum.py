# For an n=32 spurious config at p=97 (size 6, sum u=sum u^3=0, antipodal-free):
# does it have a proper vanishing SUBSUM? (Mann/DZ apply to MINIMAL relations.)
from itertools import combinations
n=32; HALF=16; p=97
e=(p-1)//n
for a in range(2,p):
    g=pow(a,e,p)
    if pow(g,n,p)==1 and pow(g,HALF,p)==p-1: break
mu=[pow(g,j,p) for j in range(n)]
# find spurious size-6 configs
spur=[]
for S in combinations(range(n),6):
    if any(((j+HALF)%n) in set(S) for j in S): continue
    us=[mu[j] for j in S]
    if sum(us)%p!=0: continue
    if sum(pow(u,3,p) for u in us)%p!=0: continue
    spur.append(S)
    if len(spur)>=3: break
print(f"n=32 p=97: found {len(spur)} sample spurious size-6 configs")
for S in spur:
    us=[mu[j] for j in S]
    # check all proper non-empty subsums for vanishing
    minimal=True; vanishing_subsums=[]
    for r in range(1,6):
        for sub in combinations(range(6),r):
            if sum(us[i] for i in sub)%p==0:
                vanishing_subsums.append((r,[S[i] for i in sub]))
                minimal=False
    print(f"  config exps={S}: MINIMAL(no proper vanishing subsum)={minimal}; vanishing subsums (weight,exps)={vanishing_subsums[:4]}")
