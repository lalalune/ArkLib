from itertools import combinations
p=2013265921
import math
for n in [8,16,32]:
    h=pow(31,(p-1)//n,p); mu=[pow(h,i,p) for i in range(n)]
    z3=sum(1 for T in combinations(mu,3) if sum(T)%p==0); z4=sum(1 for T in combinations(mu,4) if sum(T)%p==0)
    print(f"mu_{n}: 3-term sum0={z3}; 4-term sum0={z4}=C({n//2},2)={math.comb(n//2,2)}")
