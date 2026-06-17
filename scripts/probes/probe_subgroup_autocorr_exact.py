# For S = mu_n a MULTIPLICATIVE SUBGROUP of F_p^*: the dilation autocorrelation
# |S cap rho*S| is EXACTLY: n if rho in mu_n, else 0.
# Reason: x in S and rho*x in S <=> rho = (rho x)/x in S*S^{-1} = S (subgroup).
def subgroup(p, n):
    if (p-1) % n: return None
    g=None
    for c in range(2,p):
        o=1;y=c%p
        while y!=1:
            y=(y*c)%p;o+=1
            if o>p:break
        if o==p-1: g=c;break
    if g is None:return None
    h=pow(g,(p-1)//n,p)
    H=set(pow(h,i,p) for i in range(n))
    if len(H)!=n: return None
    return H

tot=0;bad=0
for (p,n) in [(97,8),(257,16),(673,32),(4129,8),(40961,16),(193,8),(577,16),(7681,32),(12289,16)]:
    H=subgroup(p,n)
    if H is None: continue
    for rho in range(1,p):
        ac=sum(1 for x in H if (rho*x)%p in H)
        expected = n if rho in H else 0
        tot+=1
        if ac!=expected:
            bad+=1
            if bad<=5: print("VIOL p=%d n=%d rho=%d ac=%d exp=%d rho_in_H=%s"%(p,n,rho,ac,expected,rho in H))
print("checked=%d violations=%d"%(tot,bad))
