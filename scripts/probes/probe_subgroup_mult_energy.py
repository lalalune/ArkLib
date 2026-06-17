# Multiplicative energy of a subgroup H=mu_n:
#   E_x(H) = #{(a,b,c,d) in H^4 : a*b = c*d} = sum_rho |H cap rho*H|^2.
# From the exact autocorr |H cap rho*H| = n*[rho in H]:
#   E_x = sum_{rho in H} n^2 = n * n^2 = n^3.
# Contrast: additive energy of mu_n (char-0 / generic large p) is MINIMAL ~3n^2.
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

ok=0;tot=0
for (p,n) in [(97,8),(257,16),(673,32),(4129,8),(40961,16),(193,8),(577,16),(7681,32)]:
    H=subgroup(p,n)
    if H is None: continue
    Hl=list(H)
    # direct count of mult-energy quadruples
    from collections import Counter
    prod=Counter()
    for a in Hl:
        for b in Hl:
            prod[(a*b)%p]+=1
    Ex=sum(v*v for v in prod.values())
    tot+=1
    expect=n**3
    status = "OK" if Ex==expect else "VIOL"
    if Ex!=expect: print("VIOL p=%d n=%d Ex=%d n^3=%d"%(p,n,Ex,expect))
    else: ok+=1
print("mult-energy = n^3 in %d/%d configs"%(ok,tot))
