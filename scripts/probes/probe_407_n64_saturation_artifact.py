# INDEPENDENT, careful verification of the claimed n=64 counterexample at p=2113.
p=2113; n=64; HALF=32
print("p mod 64 =", p%64, "(need 1)")
# find a primitive 64th root g: order exactly 64
assert (p-1)%n==0
e=(p-1)//n
g=None
for a in range(2,p):
    cand=pow(a,e,p)
    # order divides 64; need exact order 64 <=> cand^32 = -1
    if pow(cand,n,p)==1 and pow(cand,HALF,p)==p-1:
        g=cand; break
print("g =",g,"  g^64 mod p =",pow(g,64,p),"  g^32 mod p =",pow(g,32,p),"(need p-1=%d)"%(p-1))
# verify mu_64 are distinct
mu=[pow(g,j,p) for j in range(n)]
print("mu_64 distinct:", len(set(mu))==n)

for cfg in [(0,2,5,12,40,58),(0,3,10,38,56,62)]:
    print("\n=== config", cfg, "===")
    # antipodal-free?
    af = all(((j+HALF)%n) not in set(cfg) for j in cfg)
    print("  antipodal-free:", af)
    us=[mu[j] for j in cfg]
    s1=sum(us)%p; s3=sum(pow(u,3,p) for u in us)%p
    print("  sum u  =",s1,"(need 0)")
    print("  sum u^3=",s3,"(need 0)")
    i2=pow(2,p-2,p)
    e2=(-i2*sum(pow(u,2,p) for u in us))%p
    print("  e2 = -1/2 sum u^2 =",e2)
    # Sigma_3 = sums of 3 distinct mu_32 elements
    from itertools import combinations
    mu32=[pow(g,2*l,p) for l in range(HALF)]   # squares = mu_32
    print("  mu_32 distinct:", len(set(mu32))==HALF)
    Sig=set(sum(W)%p for W in combinations(mu32,3))
    print("  |Sigma_3| =",len(Sig))
    print("  e2 in Sigma_3:", e2 in Sig, "  <-- if False, this REFUTES")
    # cross-check via Vieta: is e2 actually the bad scalar? verify the genuine coset-union e2 values
    # also report: nearest check - is e2 maybe a sum allowing repeats or 2-subset?
    Sig2=set(sum(W)%p for W in combinations(mu32,2))
    print("  e2 in Sigma_2 (2-subset):", e2 in Sig2)
