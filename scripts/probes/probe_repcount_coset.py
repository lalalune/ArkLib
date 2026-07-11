# repCount(c) should be invariant under c -> c*zeta for zeta in mu_n
# and E(G) = (p-1)/n distinct coset-values, each repeated n times (over c != 0)
def test(p, n):
    G = [x for x in range(1,p) if pow(x,n,p)==1]
    Gset=set(G)
    def rep(c): return sum(1 for y in G if (c-y)%p in Gset)
    # coset invariance
    bad=0
    for c in range(1,p):
        for z in G:
            if rep((c*z)%p) != rep(c): bad+=1
    # energy via cosets: sum_{c!=0} rep(c)^2 should = n * sum over coset-reps
    reps_by_cn = {}
    for c in range(1,p):
        reps_by_cn.setdefault(pow(c,n,p), rep(c))
    energy_all = sum(rep(c)**2 for c in range(1,p))
    energy_coset = n * sum(v**2 for v in reps_by_cn.values())
    print(f"p={p} n={n}: coset-inv violations={bad}, E_all(c!=0)={energy_all} == n*sum_coset={energy_coset}: {energy_all==energy_coset}, #cosets={len(reps_by_cn)}=(p-1)/n={ (p-1)//n}")
test(13,4); test(17,8); test(41,8); test(41,10); test(97,16); test(257,16)
