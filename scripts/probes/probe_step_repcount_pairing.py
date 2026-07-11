# Probe: structure of r(c) = #{(g1,g2) in mu_n^2 : g1+g2 = c} on THIN proper mu_n in F_p.
# Goal: find an UNCONTESTED structural fact about r(c) for c in G+G (NOT the energy sum).
# Hypotheses to test:
#  H1: r(c) is EVEN for c != 0, c != 2g (the (g1,g2) <-> (g2,g1) involution, fixed pts only on diagonal g1=g2=>c=2g1).
#  H2: the diagonal c=2g (g in mu_n) gives the n "doubling" points; off-diagonal reps pair up.
#  H3: r(c) <= gcd-degree (already proven) -- check tightness on thin mu_n.
#  H4: r(c) for c in G+G, c!=0: is max_c r(c) bounded by a structural quantity (e.g. order of c in some sense)?
# PROPER thin mu_n=2^a only, large primes p>n^3 + Fermat, NEVER n=q-1.
import itertools
def order_subgroup(p, n):
    # mu_n exists iff n | p-1; return generator's powers
    assert (p-1) % n == 0
    # find generator g of F_p^*
    def is_gen(g):
        seen=set(); x=1
        for _ in range(p-1):
            x=(x*g)%p; seen.add(x)
        return len(seen)==p-1
    g=2
    while not is_gen(g): g+=1
    h=pow(g,(p-1)//n,p)  # order n
    return sorted(set(pow(h,j,p) for j in range(n)))

primes_for = {
    4:  [17, 73, 257, 1153],     # n^3=64; 73,257,1153 > 64; 257 Fermat
    8:  [17, 41, 521, 4129],     # n^3=512; 521,4129 > 512
    16: [17, 97, 65537],         # n^3=4096; 65537 Fermat > 4096
}
for n in (4,8,16):
    for p in primes_for[n]:
        if (p-1)%n!=0: continue
        if n==p-1: continue  # never full group
        mu=order_subgroup(p,n)
        # r(c)
        from collections import Counter
        r=Counter()
        for g1 in mu:
            for g2 in mu:
                r[(g1+g2)%p]+=1
        # H1/H2: parity of r(c) vs diagonal
        diag=set((2*g)%p for g in mu)
        h1_fails=0; maxr=0; maxr_c=None
        for c,rc in r.items():
            if c==0: continue
            # off-diagonal count = rc - (number of g with 2g=c)
            ndiag = sum(1 for g in mu if (2*g)%p==c)
            off = rc - ndiag
            if off % 2 != 0:
                h1_fails+=1
            if rc>maxr: maxr=rc; maxr_c=c
        sumset_size=len([c for c in r if c!=0])
        # additive energy E = sum r(c)^2
        E=sum(rc*rc for c,rc in r.items())
        print(f"n={n:2d} p={p:5d}: |G+G\\0|={sumset_size:4d} maxr={maxr} (c={maxr_c}) E={E} E/n^2.5={E/(n**2.5):.3f} H1_offdiag_odd_fails={h1_fails}")
