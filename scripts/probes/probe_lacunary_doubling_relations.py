# THE STRUCTURAL QUESTION:
# Our object: eta_b = sum_{x in mu_n} e_p(b x), mu_n = {g^0,...,g^{n-1}}, g order n in F_p^*.
# As x ranges over mu_n, the exponents {b*g^j mod p : j=0..n-1} are a GEOMETRIC progression mod p (ratio g).
# A lacunary set {2^k} is a geometric progression with ratio 2 in the INTEGERS (Hadamard gap).
# So mu_n's frequency set IS geometric (ratio g) -- but mod p, NOT in Z. Lacunarity (Hadamard gap n_{k+1}/n_k>=q)
# requires the gaps to grow in Z; mod p they WRAP. The wrap is exactly the obstruction.
#
# Check: for g of order n=2^mu, are the n exponents {g^j mod p} "lacunary-like" (large pairwise ratios, no small
# additive relations) up to some level, then wrap?
import math
def mu_set(n,p):
    def order(a):
        o=1; x=a%p
        while x!=1: x=(x*a)%p; o+=1
        return o
    for cand in range(2,p):
        if order(cand)==n: g=cand;break
    return g,[pow(g,j,p) for j in range(n)]

# The Aistleitner et al sequence n_k=2^k: solutions to n_{k+1}=2 n_k (i.e. 2*2^k = 2^{k+1}) are the SAME
# Diophantine relations 2 a = b that create the cubic term. For mu_n, the analogous relations are
# additive relations among {g^j}: g^a + g^a = g^b  i.e. 2 g^a = g^b mod p. Count them.
for n,p in [(16,65537)]:
    g,S=mu_set(n,p)
    Sset=set(S)
    # 3-term relations 2 g^a == g^b (the "doubling" Diophantine eqn = cubic-term source in lacunary MGF)
    doublings=[(a,b) for a in range(n) for b in range(n) if (2*S[a])%p==S[b]]
    # additive collisions g^a + g^c == g^b + g^d (E_2 quadruples beyond trivial)
    print(f"n={n} p={p} g={g}")
    print(f"  doubling relations 2*g^a=g^b mod p: {len(doublings)}  (lacunary n_k=2^k has ~N of these -> cubic term)")
    print(f"  => {'PRESENT' if doublings else 'ABSENT'}: additive structure breaking pure-independence")
    # The KEY: char-0 (no wrap) the n-th roots zeta^j satisfy 2 zeta^a = zeta^b? Never (|2 zeta^a|=2, |zeta^b|=1).
    # So char-0 has NO doubling relations -> char-0 is MORE independent than the lacunary cos sequence!
    # That's why E_r^char0 <= Wick (and even sub-r! sometimes). The wrap mod p REINTRODUCES doublings.
    print("  char-0 (roots of unity in C): 2*zeta^a=zeta^b impossible (modulus 2 vs 1) => NO doublings, cleaner than {2^k}")
