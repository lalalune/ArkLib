# Probe W_r = E_r(F_p) - E_r(C) for a THIN 2-power subgroup mu_n < F_p^*, prize regime.
# W_r counts the char-p additive-coincidence EXCESS (zero-sum solutions mod p beyond the char-0 ones).
# Goal: find the Sidon depth ell (first r with W_r != 0) and see how W grows past it vs the char-0 room.
import itertools
def find_subgroup(p, n):
    # mu_n = unique subgroup of order n in F_p^* (n | p-1). generator g of F_p^*, take g^((p-1)/n)
    # find a primitive root
    def is_primroot(g,p):
        seen=set(); x=1
        for _ in range(p-1):
            x=x*g%p; seen.add(x)
        return len(seen)==p-1
    g=2
    while not is_primroot(g,p): g+=1
    h=pow(g,(p-1)//n,p)
    S=[]; x=1
    for _ in range(n):
        S.append(x); x=x*h%p
    return sorted(set(S))

def W_r(S, p, r):
    # E_r(F_p) = #{ (a_1..a_r,b_1..b_r) in S^{2r} : sum a_i = sum b_j mod p }
    # E_r(C)   = same but EXACT integer equality of the multiset-sums lifted... 
    # Standard: E_r(C) counts solutions over Z (no wraparound); E_r(F_p) over Z/p.
    # W_r = E_r(F_p) - E_r(C) = solutions that hold mod p but NOT over Z (wraparound).
    from collections import Counter
    # r-fold sumset multiplicities
    sums_Z = Counter()
    for tup in itertools.product(S, repeat=r):
        sums_Z[sum(tup)] += 1
    Ep = 0; Ez = 0
    # E_r(C): sum over s of mult_Z[s]^2  (exact integer collisions)
    for s,c in sums_Z.items():
        Ez += c*c
    # E_r(F_p): collisions mod p
    sums_p = Counter()
    for s,c in sums_Z.items():
        sums_p[s % p] += c
    for s,c in sums_p.items():
        Ep += c*c
    return Ep, Ez, Ep-Ez

# small prize-ish: n=8, p with 8 | p-1, p >> n (thin). Try p=2^? ... use moderate p for compute.
for n in [8]:
    for p in [73, 89, 97, 113]:   # 8 | p-1
        if (p-1)%n: continue
        S=find_subgroup(p,n)
        if len(S)!=n: continue
        line=f"n={n} p={p} S={S}: "
        for r in range(1,5):
            Ep,Ez,W = W_r(S,p,r)
            line += f"W_{r}={W} "
        print(line)
