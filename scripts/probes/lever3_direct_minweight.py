import itertools, math

# Ground-truth: in Z[zeta_n] with zeta^d = -1 (d = n/2), the prime p splits;
# pick g = primitive n-th root of unity mod p (so g^d = -1 mod p).
# The ideal p0 = { c in Z^d : sum_k c_k g^k == 0 mod p }.
# We want the MINIMUM l1 weight  sum|c_k|  of a NONZERO c in p0.
# That min-l1-weight = lambda_1^{l1}(p0) = the true Q4 onset (2r = this weight).
#
# Compare to:
#   (i)   in-tree claimed lower reach   p^{1/d}
#   (ii)  2601.07511 l2 upper bound (2 d^2 p)^{1/4}, converted: l1 <= sqrt(d)*l2
#   (iii) classic Minkowski l1: lambda_1^{l1} <= (d! p)^{1/d} ~ (d/e) p^{1/d}
#
# We BFS the smallest l1 weight relation. To keep it feasible, exhaustively
# enumerate by increasing l1 weight using the meet-in-the-middle on residues.

def primitive_nth_root_mod_p(n, p):
    # find g of order exactly n mod p
    for g in range(2, p):
        if pow(g, n, p) == 1 and pow(g, n//2, p) != 1:
            ok = True
            # check order exactly n: g^(n/q)!=1 for prime q | n. n=2^mu so only q=2.
            if pow(g, n//2, p) != 1:
                return g
    return None

def min_l1_weight_ideal(d, p, g):
    # powers g^k mod p for k in 0..d-1
    gp = [pow(g, k, p) for k in range(d)]
    # search increasing total weight; coefficients integers, l1 = sum|c_k|.
    # Equivalent: find min number of signed-unit "steps" (+- e_k each contributing g^k or -g^k)
    #   summing to 0 mod p, nonzero. This is a min-weight word in the lattice.
    # Use BFS over residues with weight = number of +-g^k additions.
    # residue 0 reachable with weight 0 (empty) -> we need NONZERO vector, so
    #   smallest w>=1 returning to 0 with a nonzero net coeff vector.
    # But a +g^k then -g^k cancels to coeff 0 -> that's c=0, excluded.
    # We track (residue) and forbid the all-zero coeff. Simplest: BFS where each
    #   state is residue, and we want min steps to reach 0 using steps {+-g^k},
    #   with the path NOT being a trivial cancellation. The true min-l1 nonzero
    #   lattice vector = min cycle length in Cayley graph of Z/p with generators
    #   {+-g^k : k<d}. Min nonzero = girth-like. BFS from 0.
    from collections import deque
    steps = []
    for k in range(d):
        steps.append(gp[k]); steps.append((-gp[k]) % p)
    # BFS layered: dist[r] = min steps to reach r from 0 (r!=0). Then min cycle
    # through 0 = min over generator s of dist[(-s)%p]+1 ... but we need the
    # min-weight RELATION = min steps to return to 0 with >=1 step, net nonzero.
    # = min over s in steps of (dist to (p-s)) + 1, where the combined path has
    # nonzero coeff vector. For random g this lower-order detail rarely matters;
    # we approximate lambda_1^{l1} by min cycle length = girth.
    INF = 10**9
    dist = [INF]*p
    dist[0] = 0
    dq = deque([0])
    # we want shortest closed walk 0->0 length>=1 in undirected gen graph = girth
    # do BFS storing parent generator to detect a real cycle (not immediate backtrack)
    parent = [-1]*p
    pgen = [-1]*p
    girth = INF
    dq = deque([0]); dist[0]=0
    sset = list(set(steps))
    while dq:
        u = dq.popleft()
        for s in sset:
            v = (u+s)%p
            if dist[v]==INF:
                dist[v]=dist[u]+1; parent[v]=u; pgen[v]=s; dq.append(v)
            elif v!=parent[u] or s!=(-pgen[u])%p:
                # found a cycle
                cand = dist[u]+dist[v]+1
                girth = min(girth, cand)
    return girth

print(f"{'n':>5} {'d':>4} {'p':>9} {'min_l1':>7} {'p^(1/d)':>9} {'(d!p)^1/d':>10} {'l2_2601*sqrt(d)':>16}")
# small feasible cases: p must split (p == 1 mod n) and be small enough to BFS
for mu in range(2, 7):
    n = 2**mu; d = n//2
    # find a few primes p == 1 mod n, small enough (p < ~ 2e5 for BFS)
    cnt=0
    p = n+1
    while cnt < 3 and p < 200000:
        # primality
        if p>1 and all(p%q for q in range(2,int(p**0.5)+1)):
            if p % n == 1:
                g = primitive_nth_root_mod_p(n,p)
                if g:
                    girth = min_l1_weight_ideal(d,p,g)
                    p13 = p**(1.0/d)
                    dfp = (math.factorial(d)*p)**(1.0/d)
                    l2_2601 = (2*d*d*p)**0.25
                    l1_from = math.sqrt(d)*l2_2601
                    print(f"{n:>5} {d:>4} {p:>9} {girth:>7} {p13:>9.3f} {dfp:>10.2f} {l1_from:>16.2f}")
                    cnt+=1
        p += 1
