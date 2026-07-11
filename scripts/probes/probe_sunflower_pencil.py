"""Sunflower generalization of pencil_card_core (the clean, exactly-generalizing brick).
Hypothesis: r blocks each size r, pairwise intersection EQUALS a common core T (|T|=M, T subset every block).
Then T-punctured blocks B_i \\ T are pairwise disjoint, size r-M, inside U\\T (size U-M):
  U - M >= r*(r-M)   =>   r*(r-M) + M <= n.
At M=1, T={p}: r*(r-1)+1 <= n  (recovers pencil_card_core EXACTLY).
Johnson extraction: r*(r-M) + M <= n. Since r>=M (else r-M<0; for r<=M block trivially small),
 for r>M:  (r-M)^2 <= r*(r-M) <= n - M < n, so (r-M)^2 < n, i.e. r < M + sqrt(n).
 This is the sub-Johnson->Johnson degradation: r <= M + sqrt(n); M=1 gives r<=1+sqrt(n).
Verify the bound r*(r-M)+M <= n holds for genuine sunflowers, and the (r-M)^2<n extraction.
"""
import random

def run(r, M, n, trials=20000):
    feas = 0
    bound_ok = True
    john_ok = True
    for _ in range(trials):
        if r < M:
            break
        T = set(random.sample(range(n), M)) if M <= n else None
        if T is None:
            break
        # build r blocks: each = T ∪ (r-M distinct petals), petals pairwise disjoint, disjoint from T
        pool = [x for x in range(n) if x not in T]
        need = r*(r-M)
        if need > len(pool):
            break
        random.shuffle(pool)
        blocks = []
        idx = 0
        good = True
        for _i in range(r):
            petals = pool[idx:idx+(r-M)]
            idx += (r-M)
            b = set(T) | set(petals)
            if len(b) != r:
                good = False; break
            blocks.append(b)
        if not good:
            continue
        # verify pairwise intersection == T
        okpair = all((blocks[i] & blocks[j]) == T for i in range(r) for j in range(i+1,r))
        if not okpair:
            continue
        feas += 1
        U = set()
        for b in blocks: U |= b
        Uc = len(U)
        if not (r*(r-M) + M <= n):
            bound_ok = False
        if r > M and not ((r-M)*(r-M) < n):
            john_ok = False
    return feas, bound_ok, john_ok

for (r, M, n) in [(4,1,16),(4,2,16),(5,2,32),(6,2,32),(8,3,64),(3,2,8),(5,1,32),(6,3,64)]:
    f, b, j = run(r, M, n)
    print(f"r={r} M={M} n={n}: feas={f} | r(r-M)+M<=n OK={b} | (r-M)^2<n OK={j}")
