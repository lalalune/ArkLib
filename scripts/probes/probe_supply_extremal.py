# The extremal analysis: maximize Σ C(a_i, k+m+1) s.t. Σ C(a_i,k) ≤ C(n,k), a_i ≤ n.
# Claim: maximizer is a SINGLE large agreement (convexity), giving ≈ C(n,k+m+1) = trivial.
# So the pure packing bound CANNOT beat trivial in worst case → wall needs field structure.
from math import comb

def max_cores_packing(n,k,m):
    a=k+m+1
    budget=comb(n,k)
    # greedy/DP over agreement sizes a..n; ratio C(s,a)/C(s,k) increasing → take largest s
    # single-codeword extreme: largest s with C(s,k) ≤ budget
    best_single=0
    for s in range(a,n+1):
        if comb(s,k)<=budget:
            best_single=max(best_single, comb(s,a))
    # many-small extreme: all at s=a, count = budget/C(a,k)
    L=budget//comb(a,k)
    many_small=L*comb(a,a)  # = L
    trivial=comb(n,a)
    return best_single, many_small, trivial

for (n,k,m) in [(16,4,2),(32,8,4),(64,16,8),(128,32,16),(256,64,20)]:
    bs,ms,tr=max_cores_packing(n,k,m)
    print(f"n={n} k={k} m={m}: single-large={bs}  many-small={ms}  trivial=C(n,a)={tr}  "
          f"| single/trivial={bs/tr:.4f}")
print("\n→ single-large-agreement extreme ≈ trivial: packing bound is WORST-CASE VACUOUS")
print("  (a word near one codeword saturates it) — the supply wall provably needs the")
print("  algebraic constraint on WHICH words appear as bad-scalar lines.")
