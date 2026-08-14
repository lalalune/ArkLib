"""
probe_d3_cotlar_sparsity.py — D3 lane second batch.

(A) Cotlar-Stein on a NEW partition (by 2-adic valuation of b), distinct from the C26 block
    partition that was already refuted (Gram 2.0-2.2). Decompose the convolution operator
    T (multiplication by eta in time = Cayley adjacency) into pieces T_j indexed by v_2(b)=j,
    test the Cotlar-Stein almost-orthogonality sum  sum_j sup_k ||T_j^* T_k||^{1/2}. If it stays
    O(sqrt(n log)) the AO route SURVIVES; if it reinforces (>> M) it is REFUTED like C26.

(B) Spectral sparsity / frame: is the peak |eta_b| achieved on a SPARSE set of b (so an
    uncertainty/frame bound localizes it)? Count #{b : |eta_b| >= M/2} and #{b : |eta_b|>=M/sqrt2}.
    If the near-peak set is tiny (rank-few), a sparsity/restricted-isometry bound could pin M;
    if it is a positive fraction of p, no sparsity gain (white-noise spectrum confirmed).
"""
import math, numpy as np
from prize_workspace import Workspace, isprime

def make_W(n, idx):
    for m in range(idx, idx*40):
        p = n*m + 1
        if isprime(p): return Workspace(n, p)
    return None

def v2(x):
    j=0
    while x % 2 == 0 and x>0: x//=2; j+=1
    return j

GRID=[]
for mu in range(3,9):
    n=2**mu
    for idx in (n,4*n):
        if n*idx*40 < 3_000_000: GRID.append((n,idx))

print(f"{'n':>5} {'p':>8} {'M':>8} {'CS_partition_count':>5} {'#|eta|>=M/2':>11} {'frac>=M/2':>10} {'#>=M/r2':>8} {'fracTopMass':>11}")
for n,idx in GRID:
    W=make_W(n,idx)
    if W is None: continue
    p=W.p; M=W.M
    mag=np.sqrt(W.mag2[1:])      # |eta_b|, b=1..p-1
    bvals=np.arange(1,p)

    # (B) sparsity of near-peak set
    near = (mag >= M/2).sum()
    nearr2 = (mag >= M/math.sqrt(2)).sum()
    # mass concentrated in top-sqrt(p) frequencies (frame/sparsity surrogate):
    srt=np.sort(mag)[::-1]
    topk=int(math.sqrt(p))
    topmass = (srt[:topk]**2).sum()/ (mag**2).sum()

    # (A) Cotlar-Stein on valuation partition: group b by v_2(b). The Cayley operator's
    # spectral pieces are the |eta_b| restricted to each valuation class. Almost-orthogonality
    # surrogate: AO_sum = sum_j (max_{b in class j} |eta_b|).  If AO_sum ~ M (one class dominates)
    # the pieces are orthogonal-good; if AO_sum >> M (many classes each near M) they reinforce.
    classes={}
    for b,mb in zip(bvals,mag):
        j=v2(b); classes[j]=max(classes.get(j,0.0),mb)
    AO_sum=sum(classes.values())
    print(f"{n:>5} {p:>8} {M:>8.2f} {AO_sum/M:>5.2f} {near:>11} {near/(p-1):>10.4f} {nearr2:>8} {topmass:>11.4f}")
