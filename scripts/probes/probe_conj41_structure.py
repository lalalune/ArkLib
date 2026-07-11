#!/usr/bin/env python3
"""
Conj 41 (Open-Set Rank Lemma) STRUCTURE — the clean resolution.
Finding: the (w+1)-clique normal blocks are IDENTICALLY rank-deficient (det(A)==0 for all gamma, all p),
so the clique is exactly the conjecture's ESCAPE config, NOT a generic counterexample. The conjecture's
real content: for NON-clique (generic) m=ceil(2D/c) support configs, rank(A)=min(mc,2D) (det != 0) =>
no kernel => M_true < m => bound floor((2D-1)/c). This probe verifies both halves at large p.
"""
import itertools, random, functools
print = functools.partial(print, flush=True)
# load helpers from the kernel probe (build_A, detmod, normals, vander, kernel_vec, poly_from_roots, ...)
exec(open('scripts/probes/probe_conj41_kernel.py').read().split('print("=== Conj41')[0])
def mv(M,x,p): return [sum(M[i][j]*x[j] for j in range(len(x)))%p for i in range(len(M))]

def test(n,k,clique=None,p=1000003,trials=300,seed=0):
    D=n-k; rng=random.Random(seed)
    # determine w,c from clique if given (clique-> m=|clique| supports of size |clique|-1)
    print(f"\n--- n={n} k={k} D={D} p={p} ---")
    # (A) CLIQUE: det(A) identically zero?  + escape clause holds?
    if clique:
        Es=[tuple(sorted(set(clique)-{a})) for a in clique]; w=len(Es[0]); c=D-w
        bound=(2*D-1)//c
        if w*0+len(Es)*c!=2*D:
            print(f"  clique {clique}: w={w} c={c} m={len(Es)} mc={len(Es)*c} 2D={2*D} (skip det test, not square)")
        else:
            z=sum(1 for _ in range(trials) if (lambda g: detmod(build_A(Es,g,len(clique)>0 and L_(n) and L_(n),D,c,p),p)==0))
        L=list(range(n))
        nz=0
        for _ in range(trials):
            g=rng.sample(range(1,p),len(Es))
            if len(set(g))<len(Es): continue
            if detmod(build_A(Es,g,L,D,c,p),p)!=0: nz+=1
        # escape: ker(A) -> does some support have <Lambda_E, s2>=0 for the kernel?
        g=rng.sample(range(1,p),len(Es)); A=build_A(Es,g,L,D,c,p); kv=kernel_vec(A,p)
        esc=None
        if kv:
            s2=kv[D:]
            esc=[ (E, sum(normals(E,L,D,c,p)[0][j]*s2[j] for j in range(D))%p) for E in Es ]
        print(f"  CLIQUE {clique}: supports={Es} w={w} c={c} bound floor((2D-1)/c)={bound}")
        print(f"    det(A)!=0 over {trials} random distinct-gamma: {nz}/{trials}  => {'GENERIC FULL RANK' if nz>0 else 'det IDENTICALLY 0 (rank-deficient escape config)'}")
        if esc: print(f"    escape <Lambda_E,s2> per support: {[v for _,v in esc]}  (escape holds if some ==0: {any(v==0 for _,v in esc)})")
    # (B) NON-clique generic configs: det(A)!=0 (full rank => M_true<m => bound holds)?
    # pick c so that m=ceil(2D/c) gives mc=2D (square); use the clique's c if given else c=3
    c = D-(len(clique)-1) if clique else 3
    w = D-c
    if w<1 or 2*D % c != 0:
        print(f"  (B) skip non-clique: need c|2D and w>=1 (c={c},w={w})"); return
    m=2*D//c; bound=(2*D-1)//c
    L=list(range(n)); allsub=list(itertools.combinations(range(n),w)); full=0; tot=0
    for _ in range(trials):
        Es=rng.sample(allsub,m)
        # skip if it's a (w+1)-clique (all supports subsets of a common (w+1)-set)
        union=set().union(*Es)
        if len(union)<=w+1: continue
        g=rng.sample(range(1,p),m)
        if len(set(g))<m: continue
        tot+=1
        if detmod(build_A(Es,g,L,D,c,p),p)!=0: full+=1
    print(f"  (B) NON-clique random {m}-support configs (w={w},c={c},m={m}): det(A)!=0 (full rank) "
          f"{full}/{tot}  => {'GENERIC FULL RANK confirmed (=> M_true<m => bound holds)' if full==tot and tot>0 else 'some deficient (investigate)'}")
def L_(n): return list(range(n))

test(12,6,clique=[1,4,5,8])           # tetrahedron c=3 w=3
test(16,8,clique=[0,1,2,5,9])         # 5-clique c=4 w=4 at rate 1/2 (D=8, m=5, mc=20!=16 -> not square; det test skipped)
test(12,6)                            # generic c=3 at rate 1/2
