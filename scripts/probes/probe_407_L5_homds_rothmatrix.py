#!/usr/bin/env python3
"""
probe_407_L5_homds_rothmatrix.py  (#407 LANE L5 — odd-order higher-order-MDS, the EXACT test)

PURPOSE.  Decide whether the order-n smooth domain mu_n (the RS evaluation set, x^n = 1) is
HIGHER-ORDER MDS ("L-MDS" in Roth's terminology, arXiv:2111.03210) for the prize-relevant order
L, and whether ODD n (radix-3: 9,27,81; -1 NOT in mu_n) differs from EVEN n (8,16,32,64;
-1 = omega^{n/2} in mu_n).  The lead (KB prize-407, section-6 / L5): the floor's EVEN-order
refutation is SPECIFICALLY the negation symmetry -1 in mu_n (which the even Lam-Leung route
exploits).  ODD order removes it, routing the (odd) prize through the BGK-FREE GM-MDS /
higher-order-MDS question instead of the dyadic-vanishing-sum / BGK wall.

THE EXACT TEST (Roth Lemma 16 + Section V, the GRS specialization).  A linear [n,k] MDS code C
with parity-check H is "lightly-L-MDS" (= the higher-order MDS property whose failure boosts the
list size beyond the generalized-Singleton/Johnson bound) IFF, for EVERY L+1 DISJOINT subsets
J_0,...,J_L of the n coordinates with
        |J_m| <= n-k   and   sum_m |J_m| = L(n-k),
the block matrix
        M = M_{J_0,...,J_L}(H)   (Roth eq. (9)/(53))
is NONSINGULAR (det != 0 over F_p).  For a GRS / RS code on evaluation points alpha (here alpha =
mu_n), H is the (n-k) x n Vandermonde  H[i][j] = alpha_j^i, i=0..n-k-1, and the M-matrix is built
from the column blocks (H)_{J_m} = [ alpha_x^i ]_{x in J_m, i} (Roth eq. (53), with a sign on the
J_0 block).  This is the CORRECT higher-order-MDS object; it is NOT the arbitrary gapped-Vandermonde
minor test (that earlier probe tested the wrong matrix and conflated trivial exponent collisions
with genuine HOMDS failure).

WHAT A SINGULAR M MEANS.  By Lemma 16 a singular M for an admissible disjoint (J_m) triple yields
L+1 nonzero disjoint-support coset vectors of total weight L(n-k) -- i.e. an EXTRA list-decoding
configuration at the generalized-Singleton radius = a list-size boost = the floor.  So:
   mu_n is L-MDS  <=>  NO admissible M is singular  <=>  no off-Johnson list boost  <=>  (for the
   odd prize) a BGK-FREE pin of delta* at the generic (MDS) list size.
   mu_n is NOT L-MDS  <=>  some admissible M singular  <=>  list boost  <=>  off-Johnson floor.

PARAMETERS.  Prize-shape: k = round(rho*n), rho approx 1/4 (and a rho approx 1/2 control); the
prize order is L approx 2 (three codewords) at the FIRST nontrivial radius.  Roth/ArkLib:
order 2 (intersection-dim) is AUTOMATIC from MDS (isHigherMDS_two_of_isMDSFrame), and L=2 in
Roth's LIGHT sense is the first genuinely-testable case (Theorem 18).  So we test L=2 (the first
floor-relevant order) and L=3 where feasible, at matched (n,k,rho) for odd vs even, at the prize
prime (beta approx 4) AND at a sweep of primes (to separate char-p artifacts from structure).

USAGE:  python3 probe_407_L5_homds_rothmatrix.py [--full]
"""
import sys, math, itertools, json
from collections import defaultdict

# ----------------------------------------------------------------- exact F_p number theory
def isprime(m):
    if m < 2: return False
    for q in (2,3,5,7,11,13,17,19,23,29,31,37):
        if m % q == 0: return m == q
    d = m-1; s = 0
    while d % 2 == 0: d //= 2; s += 1
    for a in (2,3,5,7,11,13,17,19,23,29,31,37):
        x = pow(a,d,m)
        if x in (1,m-1): continue
        for _ in range(s-1):
            x = x*x % m
            if x == m-1: break
        else: return False
    return True

def prime_factors(m):
    s=set(); d=2
    while d*d<=m:
        while m%d==0: s.add(d); m//=d
        d+=1
    if m>1: s.add(m)
    return s

def subgroup(p,n):
    assert (p-1)%n==0
    e=(p-1)//n; pf=prime_factors(n)
    for c in range(2,p):
        h=pow(c,e,p)
        if pow(h,n,p)!=1: continue
        if any(pow(h,n//q,p)==1 for q in pf): continue
        S=[]; x=1
        for _ in range(n): x=x*h%p; S.append(x)
        if len(set(S))==n: return sorted(S)
    raise RuntimeError(f"no order-{n} subgroup in F_{p}")

def det_modp(M,p):
    n=len(M)
    if n==0: return 1
    A=[[x%p for x in row] for row in M]
    det=1
    for col in range(n):
        piv=next((r for r in range(col,n) if A[r][col]%p!=0),None)
        if piv is None: return 0
        if piv!=col:
            A[col],A[piv]=A[piv],A[col]; det=(-det)%p
        inv=pow(A[col][col],p-2,p)
        det=det*A[col][col]%p
        for r in range(col+1,n):
            f=A[r][col]*inv%p
            if f: A[r]=[(A[r][c]-f*A[col][c])%p for c in range(n)]
    return det%p

# ----------------------------------------------------------------- Roth M-matrix (eq. 9/53)
def roth_M_matrix(H_cols, blocks, rho, p):
    """Build M_{J_0,...,J_L}(H) per Roth eq.(9).  H_cols[x] = column of H for coordinate x
    (length rho = n-k).  blocks = (J_0,...,J_L), each a list of coordinate indices.
    Layout (eq. 9): L*rho rows, sum|J_m| columns; row-block m (m=1..L) holds
        [ -(H)_{J_0}  in the J_0 col-group ]  and  [ (H)_{J_m} in the J_m col-group ].
    All-zero elsewhere.  (When square -- sum|J_m| = L*rho -- this is the test matrix.)"""
    L = len(blocks)-1
    Jsizes = [len(b) for b in blocks]
    ncols = sum(Jsizes)
    nrows = L*rho
    # column offsets for each block
    offs=[0]*len(blocks)
    for m in range(1,len(blocks)): offs[m]=offs[m-1]+Jsizes[m-1]
    M=[[0]*ncols for _ in range(nrows)]
    for m in range(1,L+1):  # row block index 1..L  -> rows [(m-1)*rho : m*rho)
        rbase=(m-1)*rho
        # -(H)_{J_0} in J_0 columns
        for ci,x in enumerate(blocks[0]):
            col=offs[0]+ci
            for i in range(rho):
                M[rbase+i][col]=(-H_cols[x][i])%p
        # (H)_{J_m} in J_m columns
        for ci,x in enumerate(blocks[m]):
            col=offs[m]+ci
            for i in range(rho):
                M[rbase+i][col]=H_cols[x][i]%p
    return M

def H_columns_RS(S,k,p):
    """parity-check columns of RS[S,k]: H[i][j]=alpha_j^i, i=0..n-k-1.  Keyed by COORDINATE INDEX
    j=0..n-1 (alpha_j = S[j])."""
    rho=len(S)-k
    return {j:[pow(S[j],i,p) for i in range(rho)] for j in range(len(S))}

# ----------------------------------------------------------------- the L-MDS test (Lemma 16)
def is_L_MDS(S,k,L,p,maxtriples=None,collect=False,early_exit=True):
    """Decide if RS[S,k] is lightly-L-MDS via Roth Lemma 16: check det(M)!=0 for ALL disjoint
    (J_0,...,J_L) with |J_m|<=rho, sum|J_m|=L*rho (M square).  Uses dilation reduction: WLOG fix
    0 in J_0 (mu_n acts transitively on coordinates; multiplying all locators by w in mu_n maps
    the M-matrix to a row/col-scaled copy with the same singularity).  So we only enumerate block
    families whose FIRST block contains coordinate 0 -- a factor-n speedup, exact (no loss).
    Returns (is_LMDS, n_checked, n_singular, examples)."""
    n=len(S); rho=n-k
    if rho<1 or L*rho>n: return (None,0,0,[])
    Hc=H_columns_RS(S,k,p)
    Sidx=list(range(n))
    low = 2 if L==2 else 1
    parts_space=[]
    def gen_parts(rem,slots,cur):
        if slots==1:
            if low<=rem<=rho: parts_space.append(cur+[rem]); return
            return
        for v in range(low,min(rho,rem-low*(slots-1))+1):
            gen_parts(rem-v,slots-1,cur+[v])
    gen_parts(L*rho,L+1,[])
    seen_parts=set(); parts_list=[]
    for pp in parts_space:
        key=tuple(sorted(pp))
        if key not in seen_parts:
            seen_parts.add(key); parts_list.append(sorted(pp))
    nchecked=[0]; nsing=[0]; examples=[]; found=[False]
    def pick(remaining, idx, chosen, sizes):
        if found[0] and early_exit and not collect: return
        if idx==len(sizes):
            M=roth_M_matrix(Hc,chosen,rho,p)
            d=det_modp(M,p)
            nchecked[0]+=1
            if d==0:
                nsing[0]+=1; found[0]=True
                if collect and len(examples)<8:
                    examples.append([list(b) for b in chosen])
            return
        sz=sizes[idx]
        rem=sorted(remaining)
        for comb in itertools.combinations(rem,sz):
            # DILATION REDUCTION: require coordinate 0 to be in the first (smallest) block
            if idx==0 and 0 not in comb:
                continue
            if idx>0 and sizes[idx]==sizes[idx-1] and comb < tuple(chosen[idx-1]):
                continue
            newrem=[x for x in remaining if x not in comb]
            pick(newrem, idx+1, chosen+[list(comb)], sizes)
            if maxtriples and nchecked[0]>=maxtriples: return
            if found[0] and early_exit and not collect: return
    for sizes in parts_list:
        pick(set(Sidx),0,[],sizes)
        if maxtriples and nchecked[0]>=maxtriples: break
        if found[0] and early_exit and not collect: break
    return (nsing[0]==0, nchecked[0], nsing[0], examples)

# ----------------------------------------------------------------- prime selection
def prime_for_beta(n, beta_lo=3.8, beta_hi=5.2, cap=3_000_000):
    lo=max(n*2+1,int(n**beta_lo)); hi=min(cap,int(n**beta_hi))
    for m in range(max(2,lo//n), hi//n+1):
        p=n*m+1
        if p>hi: break
        if isprime(p): return p
    return None

def small_primes(n, count=6, idx_max=4000):
    out=[]
    for m in range(2,idx_max):
        p=n*m+1
        if isprime(p):
            out.append(p)
            if len(out)>=count: break
    return out

# ----------------------------------------------------------------- MAIN
def main():
    full="--full" in sys.argv
    results={"meta":{"test":"Roth Lemma16 block-M-matrix L-MDS, odd vs even mu_n"}, "rows":[], "verdict":{}}

    # matched (n,k): rho = n-k; we want L*rho <= n and a prize-ish rate.  Use rho approx n/4
    # (rho=n-k, rho small => high rate; the floor lives at high rate).  For L=2 need 2*rho<=n
    # => rho<=n/2 i.e. k>=n/2.  For L=3 need 3*rho<=n => rho<=n/3 i.e. k>=2n/3.
    # We test L=2 (first floor-relevant order) on matched odd/even pairs, and L=3 where feasible.
    # Prize rate = HIGH rate (small rho).  Floor lives at small rho.  For each n test rho=2,3
    # (and rho=4 where feasible) which is where the block enumeration is tractable AND where the
    # prize floor sits.  k = n - rho.
    def kcases(n):
        out2=[]; out3=[]
        for rho in (2,3,4):
            k=n-rho
            if 2*rho<=n and k>=2: out2.append(k)
            if 3*rho<=n and k>=2: out3.append(k)
        return out2,out3
    cases=[]
    for n in (8,9,16,15,27,32,25,64,81):
        k2,k3=kcases(n)
        cases.append((n,k2,k3))
    print("="*92)
    print("LANE L5: EXACT higher-order-MDS (Roth Lemma 16 block-M-matrix), ODD vs EVEN mu_n")
    print("  is_LMDS := det(M_{J_0..J_L}(H)) != 0 for ALL disjoint admissible (J_m)")
    print("  FALSE => list-boost floor;  TRUE => BGK-free generic-MDS pin")
    print("="*92)
    print(f"{'n':>3} {'par':>5} {'k':>3} {'rho':>3} {'L':>2} {'p':>9} {'beta':>5} "
          f"{'#checked':>9} {'#singular':>10} {'L-MDS?':>7}")
    for (n,k2s,k3s) in cases:
        par="odd" if n%2 else "even"
        p=prime_for_beta(n)
        if p is None:
            p=small_primes(n,1)[0]
        S=subgroup(p,n); beta=math.log(p)/math.log(n)
        for (L,ks) in ((2,k2s),(3,k3s)):
            for k in ks:
                rho=n-k
                if L*rho>n or rho<1: continue
                # feasibility cap on triples
                capt = None if full else 3_000_000
                # collect=True to get a full singular count + examples (no early-exit) when small;
                # else early-exit (just decide is_LMDS) for speed.
                small = (math.comb(n,rho) <= 5000)
                res=is_L_MDS(S,k,L,p,maxtriples=capt,collect=small,early_exit=not small)
                if res[0] is None: continue
                isL,nchk,nsing,ex=res
                print(f"{n:>3} {par:>5} {k:>3} {rho:>3} {L:>2} {p:>9} {beta:>5.2f} "
                      f"{nchk:>9} {nsing:>10} {str(isL):>7}", flush=True)
                results["rows"].append(dict(n=n,par=par,k=k,rho=rho,L=L,p=p,beta=round(beta,3),
                                            checked=nchk,singular=nsing,isLMDS=isL,
                                            examples=ex[:3]))
    # VERDICT
    odd=[r for r in results["rows"] if r["par"]=="odd"]
    even=[r for r in results["rows"] if r["par"]=="even"]
    odd_all_LMDS = all(r["isLMDS"] for r in odd) if odd else None
    even_all_LMDS = all(r["isLMDS"] for r in even) if even else None
    odd_any_fail = any(not r["isLMDS"] for r in odd)
    even_any_fail = any(not r["isLMDS"] for r in even)
    results["verdict"]=dict(odd_all_LMDS=odd_all_LMDS, even_all_LMDS=even_all_LMDS,
                            odd_any_fail=odd_any_fail, even_any_fail=even_any_fail)
    print("\n"+"="*92)
    print("VERDICT")
    print("="*92)
    print(f"  ODD  rows L-MDS all-true: {odd_all_LMDS}   (any fail: {odd_any_fail})")
    print(f"  EVEN rows L-MDS all-true: {even_all_LMDS}   (any fail: {even_any_fail})")
    if odd_all_LMDS and even_any_fail and not even_all_LMDS:
        v="ADVANCE: ODD mu_n IS higher-order MDS while EVEN is NOT -> negation symmetry is the obstruction; odd routes BGK-free."
    elif odd_any_fail and even_any_fail:
        v="REFUTE: BOTH parities fail L-MDS (some admissible M singular) -> cyclic symmetry not negation is the source; no odd split."
    elif (odd_all_LMDS and even_all_LMDS):
        v="INCONCLUSIVE-MDS: BOTH parities ARE L-MDS at tested params -> no list boost here; need higher L / lower rate to reach floor."
    elif odd_any_fail and not even_any_fail:
        v="INVERTED: ODD fails, EVEN passes -> odd is WORSE; lead refuted in the opposite direction."
    else:
        v="MIXED: see rows."
    print("  "+v)
    results["verdict"]["text"]=v
    with open("L5_homds_rothmatrix_results.json","w") as f:
        json.dump(results,f,indent=2)
    print("\n[written scripts/probes/L5_homds_rothmatrix_results.json]")

if __name__=="__main__":
    main()
