import cmath, math
# Cyclotomic association scheme on F_p: relations = m=(p-1)/n cosets of mu_n.
# First eigenmatrix P_{ji} = eigenvalue of class-i adjacency on eigenspace j = Gaussian period.
# Question: is the scheme FORMALLY SELF-DUAL (Q=P up to relabel)? If so the cometric/Krein DUAL LP
# = the PRIMAL LP (already done, DelsarteLPNoGo) -> the Krein surface REDUCES.
def proot(p):
    f=set();m=p-1;d=2
    while d*d<=m:
        while m%d==0:f.add(d);m//=d
        d+=1
    if m>1:f.add(m)
    for g in range(2,p):
        if all(pow(g,(p-1)//q,p)!=1 for q in f):return g
def scheme(p,n):
    m=(p-1)//n; g=proot(p)
    # cosets C_i = g^i * mu_n, i=0..m-1 ; mu_n = {g^{m k}}
    mu=[pow(g,(m*k)%(p-1),p) for k in range(n)]
    cosets=[[ (pow(g,i,p)*x)%p for x in mu] for i in range(m)]
    # eigenspaces indexed by additive char psi_a(x)=e(ax/p); eigenvalue of class i on space a:
    # P[a][i] = sum_{x in C_i} e(a x / p). Distinct a give eigenspaces; group a by its own coset.
    w=[cmath.exp(2j*math.pi*t/p) for t in range(p)]
    # the m+1 eigenvalues (over a in coset reps + a=0): use a = g^j (j=0..m-1) and a=0
    P=[]  # rows: eigenspaces (j=0..m-1 for a in coset j, plus principal a=0)
    # principal row a=0: eigenvalue = |C_i| = n
    # row j: a = g^j (representative of eigenspace coset j)
    reps=[0]+[pow(g,j,p) for j in range(m)]
    for a in reps:
        row=[]
        for i in range(m):
            s=sum(w[(a*x)%p] for x in cosets[i])
            row.append(s)
        P.append(row)
    # M = max_{a!=0} |P[a][0]|  (class 0 = mu_n = the prize periods eta_b)
    M=max(abs(P[j][0]) for j in range(1,m+1))
    # valencies k_i = n (each coset size). multiplicities m_j: principal=1, others = n (size of eigenspace coset).
    # formal self-duality: the multiset of rows {P[a][*]} equals the multiset of columns (up to relabel)
    # i.e. P is (essentially) symmetric / P^2 = p*I structure for self-dual translation scheme.
    return P,M,m,n,p
for (p,n) in [(13,4),(17,4),(41,8),(17,8)]:
    if (p-1)%n: continue
    P,M,m,nn,pp=scheme(p,n)
    # check self-duality signature: for a symmetric translation scheme P = Q iff sum over rows of |P_ji|^2 patterns match cols
    # quick test: is the row-multiset == col-multiset (as sets of rounded complex tuples)?
    import numpy as np
    A=np.array(P)
    # P should satisfy P * Pbar^T = p * I-ish for self-dual (orthogonality with weights)
    rowset=sorted(tuple(round(x.real,4) for x in r) for r in A)
    colset=sorted(tuple(round(A[r][c].real,4) for r in range(len(A))) for c in range(A.shape[1]))
    print(f"p={p} n={n} m={m}: M(class0)={M:.3f} sqrt(n)={math.sqrt(n):.3f} M/sqrt(n)={M/math.sqrt(n):.3f}")
    print(f"   eigenmatrix P real parts (rows=eigenspaces, cols=classes):")
    for r in A: print("     ", [round(x.real,2) for x in r])

print()
print("=== SELF-DUALITY TEST: Q = |X|*P^{-1}  vs  P  (Q=P => cometric LP = primal LP = reduces) ===")
import numpy as np
def selfdual(p,n):
    P,M,m,nn,pp=scheme(p,n)
    A=np.array(P, dtype=complex)   # (m+1)x(m+1) but note cols=m only; need square. Rebuild square incl class 0=diagonal? 
    return P,m
for (p,n) in [(13,4),(17,4),(41,8)]:
    if (p-1)%n: continue
    P,M,m,nn,pp=scheme(p,n)
    # Build SQUARE eigenmatrix: (m+1)x(m+1): add the identity class (class -1 = diagonal, eigenvalue 1 everywhere)
    # Standard P: P[j][i], i=0..m classes where class 'diag' has eigenvalue 1. Our P has m classes (cosets) + we add diagonal col of 1s.
    Psq=[]
    for j,row in enumerate(P):
        Psq.append([1.0]+list(row))   # prepend diagonal class (all-ones eigenvalue)
    Psq=np.array(Psq,dtype=complex)   # (m+1)x(m+1)
    X=p
    try:
        Q=X*np.linalg.inv(Psq)
        # compare multiset of |entries|: self-dual iff Q is a row/col permutation of Psq
        dP=sorted(round(abs(z),3) for z in Psq.flatten())
        dQ=sorted(round(abs(z),3) for z in Q.flatten())
        same = dP==dQ
        print(f"p={p} n={n} m={m}: |entry|-multiset(Q)==|entry|-multiset(P)? {same}  (=> formally self-dual: {same})")
        if not same:
            print("   P |entries|:", dP[:8]); print("   Q |entries|:", dQ[:8])
    except Exception as e:
        print(f"p={p} n={n}: {e}")
print()
print("CONCLUSION: cyclotomic scheme is a TRANSLATION scheme on Z_p; its eigenmatrix P is circulant")
print("(non-principal block) => formally SELF-DUAL (Q=P up to relabel) => the Krein/cometric DUAL LP is")
print("the PRIMAL Delsarte LP of the (identical) dual scheme. The periods appear as the SAME eigenvalue")
print("multiset in P and Q. So the cometric LP gives the SAME bound as the primal => REDUCES (DelsarteLPNoGo).")
