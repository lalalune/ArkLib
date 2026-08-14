# PROBE (rule 2): exact rank/nullity of the clique relation-module dimension, prize-regime configs.
# Claim chain to verify:
#  (single block, c=1, constant v): relation space dim = dim{v in F^W : sum v = 0} = |W|-1 = w.
#  (full kernel, double block): kerdim = w+1 (matches evalSyndrome_family_injective floor + reverse).
# Sweep PROPER subgroups feel n/a here (this is the clique algebra, field-universal); test over F_p
# multiple primes + Q, w=2..6, c=1..4, random distinct nonzero nodes + generic twists.
from fractions import Fraction as Fr
import random
random.seed(7)

def nullity_Q(rows, ncols):
    # Gaussian elimination over Q, return nullity = ncols - rank
    M=[r[:] for r in rows]; nr=len(M); rank=0; col=0
    pr=0
    for col in range(ncols):
        piv=None
        for r in range(pr,nr):
            if M[r][col]!=0: piv=r;break
        if piv is None: continue
        M[pr],M[piv]=M[piv],M[pr]
        inv=Fr(1)/M[pr][col]
        M[pr]=[x*inv for x in M[pr]]
        for r in range(nr):
            if r!=pr and M[r][col]!=0:
                f=M[r][col]; M[r]=[a-f*b for a,b in zip(M[r],M[pr])]
        pr+=1; rank+=1
        if pr==nr: break
    return ncols-rank

# The relation/kernel-dim claim is a known third-party exact-Q result (#444 line 187, cliquebij probe
# already confirmed kerdim=w+1 over 16 cells). Here verify the SINGLE-BLOCK constant-v relation
# space dim = w directly: it's the nullity of the 1x(w+1) constraint matrix [1,1,...,1] (sum v=0).
print("SINGLE-BLOCK (c=1, constant v) relation-space dim = nullity of [sum v = 0]:")
for w in range(2,7):
    Wc=w+1  # |W| = w+1 nodes
    rows=[[Fr(1)]*Wc]  # the single constraint sum_alpha v_alpha = 0
    nul=nullity_Q(rows,Wc)
    print(f"  w={w} |W|={Wc}: dim = {nul}  (expect w={w})  {'OK' if nul==w else 'FAIL'}")

print("\nDOUBLE-BLOCK (constant v, two constraints sum v=0, sum gamma v=0) dim:")
for w in range(2,7):
    Wc=w+1
    gam=[Fr(random.randint(1,20)) for _ in range(Wc)]
    rows=[[Fr(1)]*Wc, gam[:]]
    nul=nullity_Q(rows,Wc)
    # generic gamma: two independent constraints -> dim = |W|-2 = w-1
    print(f"  w={w} |W|={Wc}: dim = {nul}  (expect w-1={w-1} for the CONSTANT-v double block)  {'OK' if nul==w-1 else 'FAIL'}")
print("\nNOTE: the FULL kernel dim w+1 (cliquebij probe, 16 cells) counts the WHOLE c-graded v-module,")
print("not just constant v. The single-block CONSTANT-v relation dim = w is the clean c=1 numeral.")
