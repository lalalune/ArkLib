"""
ALTERNATIVE depth grading: PAIRING DEFECT.
For a zero-sum 2r-multiset over mu_n, define pairing defect = 2r - 2*(max # of disjoint
antipodal pairs {zeta^j, zeta^{j+n/2}} you can remove).  A pure Wick/char-0 solution has
defect 0 (fully pairs up).  Genuine additive coincidences (char-p excess) have defect > 0.
The conjecture 'depth-sparse' would predict the excess sits at a BOUNDED defect set.

We compute, for n=16 Fermat p=65537, the char-p zero-sum count graded by pairing defect,
and the char-0 count (defect 0 only, by Lam-Leung).  Excess by defect = char-p[defect] - char0[defect].
char0 lives entirely at defect 0; so excess[0] = char-p[0]-char0[0], excess[d>0]=char-p[d>0].

Max antipodal pairs in a multiset with multiplicities m_j (j=0..n-1): pair class i (i<n/2)
combines m_i and m_{i+n/2}; #pairs from that class = min over a matching... actually each
antipodal pair uses one zeta^i and one zeta^{i+n/2}, so pairs from class i = min(m_i, m_{i+n/2}).
Total max pairs = sum_i min(m_i, m_{i+n/2}).  Defect = 2r - 2*sum_i min(m_i,m_{i+n/2}).
"""
import sys; sys.path.insert(0,'/tmp/tool5')
from fractions import Fraction
from math import factorial
from collections import defaultdict

def mu_residues(n,p,pr):
    h=pow(pr,(p-1)//n,p); out=[]; x=1
    for _ in range(n): out.append(x); x=(x*h)%p
    return out

def charp_by_defect(n,p,pr,twor):
    """DP over antipodal CLASSES i=0..n/2-1. For class i choose (m_a=m_i, m_b=m_{i+n/2}).
    Track (coords_used, sum_mod_p, total_pairs). residue of zeta^i and zeta^{i+n/2}=-zeta^i."""
    res=mu_residues(n,p,pr); half=n//2
    cur={(0,0,0):Fraction(1)}
    for i in range(half):
        ra=res[i]; rb=res[i+half]
        nxt=defaultdict(Fraction)
        for (used,smod,pairs),w in cur.items():
            # choose ma,mb >=0 with used+ma+mb<=twor
            ma=0
            while used+ma<=twor:
                fa=factorial(ma)
                mb=0
                while used+ma+mb<=twor:
                    fb=factorial(mb)
                    nused=used+ma+mb
                    nsmod=(smod+ma*ra+mb*rb)%p
                    npairs=pairs+min(ma,mb)
                    nxt[(nused,nsmod,npairs)] += w*Fraction(1,fa*fb)
                    mb+=1
                ma+=1
        cur=dict(nxt)
    F=factorial(twor)
    prof=defaultdict(int)
    for (used,smod,pairs),w in cur.items():
        if used==twor and smod==0:
            defect=twor-2*pairs
            o=w*F; assert o.denominator==1
            prof[defect]+=int(o)
    return dict(prof)

if __name__=="__main__":
    import sympy, time
    n=16;p=65537;pr=int(sympy.primitive_root(p))
    print(f"n={n} p={p} Fermat: char-p zero-sum count by PAIRING DEFECT (defect 0 = char-0 Wick basin)")
    for twor in [8,10]:
        r=twor//2;t=time.time()
        prof=charp_by_defect(n,p,pr,twor)
        # char-0 sits entirely at defect 0
        from char0_baseline import char0_zero_sum_ordered
        c0tot=sum(char0_zero_sum_ordered(n,twor).values())
        excess={}
        for dft,cnt in sorted(prof.items()):
            ex = cnt-(c0tot if dft==0 else 0)
            excess[dft]=ex
        nz={k:v for k,v in excess.items() if v!=0}
        engaged=sorted([k for k in nz if k>0])
        print(f"  r={r} t={time.time()-t:.1f}s defects_present={sorted(prof.keys())} excess_by_defect={nz}")
        print(f"       => positive-defect levels engaged: {engaged} (count={len(engaged)})")
