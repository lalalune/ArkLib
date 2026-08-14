"""
Attack the wraparound / single-depth Wick input from every angle using the NEW machinery:
(A) ARCSINE-IID: the fleet found E_r(mu_n)=E[(Sum_{k=1}^{n/2} Y_k)^{2r}], Y iid arcsine. So eta_b is a sum
    of n/2 'antipodal phase' contributions. Is eta_b ACTUALLY distributed like iid-arcsine-sum? Where does
    the wraparound (char-p) deviate from iid? Test the moment match + the phase independence.
(B) INJECTION: WrapInjectsIntoSlack = (wrap solutions) inject into matchings x slack. Count wrap solutions
    directly and test |Wrap| <= (2r-1)!!*slack at the prize prime.
(C) the iid-arcsine sup-norm: if phases iid, M = max_b |eta_b| ~ sqrt(2*Var*log m), Var=n. Test M vs this.
"""
import cmath, math
from collections import Counter
def isprime(m):
    i=2
    while i*i<=m:
        if m%i==0: return False
        i+=1
    return m>1
def subgroup(p,n):
    e=(p-1)//n
    for c in range(2,p):
        h=pow(c,e,p)
        if pow(h,n,p)==1 and len({pow(h,i,p) for i in range(n)})==n: return [pow(h,i,p) for i in range(n)]
def periods(p,n):
    S=subgroup(p,n); g=2
    while pow(g,(p-1)//2,p)==1: g+=1
    m=(p-1)//n
    return [sum(math.cos(2*math.pi*(pow(g,j,p)*x%p)/p) for x in S) for j in range(m)]
def Er(p,n,R):
    c=Counter({0:1}); E={}; S=subgroup(p,n)
    for r in range(1,R+1):
        nc=Counter()
        for v,mm in c.items():
            for x in S: nc[(v+x)%p]+=mm
        c=nc; E[r]=sum(mm*mm for mm in c.values())
    return E
def dfac(k):
    r=1
    for i in range(1,2*k,2): r*=i
    return r

print("(A) ARCSINE-IID: does eta_b ~ sum of n/2 iid arcsine (Y=2cosU, Var=2)? Total Var should be n/2*2=n.")
for n,p in [(16,65537),(32,1048609)]:
    et=periods(p,n)
    var=sum(e*e for e in et)/len(et)  # E[eta^2] (mean~0)
    k4=sum(e**4 for e in et)/len(et)
    # iid-arcsine sum of n/2: Var=n, kurtosis: E[S^4]=n/2*E[Y^4]+3(n/2)(n/2-1)E[Y^2]^2; Y arcsine E[Y^2]=2,E[Y^4]=6
    mh=n//2
    iid_var=mh*2
    iid_k4 = mh*6 + 3*mh*(mh-1)*2*2
    print(f"  n={n}: Var(eta)={var:.2f} (iid-arcsine n={iid_var}); E[eta^4]={k4:.1f} (iid={iid_k4}); match={abs(var-iid_var)<0.5}")
print("  => if Var & 4th moment match iid-arcsine, the periods ARE iid-arcsine-distributed at low order.")
print()
print("(B) INJECTION: W_r (wraparound count) vs (2r-1)!!*slack, slack=Wick-E0, at prize prime:")
def E0cf(r,n):
    return {2:3*n**2-3*n,3:15*n**3-45*n**2+40*n,4:105*n**4-630*n**3+1435*n**2-1155*n,
            5:945*n**5-9450*n**4+39375*n**3-77175*n**2+57456*n}[r]
for n,p in [(16,65537)]:
    E=Er(p,n,5)
    for r in range(2,6):
        wick=dfac(r)*n**r; E0=E0cf(r,n); Wr=E[r]-E0; slack=wick-E0
        # injection target: Wr <= (2r-1)!!*slack_per_matching? Actually |Wrap|<=|matchings|*slack means Wr<=dfac(r)*slack_tag
        # but slack here = Wick-E0 (the energy slack). The matching-injection slack_tag = slack/(2r-1)!!? 
        slack_tag = slack/dfac(r)
        print(f"  r={r}: W_r={Wr}, slack=Wick-E0={slack}, W_r/slack={Wr/slack:.4f} (need <1 for prize), slack_tag={slack_tag:.0f}")
print()
print("(C) iid-arcsine sup-norm: M=max|eta_b| vs sqrt(2*n*log m) (iid prediction):")
for n,p in [(16,65537),(32,1048609)]:
    et=periods(p,n); M=max(abs(e) for e in et); m=len(et)
    pred=math.sqrt(2*n*math.log(m))
    print(f"  n={n} p={p}: M={M:.3f}, sqrt(2n log m)={pred:.3f}, M/pred={M/pred:.4f} (iid-arcsine sub-Gaussian => M<=pred)")
print("  => M <= sqrt(2n log m) is the iid-arcsine sub-Gaussian max; the wraparound is the iid-DEVIATION.")
