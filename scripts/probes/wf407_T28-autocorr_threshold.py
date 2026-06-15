"""
wf407 / T28-autocorr : PART 3 quantification — how far can a cross bound push the threshold?

Suppose we had a uniform band bound  cross_r <= c * E_r  (c independent of r, c < n(n-1)).
Then E_{r+1} <= (n+c) E_r, so  E_r <= n*(n+c)^{r-1}.  This implies DM ( E_r <= (2r-1)!! n^r )
when   n*(n+c)^{r-1} <= (2r-1)!! n^r,  i.e.   (n+c)^{r-1} <= (2r-1)!! * n^{r-1}.

Take logs:  (r-1) log(n+c) <= log((2r-1)!!) + (r-1) log n.
Using (2r-1)!! ~ sqrt(2)(2r/e)^r, log((2r-1)!!) ~ r log(2r/e).  So threshold r solves
   (r-1) log((n+c)/n) <~ r log(2r/e),  i.e.  log(1+c/n) <~ (r/(r-1)) log(2r/e).
For the threshold to drop to r ~ beta log n we need  log(1+c/n) <~ log(2 beta log n / e),
i.e.  1 + c/n <~ (2 beta log n)/e  =>  c <~ n*(2 beta log n / e - 1).

PRIZE: beta ~ 5 (memory regime pin), n = 2^a.  Then 2 beta log n / e = 10 * (a log 2)/e.
For a=30: 10*20.79/2.718 = 76.5, so c <~ 75.5 n.  That's BARELY below n(n-1)=n^2-n !!  i.e.
even an ENORMOUS allowed c (~75n) only pulls the threshold to beta log n at a=30.  Let's see
exactly the c-vs-threshold curve and where the prize regime sits.
"""
import math

def dfact_log(r):  # log((2r-1)!!)
    s=0.0
    for k in range(1,2*r,2): s+=math.log(k)
    return s

def dfact_log_stirling(r):
    # log((2r-1)!!) = log( (2r)! / (2^r r!) ); use lgamma for big r
    return math.lgamma(2*r+1) - r*math.log(2) - math.lgamma(r+1)

def threshold_r(n, c):
    # crude bound E_r <= n*(n+c)^{r-1}.  DM target (2r-1)!! n^r.
    # 'DM-free' from the smallest r where  log(n)+(r-1)log(n+c) <= dfact_log(r)+ r log n  permanently.
    # Closed-form: define g(r)=dfact_log(r)+r ln n - ln n -(r-1)ln(n+c). g is eventually +inf and
    # the crossover is unique past the dip.  Binary-search the last root.
    ln=math.log(n); lnc=math.log(n+c)
    def g(r):
        return dfact_log_stirling(r) + r*ln - (ln + (r-1)*lnc)
    # find an R with g(R)>0 by doubling
    R=2
    while g(R)<=0 and R< 10**9:
        R*=2
    # binary search smallest r in [1,R] with g(r)>0 AND g stays >0 (monotone past dip for these params)
    lo,hi=1,R
    while lo<hi:
        mid=(lo+hi)//2
        if g(mid)>0: hi=mid
        else: lo=mid+1
    return lo

if __name__=="__main__":
    print("How the DM-free threshold r* depends on the allowed cross constant c (cross_r<=c*E_r):\n")
    for a in [3,4,5,6,10,20,30]:
        n=2**a
        beta=5.0
        target = beta*math.log(n)   # prize-needed depth r ~ beta log n
        print(f"--- n=2^{a}={n}   (prize-needed r~beta*ln n = {target:.1f}, beta=5) ---")
        # trivial c = n(n-1)
        rtriv=threshold_r(n, n*(n-1))
        print(f"   trivial c=n(n-1)={n*(n-1)}:  r* = {rtriv}   (= {rtriv/n:.3f} n)")
        # what c is needed to reach r* <= target?
        # scan c down
        best=None
        clo, chi = 0.0, float(n*(n-1))
        # binary-search smallest c giving r*<=ceil(target)? Actually larger c => larger r*. We want
        # the LARGEST c such that r*<=target (since smaller c is better/stronger).
        tgt=max(1,int(math.ceil(target)))
        lo,hi=0.0,float(n*(n-1))
        for _ in range(60):
            mid=(lo+hi)/2
            r=threshold_r(n,mid)
            if r is not None and r<=tgt: lo=mid
            else: hi=mid
        cneeded=lo
        print(f"   to reach r*<= {tgt} (~beta ln n) you need c <= {cneeded:.2f}  = {cneeded/n:.4f} n  (trivial allows {n-1:.0f} n)")
        # interpret: ratio of needed c to trivial
        print(f"      => needed cross/E <= {cneeded:.2f} vs trivial {n*(n-1)}.  "
              f"Slack factor {n*(n-1)/max(cneeded,1e-9):.2f}x below trivial.\n")
