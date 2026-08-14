# Probe companion to O232: the sqrt extraction + the M>=2 vacuity threshold of the
# general-pairwise pencil headline r(r-1) <= C(r,2)*M + (n-1).
#  - M=0: r(r-1) <= n-1  =>  (r-1)^2 < n      (Stepanov sqrt(N), the disjoint extreme)
#  - M=1: r(r-1) <= r(r-1)/2 + (n-1) => r(r-1) <= 2(n-1) => (r-1)^2 < 2n  (autocorr-route sqrt)
#  - M>=2: C(r,2)*M = r(r-1)M/2 >= r(r-1), so the headline is VACUOUS (RHS >= LHS always),
#          i.e. it gives NO bound on r -> the Johnson collapse point. This is the machine-checkable
#          threshold separating "the pairwise double-count still bounds r" (M<=1) from "it is empty".
# Confirm the arithmetic facts hold for all small (r,M,n).
import math
viol=0; cases=0
for r in range(1,60):
    for M in range(0,6):
        Crr2 = r*(r-1)//2
        for n in range(1,200):
            # headline holds as a hypothesis test only when satisfiable; here we verify the
            # IMPLIED extractions are arithmetically sound GIVEN the headline.
            # (1) M=0 extraction:  r(r-1) <= n-1  => (r-1)^2 < n
            if M==0 and r*(r-1) <= n-1:
                if not ((r-1)*(r-1) < n): viol+=1; print("M0 fail",r,n)
            # (2) M=1 extraction:  r(r-1) <= Crr2*1 + (n-1) => (r-1)^2 < 2n
            if M==1 and r*(r-1) <= Crr2 + (n-1):
                if not ((r-1)*(r-1) < 2*n): viol+=1; print("M1 fail",r,n)
            cases+=1
        # (3) M>=2 vacuity: C(r,2)*M >= r(r-1) for all r when M>=2
        if M>=2:
            if not (Crr2*M >= r*(r-1)): viol+=1; print("vacuity fail",r,M)
print("cases=%d violations=%d" % (cases,viol))
