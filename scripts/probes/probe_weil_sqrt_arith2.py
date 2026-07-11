#!/usr/bin/env python3
# Does  ((q-1)//2)*d + (q-1) <= (d+2)*S   follow from  S <= q  ALONE (S = M^2)?
# i.e. treat S as a free variable with S <= q. Worst case S as small as possible? No -- RHS grows
# in S, so smallest S = worst. But S=M^2 and M=isqrt q so S can be as small as ~q - 2sqrt(q).
# Test: pick S = M^2 (actual), check D0 <= (d+2)*S. Already TRUE (probe1). But for a clean Lean
# proof I want to know if  D0 <= (d+2)*S  follows from a SIMPLE bound like  q <= S + 2*isqrt(q)
# or just from S>= q - 2M (since (M+1)^2 > q => q <= M^2+2M => q - 2M <= M^2 = S).
# Key clean fact: q <= M^2 + 2M + 1 (since q < (M+1)^2 = M^2+2M+1, as M=isqrt q).
# So q-1 <= M^2 + 2M, and (q-1)//2 <= (M^2+2M)//2.
# Check:  ((q-1)//2)*d + (q-1) <= (d+2)*M^2  using only  q-1 <= M^2+2M  ?
import math
fails=[]
for q in range(3,300001,2):
    M=math.isqrt(q)
    if M==0: continue
    S=M*M
    # the bound we KNOW: q-1 <= S + 2M   (since q <= (M+1)^2 = S+2M+1)
    assert q-1 <= S + 2*M
    for d in range(1,50):
        lhs=((q-1)//2)*d + (q-1)
        # try to bound lhs purely via (q-1)<=S+2M:
        # lhs <= ((S+2M)//2)*d + (S+2M)  -- and want <= (d+2)*S
        ub = ((S+2*M)//2)*d + (S+2*M)
        if lhs>ub:
            fails.append(("lhs>ub",q,d,lhs,ub))
        if ub > (d+2)*S:
            # this is the part that may FAIL -- the slack 2M*d/2 + 2M vs 2*S
            pass
# Now the real question: is  ((S+2M)//2)*d + (S+2M) <= (d+2)*S  ?  i.e.  M*d + 2M <= 2S - ... 
# Let's just check (d+2)*S - lhs >=0 directly is enough (probe1 said yes). Report min slack.
minslack=10**9
arg=None
for q in range(3,300001,2):
    M=math.isqrt(q)
    if M==0: continue
    S=M*M
    for d in range(1,50):
        lhs=((q-1)//2)*d + (q-1)
        slack=(d+2)*S - lhs
        if slack<minslack:
            minslack=slack; arg=(q,d,M,S,lhs)
print("min slack (d+2)*M^2 - D0 over all:", minslack, "at (q,d,M,S,D0)=",arg)
print("lhs>ub fails (sanity):", fails[:4], "count", len(fails))
