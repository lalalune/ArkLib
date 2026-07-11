# Verify the pairwise sign-cancellation for antipodal pairs at ODD grade.
# Claim: for odd jj, a and a+h (h=N/2) contribute to the SAME fold bucket with OPPOSITE sign.
def check(N):
    h=N//2; bad=0
    for jj in range(1,N):
        if jj%2==0: continue  # odd grades only
        for a in range(N):
            ea=(jj*a)%N
            eb=(jj*((a+h)%N))%N
            # bucket = e % h ; sign = +1 if e<h else -1
            ba, bb = ea%h, eb%h
            sa = 1 if ea<h else -1
            sb = 1 if eb<h else -1
            if not (ba==bb and sa==-sb):
                bad+=1
                if bad<5: print(f"  N={N} jj={jj} a={a}: ea={ea}(b{ba},s{sa}) eb={eb}(b{bb},s{sb}) FAIL")
    print(f"N={N}: odd-grade antipodal sign-cancellation failures: {bad}")
check(8); check(16); check(32)
