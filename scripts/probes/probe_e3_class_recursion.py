import sympy as sp
# Is there a provable recursion that yields E_3 from lower data WITHOUT the full partition count?
# The balanced-count over m classes B(2r, m). Consider adding one class at a time (m -> m+1).
# B(6, m) = sum over how many of the 6 positions use the new class. New class must be balanced
# (equal +/-), so it takes 2k positions with k+ and k-, for k=0,1,2,3.
#   k=0: B(6,m)              [new class unused]
#   k=1: C(6,2)*C(2,1)*B(4,m)  choose 2 positions, 1 is +, => C(6,2)=15 positions, C(2,1)=2 sign, rest balanced over old m classes = B(4,m)
#   k=2: C(6,4)*C(4,2)*B(2,m)  = 15 * 6 * B(2,m)
#   k=3: C(6,6)*C(6,3)*B(0,m) = 1*20*1
# This is a CLEAN recursion in m! B(2r, m+1) = sum_{k} C(2r,2k) C(2k,k) B(2r-2k, m).
# Verify:
def B(twor, m, memo={}):
    if m==0:
        return 1 if twor==0 else 0
    if (twor,m) in memo: return memo[(twor,m)]
    from math import comb
    res=0
    for k in range(0, twor//2+1):
        res += comb(twor,2*k)*comb(2*k,k)*B(twor-2*k, m-1)
    memo[(twor,m)]=res
    return res

for r in [1,2,3]:
    for m in [1,2,3,4]:
        n=2*m
        pred={1:n, 2:3*n**2-3*n, 3:15*n**3-45*n**2+40*n}[r]
        print(f"r={r} m={m}: B={B(2*r,m)} pred={pred} match={B(2*r,m)==pred}")
    print()

# So B(2r, .) satisfies B(2r, m) = sum_k C(2r,2k)C(2k,k) B(2r-2k, m-1), B(0,m)=1, B(2r,0)=0 (r>0).
# For fixed small r this is a finite linear recursion in m with polynomial solution.
# r=3: B(6,m) = B(6,m-1) + 15*2*B(4,m-1) + 15*6*B(2,m-1) + 20*B(0,m-1)
#            = B(6,m-1) + 30*B(4,m-1) + 90*B(2,m-1) + 20
# with B(2,m)=2m (= n for n=2m? B(2,m)=C(2,2)C(2,1)B0 summed.. let's just trust)
print("B(2,m) values:", [B(2,m) for m in range(5)])  # should be 2m
print("B(4,m) values:", [B(4,m) for m in range(5)])  
print("B(6,m) values:", [B(6,m) for m in range(5)])
