# Verify: at r=0, RHS m*(m-1)^(2*(r-1)) uses Nat truncated subtraction (r-1)=0,
# so RHS = m*(m-1)^0 = m. And T0 = 1 <= m. So the ceiling holds unconditionally for r>=0.
for m in [2, 3, 5, 7, 11]:
    r = 0
    rminus1 = max(r - 1, 0)  # Nat truncated subtraction
    rhs = m * (m - 1) ** (2 * rminus1)
    T0 = 1
    assert rhs == m, (m, rhs)
    assert T0 <= rhs, (m, T0, rhs)
    print(f"m={m}: r=0 RHS = m*(m-1)^(2*0) = {rhs} = m, T0=1 <= {rhs} OK")
print("PASS: unconditional ceiling T r <= m*(m-1)^(2(r-1)) holds at r=0 via Nat truncated sub.")
