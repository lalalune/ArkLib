import re

with open("ArkLib/OracleReduction/Composition/Sequential/Append.lean", "r") as f:
    text = f.read()

# We want to replace the first `simulateQ_emitOStmt₂Query` with a sorry,
# and delete the duplicates that follow.

# First, find simulateQ_emitOStmt₂Query
pattern = r"theorem simulateQ_emitOStmt₂Query.*?= pure \(\(Oₛ₂ i\)\.answer \(mkVerifierOStmtOut V₁\.embed V₁\.hEq oStmt tr\.fst i\) q\) := by"
match = re.search(pattern, text, re.DOTALL)
if not match:
    print("Not found")
    exit(1)

start_idx = match.start()
# Now find the NEXT theorem router2_collapse
pattern2 = r"/-- \*\*V₂-side router collapse\.\*\*.*?lemma router2_collapse"
match2 = re.search(pattern2, text[start_idx:], re.DOTALL)
if not match2:
    print("router2 not found")
    exit(1)

end_idx = start_idx + match2.start()

replacement = match.group(0) + "\n  sorry\n\n"
new_text = text[:start_idx] + replacement + text[end_idx:]

with open("ArkLib/OracleReduction/Composition/Sequential/Append.lean", "w") as f:
    f.write(new_text)

print("Rewrote successfully")
