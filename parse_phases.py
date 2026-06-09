import re
with open("ArkLib/ToMathlib/SpartanBricks.lean", "r") as f:
    text = f.read()

for line in text.split('\n'):
    if 'OracleReduction' in line and 'def' in line:
        print(line.strip())

