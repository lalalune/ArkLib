import re
with open("ArkLib/ToMathlib/SpartanBricks.lean", "r") as f:
    text = f.read()

# find composedPIOPResidual
print("Found composedPIOPResidual_holds:")
for match in re.finditer(r'theorem composedPIOPResidual_holds.*?sorry', text, re.DOTALL):
    print(match.group(0))

print("\nLooking for 'OracleReduction.append':")
for line in text.split('\n'):
    if 'OracleReduction.append' in line and not line.strip().startswith('--'):
        print(line.strip())

