import os
import re

renames = []
destinations = set()

def should_rename(basename):
    new_name = basename
    prefixes = ['Scratch', 'Tmp', '_keep', 'Test', 'Candidate', 'GrandChallenges', 'GrandChallenge', 'Prize']
    for p in prefixes:
        new_name = re.sub(p, '', new_name)
    new_name = re.sub(r'Leaderboard', 'Metrics', new_name)
    return new_name if new_name != basename else None

for root, _, files in os.walk('ArkLib'):
    for f in files:
        if f.endswith('.lean'):
            old_base = f[:-5]
            new_base = should_rename(old_base)
            if new_base:
                if new_base == '':
                    new_base = 'Misc'
                
                count = 1
                new_path = os.path.join(root, new_base + '.lean')
                while new_path in destinations or os.path.exists(new_path):
                    count += 1
                    new_path = os.path.join(root, new_base + str(count) + '.lean')
                    
                old_path = os.path.join(root, f)
                renames.append((old_path, new_path))
                destinations.add(new_path)

old_new_mods = []
for old_path, new_path in renames:
    exit_code = os.system(f"git mv {old_path} {new_path}")
    if exit_code == 0:
        old_mod = old_path.replace('.lean', '').replace('/', '.')
        new_mod = new_path.replace('.lean', '').replace('/', '.')
        old_new_mods.append((old_mod, new_mod))
    
old_new_mods.sort(key=lambda x: len(x[0]), reverse=True)

for root, _, files in os.walk('.'):
    if '.git' in root or '.lake' in root:
        continue
    for f in files:
        if f.endswith('.lean') or f.endswith('.md'):
            path = os.path.join(root, f)
            with open(path, 'r') as file:
                content = file.read()
                
            new_content = content
            for old_mod, new_mod in old_new_mods:
                new_content = re.sub(r'\b' + re.escape(old_mod) + r'\b', new_mod, new_content)
                
            if new_content != content:
                with open(path, 'w') as file:
                    file.write(new_content)

os.system("./scripts/update-lib.sh")
