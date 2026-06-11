import os
import re

replacements = {
    'Proposition4_21': 'Proposition421',
    '_mca_research_loop': 'MCAResearchLoop',
    'MCACapacityTrivial_keep': 'MCACapacityTrivial',
    'MCAGSRefutationCore_keep': 'MCAGSRefutationCore',
    'whir113keystone': 'Whir113Keystone'
}

for root, _, files in os.walk('.'):
    if '.git' in root or '.lake' in root:
        continue
    for f in files:
        if f.endswith('.lean') or f.endswith('.md'):
            path = os.path.join(root, f)
            with open(path, 'r') as file:
                content = file.read()
            
            new_content = content
            for old, new in replacements.items():
                new_content = new_content.replace(old, new)
                
            if new_content != content:
                with open(path, 'w') as file:
                    file.write(new_content)
