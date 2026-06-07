import sys

def resolve(filename):
    with open(filename, 'r') as f:
        lines = f.readlines()
    
    out = []
    state = 0
    for line in lines:
        if line.startswith('<<<<<<<'):
            state = 1
        elif line.startswith('======='):
            state = 2
        elif line.startswith('>>>>>>>'):
            state = 0
        else:
            if state == 0 or state == 1 or state == 2:
                # Let's just keep both sides of the conflict!
                # Wait, no, we shouldn't keep both for duplicate lines.
                pass
