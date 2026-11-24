"""Draw one step from the desk (pass --another to keep others) and print it with the live
count of proof pull requests.  Usage: python3 draw.py [--another]"""
import json, os, re, subprocess, sys
sys.path.insert(0, 'generator')
import pr_index
args = ['tools/pnp.sh', 'next'] + sys.argv[1:]
out = subprocess.run(args, capture_output=True, text=True)
m = re.search(r'^STEP\s+(\S+)', out.stdout, re.M)
if not m:
    print('no step:', (out.stdout + out.stderr)[:300]); sys.exit(0)
gid = m.group(1)
d = json.load(open(f'.pnp/{gid}.json')); g = d['gap']
idx, newest = pr_index.build(7200)
mod = g['file'].split('/')[-1][:-5]
def short(s):
    s = re.sub(r'PEqualNP\.(CircuitLowerBounds|MetaComplexity)\.', '', s)
    s = re.sub(r'\((\d+) : (ℕ|Fin \(\d+ : ℕ\))\)', r'\1', s)
    return re.sub(r'\s+', ' ', s)
print(f"{gid} w={g['weight']} len={len(g['statement'])} live proofs={sorted(idx.get(mod, []))} lease until {d['lease']['expires_at']}")
print('TITLE:', g.get('title', '')[:200])
print('SKETCH:', str(g.get('sketch'))[:300])
print('STATEMENT:', short(g['statement'])[:1500])
