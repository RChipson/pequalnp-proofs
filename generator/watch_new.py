"""Print steps posted since a given id that have no proof pull request yet (live view).
Usage: python3 watch_new.py <lowest id number to show> [min weight]"""
import json, re, subprocess, sys
sys.path.insert(0, 'generator')
import pr_index
lo = int(sys.argv[1]); minw = int(sys.argv[2]) if len(sys.argv) > 2 else 20
raw = subprocess.run(['curl', '-sSf', '-m', '40', 'https://data.pequalnp.com/data/desk/gaps.json'], capture_output=True, text=True).stdout
gaps = json.loads(raw)
json.dump(gaps, open('/tmp/gaps_now.json', 'w'))
idx, newest = pr_index.build(6900)
old = json.load(open('/tmp/pr_index.json'))
for k, v in idx.items(): old[k] = sorted(set(old.get(k, [])) | set(v))
json.dump(old, open('/tmp/pr_index.json', 'w'))
def short(s):
    s = re.sub(r'PEqualNP\.(CircuitLowerBounds|MetaComplexity)\.', '', s)
    s = re.sub(r'\((\d+) : (ℕ|Fin \(\d+ : ℕ\))\)', r'\1', s)
    s = re.sub(r'\s+', ' ', s)
    s = re.sub(r'\(?x\d* ?0 && x\d* ?1\)? \|\| \(?x\d* ?1 && x\d* ?2\)? \|\| \(?x\d* ?2 && x\d* ?3\)? \|\| \(?x\d* ?3 && x\d* ?4\)?.*?x\d* ?8 && x\d* ?5\)?', 'F9', s)
    return s
print('list updated', gaps['updated_at'], '| newest PR', newest)
for r in sorted(gaps['gaps'], key=lambda r: int(r['id'].split('-')[-1])):
    n = int(r['id'].split('-')[-1])
    if n < lo or r['weight'] < minw: continue
    mod = r['file'].split('/')[-1][:-5]
    proofs = old.get(mod, [])
    reds = sorted(x for k, v in old.items() if k.startswith('R_' + mod[2:] + '_') for x in v)
    flag = 'FREE' if not proofs else 'taken'
    print(f"{r['id']} w={r['weight']} {flag} proofs={proofs[:3]} reds={len(reds)} len={len(r['statement'])} | {short(r['statement'])[:260]}")
