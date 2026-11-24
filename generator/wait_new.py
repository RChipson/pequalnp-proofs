"""Block until a newly posted step appears (weight at least MINW), then print it in full.
State: /tmp/seen_ids.json.  Usage: python3 wait_new.py [max seconds] [min weight]"""
import json, os, re, subprocess, sys, time
sys.path.insert(0, 'generator')
import pr_index
MAXS = int(sys.argv[1]) if len(sys.argv) > 1 else 540
MINW = int(sys.argv[2]) if len(sys.argv) > 2 else 60
def fetch():
    raw = subprocess.run(['curl', '-sSf', '-m', '40', 'https://data.pequalnp.com/data/desk/gaps.json'], capture_output=True, text=True).stdout
    return json.loads(raw)
def short(s):
    s = re.sub(r'PEqualNP\.(CircuitLowerBounds|MetaComplexity)\.', '', s)
    s = re.sub(r'\((\d+) : (ℕ|Fin \(\d+ : ℕ\))\)', r'\1', s)
    return re.sub(r'\s+', ' ', s)
seen_file = '/tmp/seen_ids.json'
gaps = fetch()
if not os.path.exists(seen_file):
    json.dump([r['id'] for r in gaps['gaps']], open(seen_file, 'w'))
    print('initialised with', len(gaps['gaps']), 'steps'); sys.exit(0)
seen = set(json.load(open(seen_file)))
t0 = time.time()
while True:
    new = [r for r in gaps['gaps'] if r['id'] not in seen]
    if new:
        json.dump(sorted(seen | {r['id'] for r in gaps['gaps']}), open(seen_file, 'w'))
        json.dump(gaps, open('/tmp/gaps_now.json', 'w'))
        idx, newest = pr_index.build(7100)
        show = [r for r in new if r['weight'] >= MINW]
        print('list updated', gaps['updated_at'], '| new steps', len(new), '| shown', len(show), '| newest PR', newest)
        for r in sorted(show, key=lambda r: len(r['statement'])):
            mod = r['file'].split('/')[-1][:-5]
            print(f"--- {r['id']} w={r['weight']} len={len(r['statement'])} proofs={sorted(idx.get(mod, []))}\n    {short(r['statement'])[:1300]}")
        if show: sys.exit(0)
        seen |= {r['id'] for r in gaps['gaps']}
    if time.time() - t0 > MAXS:
        print('no new step in', MAXS, 'seconds'); sys.exit(0)
    time.sleep(15)
    try: gaps = fetch()
    except Exception as e: print('fetch failed', e)
