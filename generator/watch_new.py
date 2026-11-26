#!/usr/bin/env python3
"""Watch the public desk file and stop as soon as a batch of new titled steps appears (so that a new
family is noticed within a minute, not at the next half-hourly check).

  python3 generator/watch_new.py [minutes] [how many new titled steps count as a batch]"""
import json, re, subprocess, sys, time
minutes = int(sys.argv[1]) if len(sys.argv) > 1 else 100; need = int(sys.argv[2]) if len(sys.argv) > 2 else 4
def gaps():
    raw = subprocess.run(['curl', '-s', '-m', '60', 'https://data.pequalnp.com/data/desk/gaps.json'], capture_output=True, text=True).stdout
    try: return json.loads(raw)['gaps']
    except Exception: return None
g0 = None
while g0 is None: g0 = gaps(); time.sleep(2)
seen = {g['id'] for g in g0}; t0 = time.time()
print(time.strftime('%H:%M:%S', time.gmtime()), 'watching;', len(seen), 'steps open', flush=True)
while time.time() - t0 < minutes * 60:
    time.sleep(60)
    g = gaps()
    if g is None: continue
    new = [x for x in g if x['id'] not in seen and x.get('title') and not x['title'].startswith('A step toward')]
    for x in g: 
        if not x.get('title') or x['title'].startswith('A step toward'): seen.add(x['id'])
    if len(new) >= need:
        print(time.strftime('%H:%M:%S', time.gmtime()), 'NEW BATCH:', len(new), 'titled steps', flush=True)
        fam = {}
        for x in new: fam.setdefault(re.sub(r'\d+', '#', x['title'])[:110], []).append(x)
        for f, xs in sorted(fam.items(), key=lambda kv: -len(kv[1])):
            print(len(xs), 'no PR', sum(1 for x in xs if str(x.get('pr_open', '0')) in ('0', 'None')), '|', f, '|', xs[0]['id'], flush=True)
            print('   statement:', xs[0].get('statement', '')[:400].replace('\n', ' '))
            print('   sketch:', (xs[0].get('sketch') or '')[:500].replace('\n', ' '))
        sys.exit(0)
print('no new batch in', minutes, 'minutes')
