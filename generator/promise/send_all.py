#!/usr/bin/env python3
"""Prepare and send the "No AND/OR/NOT circuit ... represents ..." rows that are still open and have no
pull request: write the proof (gennone.py), compile it, ask the desk for the step with --proof-of,
and submit.  One step at a time.

  python3 generator/promise/send_all.py [step id ...]      (no ids: every open row of the family)"""
import json, os, re, subprocess, sys, time
S = '/tmp/claude-0/-home-user-pequalnp-proofs/740307a3-5578-556b-b545-0397351cd4f4/scratchpad'
os.chdir('/home/user/pequalnp-proofs')
ENV = dict(os.environ, PATH=os.path.expanduser('~/.elan/bin') + ':' + os.environ['PATH'], NOCHECK='1')
PRE = '¬ ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤'
def gaps():
    raw = subprocess.run(['curl', '-s', '-m', '60', 'https://data.pequalnp.com/data/desk/gaps.json'], capture_output=True, text=True).stdout
    return {g['id']: g for g in json.loads(raw)['gaps']}
def log(*a): print(time.strftime('%H:%M:%S', time.gmtime()), *a, flush=True)
d = f'{S}/desk/promise/neg'; os.makedirs(d, exist_ok=True)
MEMO = f'{d}/memo.json'
memo = json.load(open(MEMO)) if os.path.exists(MEMO) else {}
G = gaps(); ids = [a for a in sys.argv[1:] if a.startswith('L-')] or sorted(i for i, g in G.items() if g.get('statement', '').startswith(PRE))
now = time.strftime('%Y-%m-%dT%H:%M:%S', time.gmtime())
for step in ids:
    if memo.get(step, {}).get('after', '') > now or memo.get(step, {}).get('sent') or memo.get(step, {}).get('noproof'): continue
    g = G.get(step)
    if not g: log(step, 'no longer open'); continue
    if str(g.get('pr_open', '0')) not in ('0', 'None'): log(step, 'already has a pull request'); continue
    sf = f'{d}/stmt_{step}.txt'; open(sf, 'w').write(g['statement'].strip()); out = f'{d}/{step.replace("-", "_")}.lean'
    class R: stdout = 'proof made earlier'
    r = R()
    if not memo.get(step, {}).get('ok'):
        r = subprocess.run(['python3', 'generator/promise/gennone.py', step, sf, out], capture_output=True, text=True)
        if r.returncode:
            log(step, 'no proof:', r.stdout.strip()[-120:]); memo.setdefault(step, {})['noproof'] = True; json.dump(memo, open(MEMO, 'w')); continue
        c = subprocess.run(f'cd {S}/up/lean && flock /tmp/lean.lock timeout 1500 lake env lean {out}', shell=True, capture_output=True, text=True, env=ENV)
        if c.returncode or re.search(r'\berror\b', c.stdout + c.stderr): log(step, 'does not compile', (c.stdout + c.stderr)[-200:]); continue
        memo.setdefault(step, {})['ok'] = True; json.dump(memo, open(MEMO, 'w'))
    for attempt in range(40):               # wait for one of the five places
        held = [f for f in os.listdir('.pnp') if f.endswith('.json') and not f.startswith('.')]
        if len(held) < 5: break
        time.sleep(30)
    n = subprocess.run(['python3', 'generator/desk.py', 'next', '--another', '--proof-of', step], capture_output=True, text=True)
    m = re.search(r'^STEP\s+(L-[a-z]+-\d+)', n.stdout, re.M)
    if not m or m.group(1) != step:
        log(step, 'could not be leased now:', n.stdout.strip()[:160])
        mm = re.search(r'back after (\d{4}-\d\d-\d\dT\d\d:\d\d:\d\d)', n.stdout)
        if mm: memo.setdefault(step, {})['after'] = mm.group(1); json.dump(memo, open(MEMO, 'w'))
        if m: subprocess.Popen(['bash', 'generator/hold.sh', m.group(1), 'out_of_time', '20'], stdout=open(f'/tmp/hold_{m.group(1)}.log', 'w'), stderr=subprocess.STDOUT, start_new_session=True)
        time.sleep(5); continue
    t = (json.load(open(f'.pnp/{step}.json'))['lease'].get('terms') or {})
    subprocess.Popen(['bash', 'generator/hold.sh', step, 'out_of_time', '20'], stdout=open(f'/tmp/hold_{step}.log', 'w'), stderr=subprocess.STDOUT, start_new_session=True)
    s = subprocess.run(['bash', 'generator/submit.sh', step, out], capture_output=True, text=True, env=ENV)
    memo.setdefault(step, {})['sent'] = True; json.dump(memo, open(MEMO, 'w'))
    log('SENT', step, '| points', t.get('points'), t.get('level'), t.get('kind'), '|', r.stdout.strip()[-40:], '|', (s.stdout + s.stderr).strip().split('\n')[-1][:120])
    time.sleep(4)
log('done')
