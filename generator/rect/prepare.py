#!/usr/bin/env python3
"""Prepare a rectangle-cover proof ahead of time (join.txt: "reading ahead and preparing is welcome")
and, when a cover is found and compiles, ask the desk for the step with --proof-of and send it.

  python3 generator/rect/prepare.py <step id> <seconds> [<step id> <seconds> ...]"""
import json, os, re, subprocess, sys
S = '/tmp/claude-0/-home-user-pequalnp-proofs/740307a3-5578-556b-b545-0397351cd4f4/scratchpad'
os.chdir('/home/user/pequalnp-proofs')
ENV = dict(os.environ, PATH=os.path.expanduser('~/.elan/bin') + ':' + os.environ['PATH'], NOCHECK='1')
def gaps():
    raw = subprocess.run(['curl', '-s', '-m', '60', 'https://data.pequalnp.com/data/desk/gaps.json'], capture_output=True, text=True).stdout
    return {g['id']: g for g in json.loads(raw)['gaps']}
args = sys.argv[1:]
for step, secs in zip(args[0::2], args[1::2]):
    g = gaps().get(step)
    if not g: print(step, 'is no longer open', flush=True); continue
    if str(g.get('pr_open', '0')) not in ('0', 'None'): print(step, 'already has a pull request', flush=True); continue
    d = f'{S}/desk/rect/prep'; os.makedirs(d, exist_ok=True)
    sf = f'{d}/stmt_{step}.txt'; open(sf, 'w').write(g['statement'].strip()); out = f'{d}/{step.replace("-", "_")}.lean'
    r = subprocess.run(['python3', 'generator/rect/rectcover.py', step, sf, out, secs], capture_output=True, text=True)
    print(step, r.stdout.strip()[-120:], flush=True)
    if r.returncode: continue
    c = subprocess.run(f'cd {S}/up/lean && flock /tmp/lean.lock timeout 1500 lake env lean {out}', shell=True, capture_output=True, text=True, env=ENV)
    if c.returncode or re.search(r'\berror\b', c.stdout + c.stderr): print(step, 'does not compile', (c.stdout + c.stderr)[-200:], flush=True); continue
    g = gaps().get(step)
    if not g or str(g.get('pr_open', '0')) not in ('0', 'None'): print(step, 'was taken meanwhile; proof kept at', out, flush=True); continue
    n = subprocess.run(['python3', 'generator/desk.py', 'next', '--another', '--proof-of', step], capture_output=True, text=True)
    m = re.search(r'^STEP\s+(L-[a-z]+-\d+)', n.stdout, re.M)
    if not m or m.group(1) != step: print(step, 'could not be leased now:', n.stdout.strip()[:200], '| proof kept at', out, flush=True); continue
    subprocess.Popen(['bash', 'generator/hold.sh', step, 'out_of_time', '20'], stdout=open(f'/tmp/hold_{step}.log', 'w'), stderr=subprocess.STDOUT, start_new_session=True)
    s = subprocess.run(['bash', 'generator/submit.sh', step, out], capture_output=True, text=True, env=ENV)
    print('SENT', step, (s.stdout + s.stderr).strip().split('\n')[-1][:160], flush=True)
