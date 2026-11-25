#!/usr/bin/env python3
"""For a held "It is false that: ... one NOT gate ..." step on eight vertices: prove its twin with
gen8.py, and if the proof compiles and nobody has sent the twin yet, lease the twin as "already
have a proof", send it, and hand the held step back as statement_seems_false.
  python3 generator/onenot8/twin_now.py <held step>"""
import json, os, re, subprocess, sys
S = '/tmp/claude-0/-home-user-pequalnp-proofs/740307a3-5578-556b-b545-0397351cd4f4/scratchpad'
os.chdir('/home/user/pequalnp-proofs')
ENV = dict(os.environ, PATH=os.path.expanduser('~/.elan/bin') + ':' + os.environ['PATH'], NOCHECK='1')
held = sys.argv[1]
if not os.path.exists(f'.pnp/{held}.json'): sys.exit(f'{held} is not held')
stmt = json.load(open(f'.pnp/{held}.json'))['gap']['statement'].strip()
raw = subprocess.run(['curl', '-s', '-m', '60', 'https://data.pequalnp.com/data/desk/gaps.json'], capture_output=True, text=True).stdout
tw = next((g for g in json.loads(raw)['gaps'] if g.get('statement', '').strip() == stmt[3:-1]), None)
if not tw: sys.exit('twin not found')
print('twin', tw['id'], 'pr_open', tw.get('pr_open'))
if str(tw.get('pr_open', '0')) not in ('0', 'None'): sys.exit('twin already has a pull request')
d = f'{S}/desk/onenot8/auto'; os.makedirs(d, exist_ok=True)
sf = f'{d}/stmt_{tw["id"]}.txt'; open(sf, 'w').write(tw['statement'].strip())
out = f'{d}/{tw["id"].replace("-", "_")}.lean'
r = subprocess.run(['python3', 'generator/onenot8/gen8.py', tw['id'], sf, out], capture_output=True, text=True)
print(r.stdout.strip()[-160:])
if r.returncode: sys.exit('twin not proved')
c = subprocess.run(f'cd {S}/up/lean && flock /tmp/lean.lock timeout 1500 lake env lean {out}', shell=True, capture_output=True, text=True, env=ENV)
if c.returncode or re.search(r'\berror\b', c.stdout + c.stderr): sys.exit('does not compile: ' + (c.stdout + c.stderr)[-300:])
n = subprocess.run(['python3', 'generator/desk.py', 'next', '--another', '--proof-of', tw['id']], capture_output=True, text=True)
m = re.search(r'^STEP\s+(L-[a-z]+-\d+)', n.stdout, re.M)
if not m or m.group(1) != tw['id']: sys.exit('twin could not be leased: ' + n.stdout[:200])
subprocess.Popen(['bash', 'generator/hold.sh', tw['id'], 'out_of_time', '20'], stdout=open(f'/tmp/hold_{tw["id"]}.log', 'w'), stderr=subprocess.STDOUT, start_new_session=True)
s = subprocess.run(['bash', 'generator/submit.sh', tw['id'], out], capture_output=True, text=True, env=ENV)
print('SENT', tw['id'], (s.stdout + s.stderr).strip().split('\n')[-1][:160])
print(subprocess.run(['python3', 'generator/desk.py', 'release', held, 'statement_seems_false'], capture_output=True, text=True).stdout.strip()[:120])
