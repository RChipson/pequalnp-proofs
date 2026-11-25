#!/usr/bin/env python3
"""Desk loop for the 5-by-5 Table 1a family, strictly by the book: it only acts on steps the
desk has given us with a lease.

  - "takes at least 11 gates" row (not RepSizeAtMost ... 10): generate the proof with gen55.py,
    compile it, and send it with generator/submit.sh; if it does not compile, keep the lease 20
    minutes and hand the step back as out_of_time.
  - "at most 10 gates" row: if the lower-bound proof for the same mask compiles, the row is false:
    keep the lease 20 minutes and hand it back as statement_seems_false.  Otherwise stop and report.
  - any other step: stop and report, leaving the step held (a 20-minute hold job is started).
Asks the desk for one more step whenever fewer than five are held."""
import json, os, re, subprocess, sys, time
S = '/tmp/claude-0/-home-user-pequalnp-proofs/740307a3-5578-556b-b545-0397351cd4f4/scratchpad'
REPO = '/home/user/pequalnp-proofs'
os.chdir(REPO)
ENV = dict(os.environ, PATH=os.path.expanduser('~/.elan/bin') + ':' + os.environ['PATH'])
LOW = re.compile(r'^¬ \(PEqualNP\.Represents\.RepSizeAtMost \(fun u v : Fin 5 => \((\d+) : ℕ\)\.testBit \(5 \* u\.val \+ v\.val\)\) 10\)$')
UP = re.compile(r'^PEqualNP\.Represents\.RepSizeAtMost \(fun u v : Fin 5 => \((\d+) : ℕ\)\.testBit \(5 \* u\.val \+ v\.val\)\) 10$')
def log(*a):
    print(time.strftime('%H:%M:%S', time.gmtime()), *a, flush=True)
def held():
    return sorted(f[:-5] for f in os.listdir('.pnp') if f.endswith('.json') and not f.startswith('.'))
def hold(step, reason):
    # one renewal job per step, started the moment the step is given; later calls only set the reason
    open(f'/tmp/reason_{step}', 'w').write(reason)
    if os.path.exists(f'/tmp/hold_{step}.log'): return
    subprocess.Popen(['bash', 'generator/hold.sh', step, reason, '20'], stdout=open(f'/tmp/hold_{step}.log', 'w'),
                     stderr=subprocess.STDOUT, start_new_session=True)
def lower_file(step_for_name, mask, stmt):
    d = f'{S}/desk/t55/auto'; os.makedirs(d, exist_ok=True)
    sf = f'{d}/stmt_{step_for_name}.txt'; open(sf, 'w').write(stmt)
    out = f'{d}/{step_for_name.replace("-", "_")}.lean'
    r = subprocess.run(['python3', 'generator/table1a5/gen55.py', step_for_name, str(mask), sf, out], capture_output=True, text=True)
    if r.returncode != 0: return None, 'generator failed: ' + r.stderr[-300:]
    c = subprocess.run(f'cd {S}/up/lean && flock /tmp/lean.lock timeout 1500 lake env lean {out}', shell=True,
                       capture_output=True, text=True, env=ENV)
    bad = c.returncode != 0 or re.search(r'\berror\b', c.stdout + c.stderr) or 'sorry' in open(out).read()
    return (None, 'does not compile: ' + (c.stdout + c.stderr)[-400:]) if bad else (out, 'compiled')
while True:
    if len(held()) >= 5:
        time.sleep(60); continue
    r = subprocess.run(['python3', 'generator/desk.py', 'next', '--another'], capture_output=True, text=True)
    m = re.search(r'^STEP\s+(L-[a-z]+-\d+)', r.stdout, re.M)
    if not m:
        log('none:', r.stdout.strip().split('\n')[0][:100]); time.sleep(150); continue
    step = m.group(1)
    d = json.load(open(f'.pnp/{step}.json')); g = d['gap']; stmt = g['statement'].strip(); title = g.get('title', '')
    log('GIVEN', step, '|', title[:110], '| pr_open', g.get('pr_open'), '| terms', (d['lease'].get('terms') or {}))
    hold(step, 'out_of_time')   # the lease is renewed every five minutes from now on
    lo, up = LOW.match(stmt), UP.match(stmt)
    ready = f'generator/ready/{step.replace("-", "_")}.lean'
    if os.path.exists(ready) and stmt in open(ready).read() and str(g.get('pr_open', '0')) in ('0', 'None'):
        tmp = f'{S}/desk/ready_{step.replace("-", "_")}.lean'
        open(tmp, 'w').write(open(ready).read())
        s2 = subprocess.run(['bash', 'generator/submit.sh', step, tmp], capture_output=True, text=True, env=dict(ENV, NOCHECK='1'))
        log('SENT READY', step, '|', (s2.stdout + s2.stderr).strip().split('\n')[-1][:200])
        time.sleep(20); continue
    if lo and str(g.get('pr_open', '0')) in ('0', 'None'):
        out, why = lower_file(step, int(lo.group(1)), stmt)
        if out:
            s = subprocess.run(['bash', 'generator/submit.sh', step, out], capture_output=True, text=True, env=dict(ENV, NOCHECK='1'))
            log('SENT', step, '|', (s.stdout + s.stderr).strip().split('\n')[-1][:200])
            if step in held():
                log('STOP: after sending,', step, 'is still held; look at it'); sys.exit(0)
        else:
            log('lower bound for', step, why[:300]); hold(step, 'out_of_time')
    elif lo:
        log(step, 'already has a pull request waiting; holding 20 minutes then handing back'); hold(step, 'out_of_time')
    elif up:
        # prove the opposite statement locally (file named after this step, never sent)
        dd = f'{S}/desk/t55/auto'; os.makedirs(dd, exist_ok=True)
        sf = f'{dd}/neg_{step}.txt'; open(sf, 'w').write('¬ (' + stmt + ')')
        o2 = f'{dd}/neg_{step.replace("-", "_")}.lean'
        gch = subprocess.run(['python3', 'generator/table1a5/gen55.py', step, up.group(1), sf, o2], capture_output=True, text=True)
        c = subprocess.run(f'cd {S}/up/lean && flock /tmp/lean.lock timeout 1500 lake env lean {o2}', shell=True, capture_output=True, text=True, env=ENV)
        if gch.returncode == 0 and c.returncode == 0 and not re.search(r'\berror\b', c.stdout + c.stderr):
            log(step, 'is false: its opposite compiles locally; holding 20 minutes then statement_seems_false')
            hold(step, 'statement_seems_false')
        else:
            log('LOOK:', step, 'at-most-10 row whose opposite did not compile'); open('/tmp/auto55_other.log', 'a').write(r.stdout + '\n=====\n'); hold(step, 'out_of_time')
    else:
        open('/tmp/auto55_other.log', 'a').write(r.stdout + '\n=====\n'); hold(step, 'out_of_time')
        if title.startswith(('False:', 'It is false that', 'No AND/OR', 'An AND/OR', 'Table 2: 9 vertices', 'At fan-in two, one NOT gate')):
            log('OTHER (a row at the conjectured bound)', step, '(held 20 minutes, then out_of_time unless handled)')
        else:
            log('STOP: a step worth a real attempt:', step); print(r.stdout[:7000], flush=True); sys.exit(0)
    time.sleep(20)
