#!/usr/bin/env python3
"""Rows "At fan-in two, one NOT gate saves nothing on edges ..." (dense eight-vertex graphs): take free rows of
this family from the desk by name, prove them with gen8k.py and send them.

By the book (https://pequalnp.com/join.txt and its reference tools/pnp.sh):
  - the unit is taken from the desk BEFORE it is proved: `next --unit <id>` asks for that exact unit and gets it
    only if the desk leases it to us (then it is ours alone and earns its lease price); a refusal leases nothing;
  - only rows that are free on the public list and have no pull request waiting are asked for;
  - one request every few seconds at most; a pause or a 429 from the desk is honoured by generator/desk.py;
  - at most five units are held; a row we cannot prove is handed back at once with an honest reason;
  - a file is sent only after it compiled here, through generator/submit.sh (one branch, one commit, one file).

  python3 generator/onenot8k/sweep.py [--minutes 95] [--copy 0]
The owner allowed this script by a permission rule in .claude/settings.json (28 Nov)."""
import fcntl, json, os, random, re, subprocess, sys, time
S = '/tmp/claude-0/-home-user-pequalnp-proofs/740307a3-5578-556b-b545-0397351cd4f4/scratchpad'
REPO = '/home/user/pequalnp-proofs'
os.chdir(REPO)
ENV = dict(os.environ, PATH=os.path.expanduser('~/.elan/bin') + ':' + os.environ['PATH'])
FAMILY = 'At fan-in two, one NOT gate saves nothing on edges'
MINUTES = int(sys.argv[sys.argv.index('--minutes') + 1]) if '--minutes' in sys.argv else 95
COPY = int(sys.argv[sys.argv.index('--copy') + 1]) if '--copy' in sys.argv else 0
T_END = time.time() + MINUTES * 60
TRIED = '/tmp/sweep_tried.txt'          # rows some copy has already asked for (one line per id)
LIST = f'{S}/gaps_sweep.json'

LOGF = ['/tmp/loop_now.log', '/tmp/loop_1.log', '/tmp/loop_2.log'][COPY % 3]     # the files the half-hourly check reads
open(LOGF, 'w').close()
def log(*a):
    line = ' '.join(str(x) for x in (time.strftime('%H:%M:%S', time.gmtime()),) + a)
    print(line, flush=True); open(LOGF, 'a').write(line + '\n')
def held():
    return sorted(f[:-5] for f in os.listdir('.pnp') if f.endswith('.json') and not f.startswith('.'))
def hold(step, reason):
    # the renewal job of the desk loop: a renewal every five minutes, and the step is handed back after 20 minutes
    open(f'/tmp/reason_{step}', 'w').write(reason)
    if subprocess.run(['pgrep', '-f', f'generator/hold.sh {step} '], capture_output=True).returncode == 0: return
    subprocess.Popen(['bash', 'generator/hold.sh', step, reason, '20'], stdout=open(f'/tmp/hold_{step}.log', 'w'),
                     stderr=subprocess.STDOUT, start_new_session=True)
def swap_kb():
    try: return int(re.search(r'SwapTotal:\s+(\d+) kB', open('/proc/meminfo').read()).group(1))
    except Exception: return 0

def free_rows():
    # the public list, fetched at most once a minute by all copies together
    if not os.path.exists(LIST) or time.time() - os.path.getmtime(LIST) > 60:
        subprocess.run(['curl', '-s', '-m', '60', 'https://data.pequalnp.com/data/desk/gaps.json', '-o', LIST + f'.{COPY}'], capture_output=True)
        try: json.load(open(LIST + f'.{COPY}')); os.replace(LIST + f'.{COPY}', LIST)
        except Exception: pass
    try: gaps = json.load(open(LIST))['gaps']
    except Exception: return []
    return [g for g in gaps if g.get('title', '').startswith(FAMILY) and str(g.get('pr_open', '0')) in ('0', 'None')
            and g.get('offerable_now') and not g.get('held_now')]

def claim(rows):
    # one row no copy has asked for yet; the choice is recorded under a lock so that two copies never take the same
    with open(TRIED, 'a+') as f:
        fcntl.flock(f, fcntl.LOCK_EX); f.seek(0); done = set(f.read().split())
        rows = [g for g in rows if g['id'] not in done]
        if not rows: return None
        g = random.choice(rows); f.write(g['id'] + '\n'); f.flush()
        return g

def build(step, stmt):
    d = f'{S}/desk/onenot8k/auto'; os.makedirs(d, exist_ok=True)
    sf = f'{d}/stmt_{step}.txt'; open(sf, 'w').write(stmt)
    out = f'{d}/{step.replace("-", "_")}.lean'
    sw = swap_kb() >= 8000000
    try:
        r = subprocess.run(['python3', 'generator/onenot8k/gen8k.py', step, sf, out], capture_output=True, text=True, timeout=1500)
    except subprocess.TimeoutExpired:
        return None, 'the searches for the data timed out'
    if r.returncode != 0: return None, (r.stdout + r.stderr).strip()[-200:]
    try: gates = json.load(open(out + '.json'))['m']
    except Exception: gates = 0
    if gates >= 15:
        return None, f'a {gates}-gate graph: its file takes too long and too much memory to compile here'
    # one compile at a time; a 15-gate file on one thread, so that only one heavy step is in memory at a time
    pre = 'LEAN_ARGS=-j1 ' if gates >= 15 else ''
    c = subprocess.run(f'{pre}flock /tmp/lean.lock python3 generator/onenot8k/compile_capped.py {out} {"40" if sw else "12.0"}', shell=True,
                       capture_output=True, text=True, env=ENV)
    last = (c.stdout.strip().split('\n') or [''])[-1]
    if c.returncode != 0: return None, f'{gates} gates; does not compile here: ' + c.stdout.strip()[-200:].replace('\n', ' ')
    return out, r.stdout.strip().split('\n')[-1][-80:] + ' | ' + last

log('sweep copy', COPY, 'for', MINUTES, 'minutes; swap', swap_kb() // 1000000, 'GB')
idle = 0
while time.time() < T_END:
    if len(held()) >= 5: time.sleep(5); continue
    g = claim(free_rows())
    if not g:
        idle += 1
        if idle == 1: log('no free row of the family left that we have not asked for; looking again every minute')
        time.sleep(60); continue
    idle = 0
    want = g['id']
    # A quick look before the row is taken (a few seconds): is there a circuit of 14 gates?  If not, the graph
    # needs 15 or more and its file takes over ten minutes and about 20 GB to compile here; such a row is left
    # for others for now (noted in /tmp/sweep_heavy.txt) instead of being taken and handed back.
    pf = f'{S}/desk/onenot8k/probe_{want}.txt'; open(pf, 'w').write((g.get('statement') or '').strip())
    pr = subprocess.run(['python3', 'generator/onenot8k/gen8k.py', '--probe', pf, '8'], capture_output=True, text=True)
    if pr.returncode != 0:
        open('/tmp/sweep_heavy.txt', 'a').write(want + '\n'); log('left alone', want, '| no 14-gate circuit found in the quick look'); continue
    time.sleep(3 + COPY)          # one request every few seconds at most, over all copies
    r = subprocess.run(['python3', 'generator/desk.py', 'next', '--another', '--unit', want], capture_output=True, text=True)
    if r.returncode == 120: log('STOPPED by the project:', r.stdout.strip()[:200]); break
    m = re.search(r'^STEP\s+(L-[a-z]+-\d+)', r.stdout, re.M)
    if not m:
        log('not leased', want, '|', r.stdout.strip().split('\n')[-1][:160])
        if 'PAUSED' in r.stdout: time.sleep(60)
        continue
    step = m.group(1); hold(step, 'out_of_time')
    if step != want:
        log('the desk answered', step, 'instead of', want, '; handed back')
        subprocess.run(['python3', 'generator/desk.py', 'release', step, 'other'], capture_output=True, text=True); continue
    lease = json.load(open(f'.pnp/{step}.json'))
    stmt = lease['gap']['statement'].strip(); pts = (lease['lease'].get('terms') or {}).get('points')
    log('TAKEN', step, '|', pts, 'points |', lease['gap'].get('title', '')[len(FAMILY):][:70])
    if not lease['gap'].get('title', '').startswith(FAMILY) or str(lease['gap'].get('pr_open', '0')) not in ('0', 'None'):
        out, why = None, 'not a free row of the family after all'
    else:
        out, why = build(step, stmt)
    if out and os.path.exists(f'.pnp/{step}.json'):
        s = subprocess.run(['bash', 'generator/submit.sh', step, out], capture_output=True, text=True, env=dict(ENV, NOCHECK='1'))
        log('SENT', step, '|', pts, 'points |', why, '|', (s.stdout + s.stderr).strip().split('\n')[-1][:160])
    else:
        rr = subprocess.run(['python3', 'generator/desk.py', 'release', step, 'other'], capture_output=True, text=True)
        log('handed back', step, '|', str(why)[:200], '|', rr.stdout.strip().split('\n')[-1][:80])
log('bounded run over; held now:', held())
