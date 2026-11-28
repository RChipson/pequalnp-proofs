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
# --family six: rows "Table 2: for the monotone six-input f with table ..." (generator/sixinput/gen6k.py)
FAM = sys.argv[sys.argv.index('--family') + 1] if '--family' in sys.argv else 'onenot'
# --family three: rows "Three ordered outputs a, b, c fit / exceed N gates ..." (generator/threeout); they go
# through the same loop as the six-input rows
THREE = FAM == 'three'
# --family promise / twolit: the search rows "One-a-side promise: the a by b bipartite graph ... at most k gates" and
# "The two-lit function of the graph H ... at most k gates" (the exact searches the desk loop uses for them)
SEARCH = FAM in ('promise', 'twolit')
SIX = FAM in ('six', 'three', 'promise', 'twolit')
FAMILY = 'One-a-side promise: the' if FAM == 'promise' else 'The two-lit function' if FAM == 'twolit' else ('Three ordered outputs', 'On five input bits, three ordered outputs') if THREE else 'Table 2: for the monotone six-input f' if SIX else 'At fan-in two, one NOT gate saves nothing on edges'
MINUTES = int(sys.argv[sys.argv.index('--minutes') + 1]) if '--minutes' in sys.argv else 95
COPY = int(sys.argv[sys.argv.index('--copy') + 1]) if '--copy' in sys.argv else 0
T_END = time.time() + MINUTES * 60
TRIED = f'/tmp/sweep_tried_{FAM}.txt' if SEARCH else '/tmp/sweep_tried_three.txt' if THREE else '/tmp/sweep_tried_six.txt' if SIX else '/tmp/sweep_tried.txt'      # rows already asked for
LIST = f'{S}/gaps_sweep.json'

LOGF = '/tmp/loop_three.log' if THREE else ['/tmp/loop_now.log', '/tmp/loop_1.log', '/tmp/loop_2.log'][COPY % 3]     # the files the checks read
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
        # the sparser graphs first: among them a least circuit of 14 gates or fewer is more common
        if SIX:
            # the newest rows first: a fresh batch still holds 10 to 12-gate functions, the older rows are what
            # every team has passed over
            rows.sort(key=lambda g: (str(g.get('posted_at') or ''), g['id']), reverse=True)
            g = random.choice(rows[:24])
        else:
            ne = lambda g: len(re.findall(r'\d-\d', g.get('title', '')))
            least = min(ne(g) for g in rows)
            g = random.choice([g for g in rows if ne(g) == least])
        f.write(g['id'] + '\n'); f.flush()
        return g

class _R:            # what the compile step reads from a generator's run
    def __init__(self, text): self.stdout = text; self.returncode = 0

def gen_three(step, stmt):
    # the true side is known from a short search; a file is written only for a true row
    d = f'{S}/desk/three'; os.makedirs(d, exist_ok=True)
    sf = f'{d}/stmt_{step}.txt'; open(sf, 'w').write(stmt)
    out = f'{d}/{step.replace("-", "_")}.lean'
    script = 'generator/threeout/genexceed.py' if stmt.startswith('¬') else 'generator/threeout/genfit.py'
    r = subprocess.run(['python3', script, step, sf, out], capture_output=True, text=True, timeout=300)
    if r.returncode != 0: return None, (r.stdout + r.stderr).strip()[-120:].replace('\n', ' ')
    return out, _R('exceed' if stmt.startswith('¬') else 'fit')

def gen_search(step, stmt):
    # an exact search for a circuit within the row's bound; a file is written only when one is found
    d = f'{S}/desk/sweep_{FAM}'; os.makedirs(d, exist_ok=True)
    sf = f'{d}/stmt_{step}.txt'; open(sf, 'w').write(stmt)
    out = f'{d}/{step.replace("-", "_")}.lean'
    cmd = ['python3', 'generator/encoder/rowrect.py', step, sf, out] if FAM == 'promise' else ['python3', 'generator/twolit/twolit.py', step, sf, out, '90']
    try:
        r = subprocess.run(cmd, capture_output=True, text=True, timeout=300 if FAM == 'promise' else 120)
    except subprocess.TimeoutExpired:
        return None, 'the search did not end in time'
    if r.returncode != 0 or not os.path.exists(out): return None, (r.stdout + r.stderr).strip()[-120:].replace('\n', ' ')
    return out, _R(r.stdout.strip()[-70:])

def gen_six(step, stmt):
    if THREE: return gen_three(step, stmt)
    if SEARCH: return gen_search(step, stmt)
    # the data and the file (searches outside Lean only); nothing is compiled here
    d = f'{S}/desk/six/k'; os.makedirs(d, exist_ok=True)
    sf = f'{d}/stmt_{step}.txt'; open(sf, 'w').write(stmt)
    out = f'{d}/{step.replace("-", "_")}.lean'
    try:
        r = subprocess.run(['python3', 'generator/sixinput/gen6k.py', step, sf, out], capture_output=True, text=True, timeout=900)
    except subprocess.TimeoutExpired:
        return None, 'the search for a witness circuit timed out'
    if r.returncode != 0:
        # no circuit of 10 or 11 gates: the table engine (generator/sixinput/gen6t.py) for a 12-gate function
        try:
            r = subprocess.run(['python3', 'generator/sixinput/gen6t.py', step, sf, out, '1', '12', '12'], capture_output=True, text=True, timeout=900)
        except subprocess.TimeoutExpired:
            return None, 'the searches for the tables timed out'
        if r.returncode != 0: return None, (r.stdout + r.stderr).strip()[-200:].replace('\n', ' ')
    return out, r

def build_six(step, stmt, ready=None):
    out, r = ready if ready else gen_six(step, stmt)
    if not out: return None, r
    c = subprocess.run(f'flock /tmp/lean_six_{COPY % 2}.lock python3 generator/onenot8k/compile_capped.py {out} 40 420', shell=True,
                       capture_output=True, text=True, env=ENV)
    last = (c.stdout.strip().split('\n') or [''])[-1]
    if c.returncode != 0: return None, r.stdout.strip()[-70:] + ' | does not compile here: ' + c.stdout.strip()[-200:].replace('\n', ' ')
    return out, r.stdout.strip().split('\n')[-1][-70:] + ' | ' + last

def build(step, stmt):
    if SIX: return build_six(step, stmt)
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
    try:
        sz = json.load(open(out + '.json'))['sizes']; top1 = max(v for k, v in sz.items() if len(k) == 1)
    except Exception: top1 = 0
    if top1 >= gates - 1:
        # a sub-bound only one below the whole graph's: such files went past 12 GB here every time (28 Nov)
        return None, f'{gates} gates with a {top1}-gate part: its file needs more memory than this machine has'
    # one compile at a time; a 15-gate file on one thread, so that only one heavy step is in memory at a time
    pre = 'LEAN_ARGS=-j1 ' if gates >= 15 else ''
    # at most 12 GB and seven minutes: the 14-gate files that were accepted needed 5 to 11 GB and under three
    # minutes; one that needs more would only block the queue (on 28 Nov one ran 23 minutes in swap and two leases
    # ran out behind it)
    c = subprocess.run(f'{pre}flock /tmp/lean.lock python3 generator/onenot8k/compile_capped.py {out} 12.0 420', shell=True,
                       capture_output=True, text=True, env=ENV)
    last = (c.stdout.strip().split('\n') or [''])[-1]
    if c.returncode != 0: return None, f'{gates} gates; does not compile here: ' + c.stdout.strip()[-200:].replace('\n', ' ')
    return out, r.stdout.strip().split('\n')[-1][-80:] + ' | ' + last

PREPARE = '--prepare' in sys.argv; FROM_STOCK = '--from-stock' in sys.argv
STOCK = f'{S}/desk/six/stock'; os.makedirs(STOCK, exist_ok=True)
log('sweep copy', COPY, 'for', MINUTES, 'minutes; swap', swap_kb() // 1000000, 'GB', '| prepare only' if PREPARE else '| from stock' if FROM_STOCK else '')

def stock_one(g):
    # a proof made ahead of time (join.txt: reading ahead and preparing is welcome); nothing is asked of the desk
    step = g['id']; stmt = (g.get('statement') or '').strip()
    out, why = build_six(step, stmt)
    if not out: log('no proof for', step, '|', str(why)[:160]); return
    dst = f'{STOCK}/{step.replace("-", "_")}.lean'; os.replace(out, dst); open(dst + '.stmt', 'w').write(stmt)
    log('STOCKED', step, '|', why)

if PREPARE:
    assert SIX
    TRIED = '/tmp/sweep_stocked_six.txt'
    while time.time() < T_END:
        g = claim(free_rows())
        if not g: time.sleep(60); continue
        stock_one(g)
    log('bounded run over (prepare only)'); sys.exit(0)

def send_proved(step, src, stmt):
    """A row whose proof is compiled and in hand: lease it (next --proof-of, join.txt) and send it at once."""
    free = {g['id']: g for g in free_rows()}
    if step in free and (free[step].get('statement') or '').strip() != stmt:
        log('proved', step, ': the statement on the list differs; left unsent'); return False
    while len(held()) >= 5: time.sleep(5)
    time.sleep(3 + COPY)
    r = subprocess.run(['python3', 'generator/desk.py', 'next', '--another', '--proof-of', step], capture_output=True, text=True)
    if r.returncode == 120: log('STOPPED by the project:', r.stdout.strip()[:200]); sys.exit(0)
    m = re.search(r'^STEP\s+(L-[a-z]+-\d+)', r.stdout, re.M)
    if not m or m.group(1) != step:
        log('not leased', step, '|', r.stdout.strip().split('\n')[-1][:160])
        if m: subprocess.run(['python3', 'generator/desk.py', 'release', m.group(1), 'other'], capture_output=True, text=True)
        if 'PAUSED' in r.stdout: time.sleep(60)
        return False
    hold(step, 'out_of_time')
    lease = json.load(open(f'.pnp/{step}.json')); pts = (lease['lease'].get('terms') or {}).get('points')
    if lease['gap']['statement'].strip() != stmt or str(lease['gap'].get('pr_open', '0')) not in ('0', 'None'):
        log(step, ': the leased statement differs or a pull request is already waiting; handed back')
        subprocess.run(['python3', 'generator/desk.py', 'release', step, 'other'], capture_output=True, text=True); return False
    s = subprocess.run(['bash', 'generator/submit.sh', step, src], capture_output=True, text=True, env=dict(ENV, NOCHECK='1', BG_RELEASE='1'))
    log('SENT', step, '|', pts, 'points |', (s.stdout + s.stderr).strip().split('\n')[-1][:160])
    return True

if FROM_STOCK:
    assert SIX
    names = sorted(f[:-5] for f in os.listdir(STOCK) if f.endswith('.lean'))
    for nm in names:
        if time.time() > T_END: break
        step = nm.replace('_', '-'); src = f'{STOCK}/{nm}.lean'
        if step not in {g['id'] for g in free_rows()}:
            log('stocked', step, 'is no longer free; left unsent'); os.replace(src, src + '.gone'); continue
        if send_proved(step, src, open(src + '.stmt').read().strip()): os.replace(src, src + '.sent')
    log('bounded run over (from stock); held now:', held()); sys.exit(0)

if SIX:
    # A quick look first (under a minute, nothing asked of the desk): is there a circuit of 10 or 11 gates?  Then the
    # row is taken from the desk by name BEFORE the proof is built (next --unit), so that it is ours alone while the
    # file is generated and compiled; a row whose file does not compile here is handed back at once.
    while time.time() < T_END:
        if len(held()) >= 5: time.sleep(5); continue
        g = claim(free_rows())
        if not g:
            log('no free row of the family left that we have not tried; looking again in a minute'); time.sleep(60); continue
        want = g['id']; stmt = (g.get('statement') or '').strip()
        # the data and the file are made now (searches outside Lean, about a minute); the compile, which is the
        # proof being checked, comes after the row is taken
        ready = gen_six(want, stmt)
        if not ready[0]:
            if SEARCH: log('left alone', want, '|', str(ready[1])[:110])
            elif not THREE: open('/tmp/sweep_six_slow.txt', 'a').write(want + '\n'); log('left alone', want, '| no circuit of 10, 11 or 12 gates found in the quick look')
            continue
        # the public list runs minutes behind: GitHub is asked whether a pull request for this row is already waiting
        seen = subprocess.run(['gh', 'api', '-X', 'GET', 'search/issues', '-f', f'q=repo:open-goat/pequalnp-proofs is:pr in:title {want}',
                               '--jq', '[.items[] | select(.title == "' + want + '")] | length'], capture_output=True, text=True).stdout.strip()
        if seen not in ('0', ''):
            log('left alone', want, '| a pull request for it is already waiting'); continue
        time.sleep(2 + COPY)
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
        lease = json.load(open(f'.pnp/{step}.json')); pts = (lease['lease'].get('terms') or {}).get('points')
        log('TAKEN', step, '|', pts, 'points')
        if lease['gap']['statement'].strip() != stmt or str(lease['gap'].get('pr_open', '0')) not in ('0', 'None'):
            out, why = None, 'the leased statement differs from the list, or a pull request is already waiting'
        else:
            out, why = build_six(step, stmt, ready)
        if out and os.path.exists(f'.pnp/{step}.json'):
            s = subprocess.run(['bash', 'generator/submit.sh', step, out], capture_output=True, text=True, env=dict(ENV, NOCHECK='1', BG_RELEASE='1'))
            last = (s.stdout + s.stderr).strip().split('\n')[-1][:160]
            log('SENT' if 'release of' in last else 'NOT SENT', step, '|', pts, 'points |', why, '|', last)
        else:
            rr = subprocess.run(['python3', 'generator/desk.py', 'release', step, 'other'], capture_output=True, text=True)
            log('handed back', step, '|', str(why)[:200], '|', rr.stdout.strip().split('\n')[-1][:80])
    log('bounded run over; held now:', held()); sys.exit(0)

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
    pr = None if SIX else subprocess.run(['python3', 'generator/onenot8k/gen8k.py', '--probe', pf, '8'], capture_output=True, text=True)
    if pr is not None and pr.returncode != 0:
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
    log('TAKEN', step, '|', pts, 'points |', lease['gap'].get('title', '')[len(FAMILY):][:50])
    if not lease['gap'].get('title', '').startswith(FAMILY) or str(lease['gap'].get('pr_open', '0')) not in ('0', 'None'):
        out, why = None, 'not a free row of the family after all'
    else:
        out, why = build(step, stmt)
    if out and os.path.exists(f'.pnp/{step}.json'):
        s = subprocess.run(['bash', 'generator/submit.sh', step, out], capture_output=True, text=True, env=dict(ENV, NOCHECK='1', BG_RELEASE='1'))
        log('SENT', step, '|', pts, 'points |', why, '|', (s.stdout + s.stderr).strip().split('\n')[-1][:160])
    else:
        rr = subprocess.run(['python3', 'generator/desk.py', 'release', step, 'other'], capture_output=True, text=True)
        log('handed back', step, '|', str(why)[:200], '|', rr.stdout.strip().split('\n')[-1][:80])
log('bounded run over; held now:', held())
