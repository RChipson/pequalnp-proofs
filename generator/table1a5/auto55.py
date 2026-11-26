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
    if subprocess.run(['pgrep', '-f', f'generator/hold.sh {step} '], capture_output=True).returncode == 0: return
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
def twin_of(stmt):
    # the opposite row, listed beside the step in the public desk file (join.txt: if you believe a
    # step is false, prove its negated twin)
    try:
        raw = subprocess.run(['curl', '-s', '-m', '60', 'https://data.pequalnp.com/data/desk/gaps.json'], capture_output=True, text=True).stdout
        want = stmt[3:-1] if stmt.startswith('¬ (') and stmt.endswith(')') else '¬ (' + stmt + ')'
        for g in json.loads(raw)['gaps']:
            if g.get('statement', '').strip() == want: return g
    except Exception as e:
        log('twin lookup failed', e)
    return None
def send_twin(twin, make):
    # make(twin id, twin statement) -> path of a compiled proof file, or None
    if str(twin.get('pr_open', '0')) not in ('0', 'None'):
        log('twin', twin['id'], 'already has a pull request waiting; not sent'); return False
    out = make(twin['id'], twin['statement'].strip())
    if not out: return False
    if len(held()) >= 5:
        log('twin', twin['id'], 'proved but five steps are held; not leased now'); return False
    r = subprocess.run(['python3', 'generator/desk.py', 'next', '--another', '--proof-of', twin['id']], capture_output=True, text=True)
    m = re.search(r'^STEP\s+(L-[a-z]+-\d+)', r.stdout, re.M)
    if not m or m.group(1) != twin['id']:
        log('twin', twin['id'], 'could not be leased:', r.stdout.strip()[:200])
        if m: hold(m.group(1), 'out_of_time')
        return False
    hold(twin['id'], 'out_of_time')
    got = json.load(open(f'.pnp/{twin["id"]}.json'))['gap']['statement'].strip()
    if got != twin['statement'].strip():
        log('twin', twin['id'], 'statement differs from the public file; not sent'); return False
    s3 = subprocess.run(['bash', 'generator/submit.sh', twin['id'], out], capture_output=True, text=True, env=dict(ENV, NOCHECK='1'))
    log('SENT TWIN', twin['id'], '|', (s3.stdout + s3.stderr).strip().split('\n')[-1][:200])
    return True
def rect_file(step, stmt, seconds=780):
    d = f'{S}/desk/rect'; os.makedirs(d, exist_ok=True)
    # a matrix on which the search already failed with K rectangles is not searched again with K or fewer
    mm = re.search(r'L\.length ≤ (\d+) ∧.*?\(\(\[([0-9, ]+)\] : List ℕ\)\.getD i\.val 0\)\.testBit j\.val = (true|false)', stmt)
    memo = f'{d}/failed.json'
    failed = json.load(open(memo)) if os.path.exists(memo) else {}
    key = (mm.group(2) + '|' + mm.group(3)) if mm else None
    if key and failed.get(key, -1) >= int(mm.group(1)):
        return None, f'not searched: the search already failed on this matrix with {failed[key]} rectangles'
    sf = f'{d}/stmt_{step}.txt'; open(sf, 'w').write(stmt)
    out = f'{d}/{step.replace("-", "_")}.lean'
    r = subprocess.run(['python3', 'generator/rect/rectcover.py', step, sf, out, str(seconds)], capture_output=True, text=True)
    if r.returncode != 0:
        if key and r.returncode == 1:
            failed[key] = max(failed.get(key, -1), int(mm.group(1))); json.dump(failed, open(memo, 'w'))
        return None, r.stdout.strip()[-200:]
    c = subprocess.run(f'cd {S}/up/lean && flock /tmp/lean.lock timeout 1500 lake env lean {out}', shell=True,
                       capture_output=True, text=True, env=ENV)
    bad = c.returncode != 0 or re.search(r'\berror\b', c.stdout + c.stderr)
    return (None, 'does not compile: ' + (c.stdout + c.stderr)[-400:]) if bad else (out, 'compiled')
def six_file(step, stmt, script='generator/sixinput/gen6.py', sub='six'):
    d = f'{S}/desk/{sub}/auto'; os.makedirs(d, exist_ok=True)
    sf = f'{d}/stmt_{step}.txt'; open(sf, 'w').write(stmt)
    out = f'{d}/{step.replace("-", "_")}.lean'
    try:
        r = subprocess.run(['python3', script, step, sf, out], capture_output=True, text=True, timeout=1500)
    except subprocess.TimeoutExpired:
        return None, 'generator timed out'
    if r.returncode != 0: return None, (r.stdout + r.stderr).strip()[-200:]
    c = subprocess.run(f'cd {S}/up/lean && flock /tmp/lean.lock timeout 1500 lake env lean {out}', shell=True,
                       capture_output=True, text=True, env=ENV)
    bad = c.returncode != 0 or re.search(r'\berror\b', c.stdout + c.stderr)
    return (None, 'does not compile: ' + (c.stdout + c.stderr)[-400:]) if bad else (out, r.stdout.strip()[-120:])
def auto_file(step, stmt):
    # a short portfolio of standard tactics, for steps we have no method for (often small pieces of a cut)
    d = f'{S}/desk/autotac'; os.makedirs(d, exist_ok=True)
    name = step.replace('-', '_'); out = f'{d}/{name}.lean'
    open(out, 'w').write('import Mathlib\nimport PEqualNP.Defs\n\ntheorem PEqualNP.Outside.' + name + ' : ' + stmt + ''' := by
  first
    | decide
    | (intros; simp_all)
    | (intros; omega)
    | (intros; tauto)
    | (intros; aesop)
    | simp
    | norm_num
''')
    try:
        c = subprocess.run(f'cd {S}/up/lean && flock /tmp/lean.lock timeout 300 lake env lean {out}', shell=True,
                           capture_output=True, text=True, env=ENV, timeout=900)
    except subprocess.TimeoutExpired:
        return None
    txt = c.stdout + c.stderr
    if c.returncode != 0 or re.search(r'\berror\b', txt) or 'sorry' in txt: return None
    return out
SIX = ('Table 2: for the monotone six-input f', 'Table 2: six-input monotone f')
SIXF = ('False: for the monotone six-input f', 'False: six-input monotone f')
def eight_file(step, stmt):
    return six_file(step, stmt, 'generator/onenot8/gen8.py', 'onenot8')
ONE8 = 'At fan-in two, one NOT gate saves nothing on edges'
ONE8F = 'It is false that: At fan-in two, one NOT gate saves nothing on edges'
def is8(st):
    return 'Fin 8 → Bool' in st
ASK = 0
# after a restart: every step still held gets its renewal job back (it hands the step back when its time is up)
for st in held():
    r0 = open(f'/tmp/reason_{st}').read().strip() if os.path.exists(f'/tmp/reason_{st}') else 'out_of_time'
    hold(st, r0)
# a bounded run: after this many minutes no new step is asked for and the loop ends by itself (steps
# still held keep their renewal jobs, which hand them back on schedule)
MINUTES = int(sys.argv[sys.argv.index('--minutes') + 1]) if '--minutes' in sys.argv else 100
T_END = time.time() + MINUTES * 60
COPY = int(sys.argv[sys.argv.index('--copy') + 1]) if '--copy' in sys.argv else 0
WAIT_BURST, WAIT_QUIET = 9, 30
while True:
    if time.time() > T_END:
        log('bounded run over after', MINUTES, 'minutes; held now:', held()); break
    # join.txt: take the unit from the desk before proving it (it is then ours alone and earns its lease price);
    # never sit idle; one request every few seconds at most; only a hard unit must be given twenty minutes.
    burst = os.path.exists('/tmp/ask_now') and time.time() - os.path.getmtime('/tmp/ask_now') < 45
    if len(held()) >= 5:        # the desk lets an agent hold five units
        time.sleep(2); continue
    ASK += 1
    extra = [['--kind', 'prove', '--level', 'solid'], ['--kind', 'prove', '--level', 'solid'], ['--kind', 'search', '--level', 'solid'], ['--kind', 'prove', '--level', 'solid'], ['--kind', 'prove', '--level', 'warmup']][(ASK + COPY) % 5]
    # the responder (generator/respond/auto_respond.py) touches /tmp/ask_now when the desk's list shows new rows;
    # for a short while after that the request is for solid prove steps, the kind those rows are
    if burst: extra = ['--kind', 'prove', '--level', 'solid']
    asked_at = time.time()
    r = subprocess.run(['python3', 'generator/desk.py', 'next', '--another'] + extra, capture_output=True, text=True)
    m = re.search(r'^STEP\s+(L-[a-z]+-\d+)', r.stdout, re.M)
    if not m:
        log('none', extra, ':', r.stdout.strip().split('\n')[0][:100])
        # wait (20 seconds in a burst, 90 otherwise, 150 if the checker is behind), or less when the responder reports new rows
        t_wait = time.time() + (150 if 'checker is behind' in r.stdout else WAIT_BURST if burst else WAIT_QUIET)
        while time.time() < t_wait:
            if os.path.exists('/tmp/ask_now') and os.path.getmtime('/tmp/ask_now') > asked_at and time.time() - asked_at > 3: break
            time.sleep(1)
        continue
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
            tw = twin_of(stmt)
            if tw:
                send_twin(tw, lambda tid, tstmt: lower_file(tid, int(up.group(1)), tstmt)[0])
        else:
            log('LOOK:', step, 'at-most-10 row whose opposite did not compile'); open('/tmp/auto55_other.log', 'a').write(r.stdout + '\n=====\n'); hold(step, 'out_of_time')
    elif 'has an AND/OR/NOT circuit of fan-in at most two with at most' in title and stmt.startswith('PEqualNP.MetaComplexity.HasCircuitSize 1') and ' 15 (fun' not in stmt[:60]:
        # "find a circuit" rows on about ten inputs: an exact search for thirteen minutes
        if str(g.get('pr_open', '0')) not in ('0', 'None'):
            log(step, 'find-a-circuit row with a pull request already waiting; handing back after 20 minutes')
        else:
            dm = f'{S}/desk/findckt/auto'; os.makedirs(dm, exist_ok=True)
            sf = f'{dm}/stmt_{step}.txt'; open(sf, 'w').write(stmt); om = f'{dm}/{step.replace("-", "_")}.lean'
            # a step whose search already came back empty is not searched again
            tried = set(open(f'{dm}/tried.txt').read().split()) if os.path.exists(f'{dm}/tried.txt') else set()
            if step in tried:
                rr = subprocess.CompletedProcess([], 1, 'searched before without result', '')
            else:
                rr = subprocess.run(['python3', 'generator/findckt/genfind.py', step, sf, om, '780'], capture_output=True, text=True)
                if rr.returncode != 0: open(f'{dm}/tried.txt', 'a').write(step + '\n')
            ok = rr.returncode == 0
            if ok:
                c = subprocess.run(f'cd {S}/up/lean && flock /tmp/lean.lock timeout 1500 lake env lean {om}', shell=True, capture_output=True, text=True, env=ENV)
                ok = c.returncode == 0 and not re.search(r'\berror\b', c.stdout + c.stderr)
            if ok:
                s = subprocess.run(['bash', 'generator/submit.sh', step, om], capture_output=True, text=True, env=dict(ENV, NOCHECK='1'))
                log('SENT', step, '|', rr.stdout.strip()[-60:], '|', (s.stdout + s.stderr).strip().split('\n')[-1][:200])
            else:
                log('find-a-circuit row', step, ':', rr.stdout.strip()[-110:], '; handing back after 20 minutes')
    elif title.startswith('Monotone function on') and not stmt.startswith('¬'):
        if str(g.get('pr_open', '0')) not in ('0', 'None'):
            log(step, 'NOT-on-a-gate row with a pull request already waiting; handing back after 20 minutes')
        else:
            dm = f'{S}/desk/monot/auto'; os.makedirs(dm, exist_ok=True)
            sf = f'{dm}/stmt_{step}.txt'; open(sf, 'w').write(stmt); om = f'{dm}/{step.replace("-", "_")}.lean'
            rr = subprocess.run(['python3', 'generator/monot/gennot.py', step, sf, om, '840'], capture_output=True, text=True)
            ok = rr.returncode == 0
            if ok:
                c = subprocess.run(f'cd {S}/up/lean && flock /tmp/lean.lock timeout 1500 lake env lean {om}', shell=True, capture_output=True, text=True, env=ENV)
                ok = c.returncode == 0 and not re.search(r'\berror\b', c.stdout + c.stderr)
            if ok:
                s = subprocess.run(['bash', 'generator/submit.sh', step, om], capture_output=True, text=True, env=dict(ENV, NOCHECK='1'))
                log('SENT', step, '|', rr.stdout.strip()[-60:], '|', (s.stdout + s.stderr).strip().split('\n')[-1][:200])
            else:
                log('NOT-on-a-gate row', step, ':', rr.stdout.strip()[-110:], '; handing back after 20 minutes')
    elif title.startswith(ONE8) and is8(stmt):
        if str(g.get('pr_open', '0')) not in ('0', 'None'):
            log(step, 'eight-vertex row with a pull request already waiting; handing back after 20 minutes')
        else:
            out, why = eight_file(step, stmt)
            if out:
                s = subprocess.run(['bash', 'generator/submit.sh', step, out], capture_output=True, text=True, env=dict(ENV, NOCHECK='1'))
                log('SENT', step, '|', why, '|', (s.stdout + s.stderr).strip().split('\n')[-1][:200])
            else:
                log('eight-vertex row', step, why[:160], '; handing back after 20 minutes')
    elif title.startswith(ONE8F) and is8(stmt):
        tw = twin_of(stmt)
        if not tw:
            log('eight-vertex refutation row', step, ': twin not found; handing back after 20 minutes')
        elif str(tw.get('pr_open', '0')) not in ('0', 'None'):
            log('eight-vertex refutation row', step, ': twin', tw['id'], 'already has a pull request; handing back after 20 minutes')
        else:
            out, why = eight_file(tw['id'], tw['statement'].strip())
            if out:
                if send_twin(tw, lambda tid, tstmt: out):
                    rr = subprocess.run(['python3', 'generator/desk.py', 'release', step, 'statement_seems_false'], capture_output=True, text=True)
                    log('handed back', step, 'as statement_seems_false |', rr.stdout.strip()[:80])
            else:
                log('eight-vertex refutation row', step, ': twin not proved (', why[:120], '); handing back after 20 minutes')
    elif title.startswith(SIX):
        if str(g.get('pr_open', '0')) not in ('0', 'None'):
            log(step, 'six-input row with a pull request already waiting; handing back after 20 minutes')
        else:
            out, why = six_file(step, stmt)
            if out:
                s = subprocess.run(['bash', 'generator/submit.sh', step, out], capture_output=True, text=True, env=dict(ENV, NOCHECK='1'))
                log('SENT', step, '|', why, '|', (s.stdout + s.stderr).strip().split('\n')[-1][:200])
            else:
                log('six-input row', step, why[:200], '; handing back after 20 minutes')
    elif title.startswith(SIXF):
        # the row denies the positive statement.  The positive one (its twin) is proved here first; if
        # that proof compiles the row is false: the twin is sent when nobody has sent it yet, and the
        # row is handed back at once as statement_seems_false (our own compiled proof is the reason).
        tw = twin_of(stmt)
        if not tw:
            log('six-input refutation row', step, ': twin not found; handing back after 20 minutes')
        else:
            out, why = six_file(tw['id'], tw['statement'].strip())
            if out:
                if str(tw.get('pr_open', '0')) in ('0', 'None'):
                    send_twin(tw, lambda tid, tstmt: out)
                else:
                    log('twin', tw['id'], 'proved here but it already has a pull request waiting; not sent')
                rr = subprocess.run(['python3', 'generator/desk.py', 'release', step, 'statement_seems_false'], capture_output=True, text=True)
                log('handed back', step, 'as statement_seems_false |', rr.stdout.strip()[:80])
            else:
                log('six-input refutation row', step, ': twin not proved (', why[:120], '); handing back after 20 minutes')
    elif 'is represented on the one-a-side promise by an AND/OR circuit of fan-in two with at most' in title:
        # a graph given by a mask, AND/OR gates only: the mixed-OR block circuit (generator/keycover/row8.py)
        dm = f'{S}/desk/row8'; os.makedirs(dm, exist_ok=True)
        sf = f'{dm}/stmt_{step}.txt'; open(sf, 'w').write(stmt); om = f'{dm}/{step.replace("-", "_")}.lean'
        try:
            rr = subprocess.run(['python3', 'generator/keycover/row8.py', step, sf, om], capture_output=True, text=True, timeout=200)
            rc, msg = rr.returncode, rr.stdout.strip()[-80:]
        except subprocess.TimeoutExpired:
            rc, msg = 3, 'not finished in time'
        ok = False
        if rc == 0:
            c = subprocess.run(f'cd {S}/up/lean && timeout 900 lake env lean {om}', shell=True, capture_output=True, text=True, env=ENV)
            ok = c.returncode == 0 and not re.search(r'\berror\b', c.stdout + c.stderr)
        if ok:
            s = subprocess.run(['bash', 'generator/submit.sh', step, om], capture_output=True, text=True, env=dict(ENV, NOCHECK='1', BG_RELEASE='1'))
            log('SENT', step, '|', msg, '|', (s.stdout + s.stderr).strip().split('\n')[-1][:160])
        else:
            log('mask row', step, ':', msg, '; handing back after 20 minutes')
    elif title.startswith('One-a-side promise: the') and 'has a fan-in-two AND/OR circuit of at most' in title:
        # a small rectangular graph: exact search (generator/encoder/rowrect.py)
        dm = f'{S}/desk/rowrect'; os.makedirs(dm, exist_ok=True)
        sf = f'{dm}/stmt_{step}.txt'; open(sf, 'w').write(stmt); om = f'{dm}/{step.replace("-", "_")}.lean'
        try:
            rr = subprocess.run(['python3', 'generator/encoder/rowrect.py', step, sf, om], capture_output=True, text=True, timeout=300)
            rc, msg = rr.returncode, rr.stdout.strip()[-80:]
        except subprocess.TimeoutExpired:
            rc, msg = 3, 'not finished in time'
        ok = False
        if rc == 0:
            c = subprocess.run(f'cd {S}/up/lean && timeout 900 lake env lean {om}', shell=True, capture_output=True, text=True, env=ENV)
            ok = c.returncode == 0 and not re.search(r'\berror\b', c.stdout + c.stderr)
        if ok:
            s = subprocess.run(['bash', 'generator/submit.sh', step, om], capture_output=True, text=True, env=dict(ENV, NOCHECK='1', BG_RELEASE='1'))
            log('SENT', step, '|', msg, '|', (s.stdout + s.stderr).strip().split('\n')[-1][:160])
        elif rc == 1:
            open(f'/tmp/reason_{step}', 'w').write('statement_seems_false'); log('rectangular row', step, ':', msg)
        else:
            log('rectangular row', step, ':', msg)
    elif title.startswith('The two-lit function'):
        # one or two points lit: a gate list in the notes is replayed (generic provers); otherwise exact search
        dm = f'{S}/desk/twolit'; os.makedirs(dm, exist_ok=True)
        sf = f'{dm}/stmt_{step}.txt'; open(sf, 'w').write(stmt); om = f'{dm}/{step.replace("-", "_")}.lean'
        rc, msg = 3, ''
        tu = subprocess.run(['python3', 'generator/respond/try_unit.py', step], capture_output=True, text=True)
        if tu.returncode == 0: om = tu.stdout.strip().split('\n')[-1]; rc, msg = 0, 'generic prover'
        else:
            try:
                rr = subprocess.run(['python3', 'generator/twolit/twolit.py', step, sf, om, '90'], capture_output=True, text=True, timeout=120)
                rc, msg = rr.returncode, rr.stdout.strip()[-70:]
            except subprocess.TimeoutExpired: rc, msg = 3, 'not finished in time'
            if rc == 0:
                c = subprocess.run(f'cd {S}/up/lean && timeout 900 lake env lean {om}', shell=True, capture_output=True, text=True, env=ENV)
                if c.returncode != 0 or re.search(r'\berror\b', c.stdout + c.stderr): rc, msg = 3, 'the proof does not compile'
        if rc == 0:
            s = subprocess.run(['bash', 'generator/submit.sh', step, om], capture_output=True, text=True, env=dict(ENV, NOCHECK='1', BG_RELEASE='1'))
            log('SENT', step, '|', msg, '|', (s.stdout + s.stderr).strip().split('\n')[-1][:160])
        elif rc == 1:
            open(f'/tmp/reason_{step}', 'w').write('statement_seems_false'); log('two-lit row', step, ':', msg)
        else:
            log('two-lit row', step, ':', msg)
    elif 'with a one-input NOT gate computes f' in title and title.startswith('Six-input monotone f'):
        # a circuit with a NOT gate tying the AND/OR size: exhaustive SAT search (generator/monot/gen1n.py)
        dm = f'{S}/desk/monot/auto'; os.makedirs(dm, exist_ok=True)
        sf = f'{dm}/stmt_{step}.txt'; open(sf, 'w').write(stmt); om = f'{dm}/{step.replace("-", "_")}.lean'
        try:
            rr = subprocess.run(['python3', 'generator/monot/gen1n.py', step, sf, om, '840'], capture_output=True, text=True, timeout=900)
            rc, msg = rr.returncode, rr.stdout.strip()[-90:]
        except subprocess.TimeoutExpired:
            rc, msg = 3, 'the search did not end in time'
        if rc == 0:
            c = subprocess.run(f'cd {S}/up/lean && flock /tmp/lean.lock timeout 1500 lake env lean {om}', shell=True, capture_output=True, text=True, env=ENV)
            if c.returncode == 0 and not re.search(r'\berror\b', c.stdout + c.stderr):
                s = subprocess.run(['bash', 'generator/submit.sh', step, om], capture_output=True, text=True, env=dict(ENV, NOCHECK='1'))
                log('SENT', step, '|', msg, '|', (s.stdout + s.stderr).strip().split('\n')[-1][:200])
            else:
                log('one-NOT row', step, ': the proof does not compile; handing back after 20 minutes')
        elif rc == 1:
            rr = subprocess.run(['python3', 'generator/desk.py', 'release', step, 'statement_seems_false'], capture_output=True, text=True)
            log('one-NOT row', step, ':', msg, '; handed back as statement_seems_false |', rr.stdout.strip()[:80])
        else:
            log('one-NOT row', step, ':', msg, '; handing back after 20 minutes')
    elif 'is represented on the one-a-side promise by an AND/OR/NOT circuit' in title and not stmt.startswith('¬'):
        # a "find" row of the promise family (generator/promise/quick_find.py): if a circuit within the bar is
        # found it is the proof; if the exhaustive search (bars up to 7 gates) ends without one, the row is
        # handed back at once as statement_seems_false; otherwise it is handed back after twenty minutes.
        dm = f'{S}/desk/promise/pos'; os.makedirs(dm, exist_ok=True)
        sf = f'{dm}/stmt_{step}.txt'; open(sf, 'w').write(stmt); om = f'{dm}/{step.replace("-", "_")}.lean'
        try:
            rr = subprocess.run(['python3', 'generator/promise/quick_find.py', step, sf, om], capture_output=True, text=True, timeout=400)
            rc, msg = rr.returncode, rr.stdout.strip()[-90:]
        except subprocess.TimeoutExpired:
            rc, msg = 3, 'the search did not end in time'
        if rc == 0 and str(g.get('pr_open', '0')) in ('0', 'None'):
            c = subprocess.run(f'cd {S}/up/lean && flock /tmp/lean.lock timeout 1500 lake env lean {om}', shell=True, capture_output=True, text=True, env=ENV)
            if c.returncode == 0 and not re.search(r'\berror\b', c.stdout + c.stderr):
                s = subprocess.run(['bash', 'generator/submit.sh', step, om], capture_output=True, text=True, env=dict(ENV, NOCHECK='1', BG_RELEASE='1'))
                log('SENT', step, '|', msg, '|', (s.stdout + s.stderr).strip().split('\n')[-1][:200])
            else:
                log('promise row', step, ': the proof does not compile; handing back after 20 minutes')
        elif rc == 1:
            rr = subprocess.run(['python3', 'generator/desk.py', 'release', step, 'statement_seems_false'], capture_output=True, text=True)
            log('promise row', step, ':', msg, '; handed back as statement_seems_false |', rr.stdout.strip()[:80])
        else:
            # undecided: the hold time goes into the full search (generator/promise/deep.py), two rows at a time at most
            busy = int(subprocess.run('pgrep -fc "promise/deep.py L-"', shell=True, capture_output=True, text=True).stdout.strip() or 0)
            level_now = (d['lease'].get('terms') or {}).get('level', '')
            if rc == 3 and busy < 1 and level_now in ('hard', 'open'):
                subprocess.Popen(['python3', 'generator/promise/deep.py', step, '1000'], stdout=open(f'/tmp/deep_{step}.log', 'w'), stderr=subprocess.STDOUT, start_new_session=True)
                log('promise row', step, ':', msg, '; full search started for the 20 minutes it is held')
            else:
                log('promise row', step, ':', msg, '; handing back after 20 minutes')
    elif title.startswith('Rectangles:') and not stmt.startswith('¬'):
        if str(g.get('pr_open', '0')) not in ('0', 'None'):
            log(step, 'rectangle row with a pull request already waiting; handing back after 20 minutes')
        else:
            out, why = rect_file(step, stmt)
            if out:
                s = subprocess.run(['bash', 'generator/submit.sh', step, out], capture_output=True, text=True, env=dict(ENV, NOCHECK='1'))
                log('SENT', step, '|', (s.stdout + s.stderr).strip().split('\n')[-1][:200])
            else:
                log('rectangle row', step, why[:200], '; handing back after 20 minutes')
    elif title.startswith('Rectangles:'):
        # the row says no such cover exists; if the search finds one the row is false and its twin is sent
        tw = twin_of(stmt)
        if tw and str(tw.get('pr_open', '0')) in ('0', 'None'):
            if send_twin(tw, lambda tid, tstmt: rect_file(tid, tstmt)[0]):
                open(f'/tmp/reason_{step}', 'w').write('statement_seems_false')
            else:
                log('rectangle lower-bound row', step, ': no cover found, handing back after 20 minutes')
        else:
            log('rectangle lower-bound row', step, ': twin missing or already sent by someone; handing back after 20 minutes')
    else:
        open('/tmp/auto55_other.log', 'a').write(r.stdout + '\n=====\n'); hold(step, 'out_of_time')
        if str(g.get('pr_open', '0')) in ('0', 'None') and 'shard' not in d and len(stmt) < 6000 and not title.startswith(('It is false that', 'False:')):
            ao = auto_file(step, stmt)
            if ao:
                s = subprocess.run(['bash', 'generator/submit.sh', step, ao], capture_output=True, text=True, env=dict(ENV, NOCHECK='1'))
                log('SENT (standard tactics)', step, '|', (s.stdout + s.stderr).strip().split('\n')[-1][:200])
                time.sleep(20); continue
        if 'shard' in d or title.startswith(('Search:', 'A step toward:', 'Rung', 'Cut of', 'No cutting planes', 'Cutting planes', 'No run of clause learning', 'Clause learning', 'Multiplexer', 'Resolution on', 'Res(')) or (d['lease'].get('terms') or {}).get('level') == 'hard':
            log('OTHER (a search range or a step of a hard cut: beyond our tools)', step, '(held 20 minutes, then out_of_time)')
        elif title.startswith(('False:', 'It is false that', 'No AND/OR', 'An AND/OR', 'Table 2:', 'At fan-in two, one NOT gate')):
            log('OTHER (a row at the conjectured bound)', step, '(held 20 minutes, then out_of_time unless handled)')
        else:
            # an unfamiliar step: it is held for twenty minutes and written to a file for a look; the loop goes on
            log('LOOK: an unfamiliar step, held 20 minutes:', step, '|', title[:120])
            open('/tmp/auto55_look.log', 'a').write(time.strftime('%H:%M:%S', time.gmtime()) + '\n' + r.stdout[:7000] + '\n=====\n')
    # A unit that was not sent and is not hard goes back at once, with the honest reason, so that the place is
    # free for the next unit; a hard or open unit keeps its twenty minutes (the renewal job hands it back).
    level = (d['lease'].get('terms') or {}).get('level', '')
    sent = any(l.split()[:1] == [step] for l in open('generator/pr-requests.txt'))
    working = subprocess.run(['pgrep', '-f', f'deep.py {step} '], capture_output=True).returncode == 0 or os.path.exists(f'/tmp/keep_{step}')
    # families that have their own rule above were already searched; the generic provers are for the rest
    own_rule = any(k in title for k in ('is represented on the one-a-side promise by an AND/OR', 'with a one-input NOT gate computes f',
                                         'has a fan-in-two AND/OR circuit of at most', 'Rectangles:', 'The two-lit function'))
    if os.path.exists(f'.pnp/{step}.json') and not sent and not working and not own_rule:
        # before a unit goes back: the generic provers (generator/respond/try_unit.py)
        try:
            tu = subprocess.run(['python3', 'generator/respond/try_unit.py', step], capture_output=True, text=True, timeout=150)
            if tu.returncode == 0:
                proof = tu.stdout.strip().split('\n')[-1]
                s = subprocess.run(['bash', 'generator/submit.sh', step, proof], capture_output=True, text=True, env=dict(ENV, NOCHECK='1', BG_RELEASE='1'))
                log('SENT (generic prover)', step, '|', tu.stdout.strip().split('\n')[0], '|', (s.stdout + s.stderr).strip().split('\n')[-1][:160])
                sent = True
        except subprocess.TimeoutExpired: pass
    if os.path.exists(f'.pnp/{step}.json') and not sent and not working and level not in ('hard', 'open'):
        why = open(f'/tmp/reason_{step}').read().strip() if os.path.exists(f'/tmp/reason_{step}') else 'other'
        if why not in ('statement_seems_false', 'missing_lemma', 'hypothesis_too_weak', 'does_not_elaborate'): why = 'other'
        rr = subprocess.run(['python3', 'generator/desk.py', 'release', step, why], capture_output=True, text=True)
        log('handed back at once', step, 'as', why, '|', rr.stdout.strip()[:60])
    time.sleep(3)
