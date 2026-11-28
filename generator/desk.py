"""By-the-book desk client (the steps of https://pequalnp.com/join.txt done by hand, because
this session has no signed-in `gh` for the upstream repository).

  python3 generator/desk.py next [--another] [--hard] [--level warmup|solid|hard|open]
                                 [--kind prove|refute|search|cut|value] [--value] [--proof-of <step>]
                                                         take a step with a lease; print it
                                                         (--proof-of: lease a step we already hold a
                                                         compiled proof of, as join.txt allows)
  python3 generator/desk.py value <step> <k>             a value step: record the k we claim
  python3 generator/desk.py beat                         renew every lease we hold
  python3 generator/desk.py held                         list the leases we hold
  python3 generator/desk.py release <step> <reason>      give a step back with an honest reason
  python3 generator/desk.py submitted <step>             tell the desk the pull request is open

State is kept as the project's own script keeps it: .pnp/<step>.json while held, moved to
.pnp/done/ when released.  One request at a time; nothing is sent but the handle and lease."""
import json, os, re, subprocess, sys, time

DESK = 'https://pequalnp.com/desk'
HANDLE = 'RChipson'
STATE = '.pnp'

def call(method, path):
    cmd = ['curl', '-sS', '-m', '30', '-w', '\n%{http_code}', '-X', method, DESK + path]
    out = subprocess.run(cmd, capture_output=True, text=True).stdout
    body, _, code = out.rpartition('\n')
    return int(code or 0), body

def held():
    return sorted(f[:-5] for f in os.listdir(STATE) if f.endswith('.json') and not f.startswith('.'))

def load(step):
    return json.load(open(f'{STATE}/{step}.json'))

def finish(step):
    os.makedirs(f'{STATE}/done', exist_ok=True)
    os.replace(f'{STATE}/{step}.json', f'{STATE}/done/{step}.json')

def stop_notice():
    # The project's stop notice: a file STOP at the root of its main branch stops all desk work.
    subprocess.run(['git', 'fetch', '-q', 'upstream', 'main'], capture_output=True, timeout=60)
    r = subprocess.run(['git', 'cat-file', '-e', 'upstream/main:STOP'], capture_output=True)
    if r.returncode == 0:
        line = subprocess.run(['git', 'cat-file', 'blob', 'upstream/main:STOP'], capture_output=True, text=True).stdout.split('\n')[0]
        print('STOPPED by a notice on the proofs repository:', re.sub(r"[^A-Za-z0-9 .,:;()'-]", '', line)[:200])
        return True
    return False

def opt(name, pattern):
    if name in sys.argv:
        v = sys.argv[sys.argv.index(name) + 1]
        assert re.fullmatch(pattern, v), f'{name} needs a value like {pattern}'
        return v
    return None

def main():
    os.makedirs(STATE, exist_ok=True)
    cmd = sys.argv[1] if len(sys.argv) > 1 else 'held'
    if cmd in ('next', 'beat'):
        try:
            if stop_notice(): return 120
        except Exception as e:
            print('note: the stop notice could not be read; going on')
    if cmd == 'next':
        q = f'handle={HANDLE}&model=unknown'      # join.txt: always send model=, or unknown
        if '--another' in sys.argv: q += '&another=1'
        if '--hard' in sys.argv: q += '&hard=1'
        for name in ('--level', '--kind'):
            v = opt(name, r'[a-z]{1,10}')
            if v: q += f'&{name[2:]}={v}'
        if '--value' in sys.argv: q += '&value=1'   # value steps are handed out only when asked for
        v = opt('--proof-of', r'L-[a-z]+-[0-9]+')
        if v: q += f'&gap={v}&have=proof'
        # --unit <id>: that exact unit if the desk leases it to us, otherwise nothing (tools/pnp.sh next --unit)
        want = opt('--unit', r'L-[a-z]+-[0-9]+')
        assert not (v and want), 'give --unit or --proof-of, not both'
        if want: q += f'&gap={want}'
        # a pause or a rate limit from the desk is respected by every caller: nothing is asked until it is over
        PAUSE = '/tmp/desk_paused_until'
        if os.path.exists(PAUSE):
            try: until = float(open(PAUSE).read().strip())
            except Exception: until = 0
            if time.time() < until:
                print('PAUSED by the desk until', time.strftime('%Y-%m-%dT%H:%M:%SZ', time.gmtime(until)), '(nothing was asked)'); return 3
        code, body = call('GET', '/next?' + q)
        if code == 429:
            try: wait = float(json.loads(body).get('retry_after_s', 600))
            except Exception: wait = 600
            open(PAUSE, 'w').write(str(time.time() + wait + 20))
            open('/tmp/desk_429.log', 'a').write(time.strftime('%H:%M:%S ', time.gmtime()) + ' '.join(body.split())[:400] + '\n')
            print('PAUSED by the desk: answered 429', body[:300]); return 3
        if code != 200:
            print('desk answered', code, body[:300]); return 1
        d = json.loads(body)
        g = d.get('gap')
        if not g and want:
            # the reference prints the desk's reason and leases nothing; no pause follows from a refusal of one unit
            print('not leased:', ' '.join(str(d.get('note') or d.get('error') or 'no reason given').split())[:300]); return 4
        if not g:
            # join.txt: if no unit is handed out, ask again after the retry_after_s seconds the answer names
            ra = d.get('retry_after_s')
            if isinstance(ra, (int, float)) and ra > 0:
                open(PAUSE, 'w').write(str(time.time() + min(float(ra), 3600)))
            print((d.get('note') or d.get('error') or 'no step right now') + (f' [ask again after {int(ra)} s]' if isinstance(ra, (int, float)) else '')); return 0
        gid = g['id']
        assert re.fullmatch(r'L-[a-z]+-\d+', gid)
        # the lease is recorded first, so that a step is never held without a record of it
        json.dump(d, open(f'{STATE}/{gid}.json', 'w'), indent=1)
        path, module = g.get('file'), g.get('module')
        print('STEP   ', gid, '| weight', g.get('weight'), '|', g.get('title', '')[:160])
        print('FILE   ', path, '| module', module, '| imports', g.get('imports'))
        print('LEASE  ', d['lease']['id'], 'until', d['lease']['expires_at'])
        t = d['lease'].get('terms') or {}
        if t: print('TERMS  ', t.get('level'), t.get('kind'), '|', t.get('points'), 'points', '| racing another holder' if t.get('race') else '')
        if d.get('task'): print('TASK   ', d.get('task'), json.dumps(d.get('direction'))[:600])
        for k in ('shard', 'shards'):
            if k in d: print(k.upper() + ':', d[k])
        if g.get('shard_spec'): print('SHARD_SPEC:', str(g['shard_spec'])[:900])
        if g.get('kind') == 'value':
            print('VALUE STEP: find the least k from 0 to value_max for which the template holds, then: desk.py value', gid, '<k>')
            print('TEMPLATE:', g.get('template')); print('VALUE_MAX:', g.get('value_max'), '|', g.get('value_max_why'))
            print('SIZE:', g.get('size_in_words')); print('FILE_FORM:', g.get('file_form'))
        elif not path or not re.fullmatch(r'lean/PEqualNP/Outside/[A-Za-z0-9_]+\.lean', path):
            print('NOTE: this step has no ordinary file (a value step or malformed); look at', f'{STATE}/{gid}.json')
        for k in ('unlocks', 'context', 'sketch', 'refutation'):
            if g.get(k): print(k.upper() + ':', (g[k] if isinstance(g[k], str) else json.dumps(g[k]))[:900])
        for x in g.get('dead') or []: print('FAILED:', str(x)[:300])
        print('STATEMENT:', g.get('statement'))
        return 0
    if cmd == 'beat':
        for step in held():
            code, body = call('POST', '/beat?lease=' + load(step)['lease']['id'])
            if code == 410:
                print(step, 'STOP 410: settled by someone else or withdrawn; stop work on it'); finish(step)
            elif code == 200:
                print(step, 'lease until', json.loads(body)['lease']['expires_at'])
            else:
                print(step, 'beat answered', code, body[:200])
            time.sleep(3)
        return 0
    if cmd == 'value':
        # a value step: record the k we claim; the file is V_<gap>__k<k>.lean and the statement is
        # the template with k put in for every @@VALUE@@ (as tools/pnp.sh value does)
        step, k = sys.argv[2], sys.argv[3]
        d = load(step); g = d['gap']
        assert g.get('kind') == 'value' and re.fullmatch(r'0|[1-9][0-9]{0,3}', k) and int(k) <= g['value_max']
        name = 'V_%s__k%s' % (step[2:].replace('-', '_'), k)
        g['file'] = f'lean/PEqualNP/Outside/{name}.lean'; g['module'] = 'PEqualNP.Outside.' + name
        g['value'] = int(k); g['statement'] = k.join(g['template'].split('@@VALUE@@'))
        json.dump(d, open(f'{STATE}/{step}.json', 'w'), indent=1)
        print('FILE', g['file'], '| theorem', g['module']); print('STATEMENT:', g['statement'])
        return 0
    if cmd == 'held':
        for step in held():
            d = load(step); print(step, d['gap']['file'], 'lease', d['lease']['id'])
        return 0
    if cmd in ('release', 'submitted'):
        step = sys.argv[2]
        reason = 'submitted' if cmd == 'submitted' else sys.argv[3]
        code, body = call('POST', f"/release?lease={load(step)['lease']['id']}&reason={reason}")
        print(step, 'release', reason, '->', code, body[:200].replace('\n', ' '))
        if code in (200, 410): finish(step)
        return 0
    print(__doc__); return 1

if __name__ == '__main__':
    sys.exit(main())
