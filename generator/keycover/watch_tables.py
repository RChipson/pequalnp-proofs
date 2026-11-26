#!/usr/bin/env python3
"""Watch the desk's list for rows "a fixed n by n graph given by its table: some AND/OR/NOT circuit of
fan-in two with at most k gates is right on the promise", and send a proof as soon as one of them asks
for no fewer gates than the best circuit we hold for its table.

For a table seen for the first time the cover is computed (plant2.py, pick3, sa, cse.paar), which takes
about two minutes for 128 by 128.  Covers are kept per table under <scratch>/desk/big/tables/<hash>/;
a better cover dropped there as best.txt (with its gate count in best.json) is picked up on the next round.

  python3 generator/keycover/watch_tables.py <minutes>
Exits after sending one proof (so that the caller hears of it) or when the minutes are over."""
import hashlib, json, os, re, subprocess, sys, time
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import gencover
S = '/tmp/claude-0/-home-user-pequalnp-proofs/740307a3-5578-556b-b545-0397351cd4f4/scratchpad'
os.chdir('/home/user/pequalnp-proofs')
ENV = dict(os.environ, PATH=os.path.expanduser('~/.elan/bin') + ':' + os.environ['PATH'], NOCHECK='1')
BASE = f'{S}/desk/big/tables'; os.makedirs(BASE, exist_ok=True)
MEMO = f'{BASE}/memo.json'
def log(*a): print(time.strftime('%H:%M:%S', time.gmtime()), *a, flush=True)
def gaps():
    raw = subprocess.run(['curl', '-s', '-m', '60', 'https://data.pequalnp.com/data/desk/gaps.json'], capture_output=True, text=True).stdout
    return {g['id']: g for g in json.loads(raw)['gaps']}
def tools():
    for t in ('pick3', 'sa'):
        if not os.path.exists(f'{BASE}/{t}'):
            subprocess.run(['gcc', '-O2', '-o', f'{BASE}/{t}', f'{HERE}/{t}.c', '-lm'], check=True)
def cover_for(rows, n):
    """directory of the table, with best.txt (cover) and best.json ({"gates": g})"""
    h = hashlib.sha1((str(n) + ':' + ','.join('%x' % r for r in rows)).encode()).hexdigest()[:12]
    d = f'{BASE}/{h}'; os.makedirs(d, exist_ok=True)
    if os.path.exists(f'{d}/best.json'): return d
    if n > 128: return None
    tools()
    json.dump(rows, open(f'{d}/table.json', 'w'))
    log('new table', h, 'side', n, ': computing a cover')
    subprocess.run(['python3', f'{HERE}/plant2.py', f'{d}/table.json', str(n), f'{d}/cand.json'], capture_output=True, timeout=900)
    subprocess.run(['python3', f'{HERE}/topick.py', f'{d}/table.json', str(n), f'{d}/cand.json', f'{d}/t.txt', f'{d}/c.txt'], check=True)
    with open(f'{d}/cover0.txt', 'w') as f: subprocess.run([f'{BASE}/pick3', str(n), f'{d}/t.txt', f'{d}/c.txt'], stdout=f, stderr=subprocess.DEVNULL, check=True)
    best = None
    for seed in range(1, 9):
        subprocess.run([f'{BASE}/sa', str(n), f'{d}/t.txt', f'{d}/cover0.txt', f'{d}/sa{seed}.txt', str(seed), '100', '0.5', '0.12'], capture_output=True, check=True)
        g, o = gencover.best_circuit(n, gencover.load_blocks(f'{d}/sa{seed}.txt'), 4)
        if best is None or len(g) < best[0]: best = (len(g), seed)
    os.replace(f'{d}/sa{best[1]}.txt', f'{d}/best.txt'); json.dump({'gates': best[0]}, open(f'{d}/best.json', 'w'))
    log('table', h, 'best circuit', best[0], 'gates')
    return d
def main():
    end = time.time() + 60 * float(sys.argv[1])
    memo = json.load(open(MEMO)) if os.path.exists(MEMO) else {}
    while time.time() < end:
        try: G = gaps()
        except Exception as e: log('list not read', e); time.sleep(30); continue
        now = time.strftime('%Y-%m-%dT%H:%M:%S', time.gmtime())
        for step, g in G.items():
            if 'given by its table' not in g.get('title', ''): continue
            if str(g.get('pr_open', '0')) not in ('0', 'None'): continue
            if 'STOOD DOWN' in g.get('sketch', '') or 'do not start' in g.get('sketch', ''): continue
            me = memo.setdefault(step, {})
            if me.get('sent') or me.get('after', '') > now: continue
            st = g['statement'].strip()
            try: rows, n, k = gencover.parse_statement(st)
            except Exception: continue
            if not st.startswith('∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤'): continue
            d = cover_for(rows, n)
            if not d: continue
            have = json.load(open(f'{d}/best.json'))['gates']
            if have > k:
                if me.get('short') != have: log(step, 'asks for', k, 'gates; we hold', have); me['short'] = have; json.dump(memo, open(MEMO, 'w'))
                continue
            gates, out = gencover.best_circuit(n, gencover.load_blocks(f'{d}/best.txt'), 12)
            if len(gates) > k: continue
            tree = any('PromiseColTree' in i for i in g.get('imports', []))
            if not tree and not any(i.endswith('PromiseCol') for i in g.get('imports', [])): log(step, 'names neither helper; skipped'); me['after'] = '9'; continue
            outf = f'{d}/{step.replace("-", "_")}.lean'
            gencover.write_lean(step, st, rows, n, gates, out, outf, tree)
            c = subprocess.run(f'cd {S}/up/lean && flock /tmp/lean.lock timeout 1500 lake env lean {outf}', shell=True, capture_output=True, text=True, env=ENV)
            if c.returncode or re.search(r'\berror\b', c.stdout + c.stderr): log(step, 'does not compile', (c.stdout + c.stderr)[-300:]); me['after'] = '9'; continue
            log(step, 'proof ready:', len(gates), 'gates for a bound of', k)
            n_ = subprocess.run(['python3', 'generator/desk.py', 'next', '--another', '--proof-of', step], capture_output=True, text=True)
            m = re.search(r'^STEP\s+(L-[a-z]+-\d+)', n_.stdout, re.M)
            if not m or m.group(1) != step:
                mm = re.search(r'back after (\d{4}-\d\d-\d\dT\d\d:\d\d:\d\d)', n_.stdout)
                me['after'] = mm.group(1) if mm else time.strftime('%Y-%m-%dT%H:%M:%S', time.gmtime(time.time() + 120))
                json.dump(memo, open(MEMO, 'w'))
                log(step, 'not handed to us now:', n_.stdout.strip()[:160]); continue
            subprocess.Popen(['bash', 'generator/hold.sh', step, 'out_of_time', '20'], stdout=open(f'/tmp/hold_{step}.log', 'w'), stderr=subprocess.STDOUT, start_new_session=True)
            s = subprocess.run(['bash', 'generator/submit.sh', step, outf], capture_output=True, text=True, env=ENV)
            me['sent'] = now; json.dump(memo, open(MEMO, 'w'))
            log('SENT', step, (s.stdout + s.stderr).strip().split('\n')[-1][:200])
            return
        json.dump(memo, open(MEMO, 'w'))
        time.sleep(30)
    log('time is up')
main()
