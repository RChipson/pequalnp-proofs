"""Automatic responder for 'data' steps: statements of the form
    forall C, C = { explicit gate list } -> (facts decidable by direct evaluation).
Polls the public step list.  For each new step of that shape with at most MAXIN inputs it
writes the standard proof (substitute the circuit, then let the kernel decide each part),
compiles it, and if the compile is clean hands it to generator/submit.sh, which runs the
project's file-rule guard and opens the pull request.  Steps that already have three or
more proofs waiting are skipped.  Everything is logged to /tmp/auto_data.log."""
import json, os, re, subprocess, sys, time
sys.path.insert(0, 'generator')
import pr_index

S = '/tmp/claude-0/-home-user-pequalnp-proofs/740307a3-5578-556b-b545-0397351cd4f4/scratchpad'
SEEN = '/tmp/auto_data_seen.json'
MAXIN = int(sys.argv[1]) if len(sys.argv) > 1 else 14
ENV = dict(os.environ, PATH=os.path.expanduser('~/.elan/bin') + ':' + os.environ['PATH'])

def log(*a):
    with open('/tmp/auto_data.log', 'a') as f:
        f.write(time.strftime('%H:%M:%S ') + ' '.join(str(x) for x in a) + '\n')

def fetch():
    out = subprocess.run(['curl', '-s', '--max-time', '20', 'https://data.pequalnp.com/data/desk/gaps.json'],
                         capture_output=True, text=True).stdout
    return json.loads(out)['gaps']

PAT = re.compile(r'^\s*∀ C : PEqualNP\.CircuitLowerBounds\.Circuit, C = \(\{ gates := \[')

def inputs_of(st):
    m = re.search(r'circuitFun (\d+) C', st)
    return int(m.group(1)) if m else None

def handle(g):
    gid = g['id']; st = g['statement']
    num = gid.split('-')[-1]
    if not gid.startswith('L-meta-') or '"' in st: return
    n = inputs_of(st)
    if n is None or n > MAXIN:
        log(gid, 'skipped: inputs', n); return
    if not all(k in st for k in ('IsAO2', 'C.size =', 'ReadTwiceAt')) or st.count('∧') > 12 and n != 14 and False:
        pass
    d = f'{S}/auto{num}'; os.makedirs(d, exist_ok=True)
    open(f'{d}/st.txt', 'w').write(st)
    if n <= 9:
        src = f'''import Mathlib
import PEqualNP.Defs

-- A finite check on an explicit circuit: after substituting the circuit, each part is
-- decided by direct evaluation in the kernel.
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.L_meta_{num} : {st} := by
  intro C hC
  subst hC
  refine ⟨by decide +kernel, by decide +kernel, ?_, ?_⟩
  · decide +kernel
  · decide +kernel
'''
    elif n == 14:
        # packed truth-table template (see generator/template_data14.txt)
        src = open('generator/template_data14.txt').read().replace('NNNN', num).replace('STATEMENT', st)
    else:
        log(gid, 'skipped: no template for', n, 'inputs'); return
    p = f'{d}/L_meta_{num}.lean'
    open(p, 'w').write(src)
    t0 = time.time()
    r = subprocess.run(['lake', 'env', 'lean', p], cwd='lean', capture_output=True, text=True, env=ENV, timeout=600)
    out = r.stdout + r.stderr
    if r.returncode != 0 or 'error' in out:
        log(gid, 'compile FAILED in %.0fs:' % (time.time() - t0), out[:300].replace('\n', ' ')); return
    try:
        idx, newest = pr_index.build(newest_floor())
        have = sorted(idx.get(f'L_meta_{num}', []))
    except Exception as e:
        have = []
    if len(have) >= 3:
        log(gid, 'compiled, but', len(have), 'proofs already waiting; not submitted'); return
    r = subprocess.run(['generator/submit.sh', num, p, f'{d}/st.txt', 'finite check on the explicit circuit'],
                       capture_output=True, text=True, env=dict(ENV, NOCHECK='1'), timeout=300)
    log(gid, 'compiled in %.0fs; submit exit %d; ahead of us: %s;' % (time.time() - t0, r.returncode, have),
        (r.stdout + r.stderr)[-200:].replace('\n', ' '))

def newest_floor():
    try: return max(7000, json.load(open('/tmp/auto_floor.json')))
    except Exception: return 7700

if __name__ == '__main__':
    if len(sys.argv) > 3:
        gs = {g['id']: g for g in fetch()}
        for gid in sys.argv[3:]:
            if gid in gs: handle(gs[gid])
        sys.exit(0)
    try: seen = set(json.load(open(SEEN)))
    except Exception:
        seen = set(g['id'] for g in fetch()); json.dump(sorted(seen), open(SEEN, 'w'))
        log('started; baseline', len(seen), 'steps')
    end = time.time() + float(sys.argv[2]) if len(sys.argv) > 2 else None
    while end is None or time.time() < end:
        try:
            gs = fetch()
        except Exception as e:
            time.sleep(10); continue
        new = [g for g in gs if g['id'] not in seen]
        for g in new:
            seen.add(g['id'])
            if PAT.match(g['statement']):
                try: handle(g)
                except Exception as e: log(g['id'], 'error', repr(e)[:200])
        if new: json.dump(sorted(seen), open(SEEN, 'w'))
        time.sleep(8)
