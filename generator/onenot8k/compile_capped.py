#!/usr/bin/env python3
"""Compile one Lean file and watch its memory.

  python3 compile_capped.py <file.lean> [limit in GB, default 6.4]
The project's checker allows about 6.5 GB; a file that needs more ends there as FAULT, so it is not worth sending.
The compile is stopped as soon as it passes the limit.  The last line printed is
  PEAK <GB> <seconds> ok | over | failed
Exit 0: compiled with no error inside the limit.  4: over the limit.  1: did not compile."""
import os, re, subprocess, sys, time
LEAN_DIR = os.environ.get('LEAN_DIR', '/tmp/claude-0/-home-user-pequalnp-proofs/740307a3-5578-556b-b545-0397351cd4f4/scratchpad/up/lean')

def tree_rss(pid):
    # resident memory (GB) of the process and everything under it
    kids = {}
    for p in os.listdir('/proc'):
        if not p.isdigit(): continue
        try:
            st = open(f'/proc/{p}/stat').read(); pp = int(st.rsplit(')', 1)[1].split()[1]); kids.setdefault(pp, []).append(int(p))
        except Exception: pass
    todo = [pid]; tot = 0
    while todo:
        q = todo.pop(); todo += kids.get(q, [])
        try:
            m = re.search(r'VmRSS:\s+(\d+) kB', open(f'/proc/{q}/status').read())
            if m: tot += int(m.group(1))
        except Exception: pass
    return tot / 1e6

def run(path, cap=6.4, seconds=1500):
    env = dict(os.environ, PATH=os.path.expanduser('~/.elan/bin') + ':' + os.environ['PATH'])
    log = path + '.compile.log'
    with open(log, 'w') as lf:
        p = subprocess.Popen(['lake', 'env', 'lean', path], cwd=LEAN_DIR, stdout=lf, stderr=subprocess.STDOUT, env=env, start_new_session=True)
        t0 = time.time(); peak = 0.0; over = False
        while p.poll() is None:
            peak = max(peak, tree_rss(p.pid))
            if peak > cap or time.time() - t0 > seconds:
                over = True
                try: os.killpg(p.pid, 9)
                except Exception: pass
                p.wait(); break
            time.sleep(0.3)
    txt = open(log).read()
    bad = p.returncode != 0 or re.search(r'\berror\b', txt)
    return peak, time.time() - t0, ('over' if over else 'failed' if bad else 'ok'), txt

if __name__ == '__main__':
    cap = float(sys.argv[2]) if len(sys.argv) > 2 else 6.4
    peak, secs, verdict, txt = run(sys.argv[1], cap)
    if verdict == 'failed': print(txt[-600:])
    print(f'PEAK {peak:.1f} {secs:.0f} {verdict}')
    sys.exit({'ok': 0, 'over': 4, 'failed': 1}[verdict])
