#!/usr/bin/env python3
"""Proof file for a desk row
   ¬ ∃ C, FanInTwo C ∧ C.size ≤ s ∧ Represents (fun u v : Fin n => (M : ℕ).testBit (n * u.val + v.val)) C
by a SAT solver's certificate replayed with the project's checker (PEqualNP.Library.LRAT):

  gennot_promise.py   the formula  enc2 (n + n) s (Promise.gMask n n M) (Promise.repRows n n)  as DIMACS
  cadical             an LRAT refutation
  genrow.py           the project's own packer (notes/data/lrat-link/genrow.py on the project's main branch,
                      fetched from there), whose output is fitted to the row: the formula is the library
                      formula itself, the last line is PromiseN.repN_lower_mask.

  python3 mkfloor.py <step id> <statement file> <out.lean> [seconds for the solver]
exit 0: file written; 1: the formula is satisfiable or the solver ran out of time; 2: not such a row."""
import os, re, subprocess, sys
HERE = os.path.dirname(os.path.abspath(__file__))
S = '/tmp/claude-0/-home-user-pequalnp-proofs/740307a3-5578-556b-b545-0397351cd4f4/scratchpad'
PAT = re.compile(r'¬ ∃ C : PEqualNP\.CircuitLowerBounds\.Circuit, PEqualNP\.MetaComplexity\.FanInTwo C ∧ C\.size ≤ (\d+) ∧ PEqualNP\.Represents\.Represents \(fun u v : Fin (\d+) => \((\d+) : ℕ\)\.testBit \((\d+) \* u\.val \+ v\.val\)\) C')

def main():
    step, sf, out = sys.argv[1:4]
    secs = sys.argv[4] if len(sys.argv) > 4 else '600'
    stmt = open(sf).read().strip()
    m = PAT.fullmatch(' '.join(stmt.split()))            # the statement is kept as posted; only the match ignores spacing
    if not m or m.group(2) != m.group(4): print('not a row of this family'); return 2
    s, n, M = int(m.group(1)), int(m.group(2)), int(m.group(3))
    work = f'{S}/lrat/work'; os.makedirs(work, exist_ok=True)
    packer = f'{S}/lrat/genrow.py'
    if not os.path.exists(packer):
        src = subprocess.run(['git', '-C', '/home/user/pequalnp-proofs', 'show', 'upstream/main:notes/data/lrat-link/genrow.py'], capture_output=True, text=True, check=True).stdout
        open(packer, 'w').write(src)
    tag = step.replace('-', '_')
    cnf, lrat, raw = f'{work}/{tag}.cnf', f'{work}/{tag}.lrat', f'{work}/{tag}.raw.lean'
    subprocess.run([sys.executable, f'{HERE}/gennot_promise.py', str(n), str(n), str(M), str(s), cnf], capture_output=True, check=True)
    if os.path.exists(lrat): os.unlink(lrat)
    r = subprocess.run(['cadical', '-q', '-t', secs, '--unsat', '--seed=2', '--lrat', '--no-binary', cnf, lrat], capture_output=True, text=True)
    if r.returncode != 20: print('no refutation: cadical exit', r.returncode, '(10 = a circuit exists, 0 = out of time)'); return 1
    ns = f'PEqualNP.Outside.{tag}_aux'
    g = subprocess.run([sys.executable, packer, cnf, lrat, raw, ns, str(2 * n), str(s), '0', 'true', '--not', '--seg', '60000'], capture_output=True, text=True)
    if g.returncode: print('packer failed:', g.stderr[-300:]); return 1
    txt = open(raw).read()
    i = txt.index('def c_Kw_0'); j = txt.index('/-- Every circuit')
    body = txt[i:j]
    body = re.sub(r'^(def c_\w+ : List Nat := \[)', r'set_option maxRecDepth 1000000 in\n\1', body, flags=re.M)
    body = re.sub(r'^(theorem )', r'set_option maxRecDepth 1000000 in\nset_option maxHeartbeats 0 in\n\1', body, flags=re.M)
    info = g.stdout.strip().split('\n')[-1]
    head = f'''import Mathlib
import PEqualNP.Defs
import PEqualNP.Library.LRAT.PromiseN

-- No AND/OR/NOT circuit of fan-in two with at most {s} gates represents the {n} by {n} graph with mask {M} on the
-- one-a-side promise.  The formula handed to the checker is the library formula
--   enc2 ({n} + {n}) {s} (Promise.gMask {n} {n} {M}) (Promise.repRows {n} {n})
-- itself; the certificate is a CaDiCaL LRAT refutation, trimmed and packed by the project's
-- notes/data/lrat-link/genrow.py ({info}).

namespace {ns}
open PEqualNP.Library.LRAT PEqualNP.Library.LRAT.LinkN

def F : List (List ℕ) := enc2 ({n} + {n}) {s} (Promise.gMask {n} {n} {M}) (Promise.repRows {n} {n})

'''
    tail = f'''end {ns}

theorem PEqualNP.Outside.{tag} : {stmt} :=
  PEqualNP.Library.LRAT.PromiseN.repN_lower_mask {n} {n} {M} {s} {ns}.unsat
'''
    open(out, 'w').write(head + body + tail)
    print(f'wrote {out}: {os.path.getsize(out)} bytes; {info}')
    return 0

if __name__ == '__main__':
    sys.exit(main())
