#!/usr/bin/env python3
"""Rows "Three ordered outputs a, b, c exceed N gates at a two-NOT limit" (the negated twins of the "fit" rows).

The proof text is that of the merged L_meta_49854 (Jack Taylor-Crush, same repository, Apache-2.0): a search over
sets of five-bit wire patterns, run by Lean's kernel, with a proof that it covers every circuit of the statement.
Only the three numbers and the gate bound change.  This program first checks by its own search (genfit.least) that
no circuit of that size exists, so that a file is written only for a true row.

  python3 genexceed.py <step id> <statement file> <out.lean>
Exit 0: file written.  Exit 1: a circuit of that size exists (the row is false).  Exit 3: not a row of this family."""
import os, re, subprocess, sys
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
import genfit
TEMPLATE_ID = 'L_meta_49854'

def template():
    return subprocess.run(['git', '-C', '/home/user/pequalnp-proofs', 'show', f'upstream/main:lean/PEqualNP/Outside/{TEMPLATE_ID}.lean'],
                          capture_output=True, text=True, check=True).stdout

def build(step, stmt):
    if not (stmt.startswith('¬ (') and stmt.endswith(')')): return 3, None
    m = genfit.PAT.match(stmt[3:-1])
    if not m: return 3, None
    N, a, b, c = map(int, m.groups())
    if max(a, b, c) > 31 or len({a, b, c}) < 3: return 3, None       # the template's proof asks for three different patterns below 32
    n, _ = genfit.least([a, b, c], N)
    if n is not None: return 1, None
    t = template()
    def rep(old, new, count=1):
        nonlocal t
        assert t.count(old) == count, (old, t.count(old)); t = t.replace(old, new)
    rep('theorem cert : reach 5 20 25 5 2 S0 = false := by decide +kernel', f'theorem cert : reach {a} {b} {c} {N} 2 S0 = false := by decide +kernel')
    rep('  have := sound 5 20 25 (by decide)', f'  have := sound {a} {b} {c} (by decide)')
    rep('    6 S0 5 2 (fun t => by simp)', f'    6 S0 {N} 2 (fun t => by simp)')
    # the two statements: the posted one, verbatim
    i0 = t.index('theorem main : ') + len('theorem main : '); i1 = t.index(' := by\n', i0)
    t = t[:i0] + stmt + t[i1:]
    i0 = t.index(f'theorem PEqualNP.Outside.{TEMPLATE_ID} : ') + len(f'theorem PEqualNP.Outside.{TEMPLATE_ID} : '); i1 = t.index(f' :=\n  PEqualNP.Outside.{TEMPLATE_ID}.main', i0)
    t = t[:i0] + stmt + t[i1:]
    t = t.replace(TEMPLATE_ID, step.replace('-', '_'))
    t = t.replace('import PEqualNP.Defs\n', 'import PEqualNP.Defs\n\n-- The whole proof text is that of the merged ' + TEMPLATE_ID + ' (Jack Taylor-Crush, same repository, Apache-2.0);\n-- only the three patterns and the gate bound of this row were put in.\n', 1)
    return 0, t

if __name__ == '__main__':
    step, sf, out = sys.argv[1:4]
    rc, txt = build(step, open(sf).read().strip())
    if rc == 0: open(out, 'w').write(txt); print('written')
    else: print('a circuit of that size exists: the row is false' if rc == 1 else 'not a row of this family')
    sys.exit(rc)
