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
T4 = 'L_meta_49854'      # four ordered bits (Jack Taylor-Crush)
T5 = 'L_meta_50103'      # five ordered bits (ptrdsh)

def template(tid):
    return subprocess.run(['git', '-C', '/home/user/pequalnp-proofs', 'show', f'upstream/main:lean/PEqualNP/Outside/{tid}.lean'],
                          capture_output=True, text=True, check=True).stdout

def build(step, stmt):
    if not (stmt.startswith('¬ (') and stmt.endswith(')')): return 3, None
    q0 = genfit.parse(stmt[3:-1])
    if not q0: return 3, None
    n, B, N, a, b, c = q0
    if B != 2 or n not in (4, 5): return 3, None
    if n == 5 and N >= 6: return 3, None      # that file needs over ten minutes and 13 GB to compile here
    k, _ = genfit.least([a, b, c], N, B, n)
    if k is not None: return 1, None
    ns = step.replace('-', '_')
    if n == 4:
        if len({a, b, c}) < 3: return 3, None       # that proof asks for three different patterns
        t = template(T4)
        def rep(old, new, count=1):
            nonlocal t
            assert t.count(old) == count, (old, t.count(old)); t = t.replace(old, new)
        rep('theorem cert : reach 5 20 25 5 2 S0 = false := by decide +kernel', f'theorem cert : reach {a} {b} {c} {N} 2 S0 = false := by decide +kernel')
        rep('  have := sound 5 20 25 (by decide)', f'  have := sound {a} {b} {c} (by decide)')
        rep('    6 S0 5 2 (fun t => by simp)', f'    6 S0 {N} 2 (fun t => by simp)')
        i0 = t.index('theorem main : ') + len('theorem main : '); i1 = t.index(' := by\n', i0)
        t = t[:i0] + stmt + t[i1:]
        i0 = t.index(f'theorem PEqualNP.Outside.{T4} : ') + len(f'theorem PEqualNP.Outside.{T4} : '); i1 = t.index(f' :=\n  PEqualNP.Outside.{T4}.main', i0)
        t = t[:i0] + stmt + t[i1:]
        t = t.replace(T4, ns); who = T4 + ' (Jack Taylor-Crush'
    else:
        if not a < b < c: return 3, None            # that proof asks for the three patterns in increasing order
        t = template(T5)
        i0 = t.index(f'theorem PEqualNP.Outside.{T5} : ') + len(f'theorem PEqualNP.Outside.{T5} : '); i1 = t.index(f' :=\n  PEqualNP.Outside.{T5}_aux.final ', i0)
        tail = f' :=\n  PEqualNP.Outside.{T5}_aux.final {N} {a} {b} {c} (by decide +kernel)\n'
        t = t[:i0] + stmt + tail
        t = t.replace(T5, ns); who = T5 + ' (ptrdsh'
    t = t.replace('import PEqualNP.Defs\n', 'import PEqualNP.Defs\n\n-- The whole proof text is that of the merged ' + who + ', same repository, Apache-2.0);\n-- only the three patterns and the gate bound of this row were put in.\n', 1)
    return 0, t

if __name__ == '__main__':
    step, sf, out = sys.argv[1:4]
    rc, txt = build(step, open(sf).read().strip())
    if rc == 0: open(out, 'w').write(txt); print('written')
    else: print('a circuit of that size exists: the row is false' if rc == 1 else 'not a row of this family')
    sys.exit(rc)
