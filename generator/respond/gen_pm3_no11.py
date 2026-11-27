#!/usr/bin/env python3
"""Proof of a unit "Perfect matching on a 3 by 3 graph: no normal-form circuit of at most 11 gates opens with <gate>,
then <gate>" by the counting argument of the merged L_meta_27140 (green-notes; same repository, Apache-2.0):
if for every input there are two inputs differing only there, on which the function differs and the two opening
gates do not, then the remaining gates must read all nine inputs and every gate wire but the last, so there are
at least ten of them.  The witnesses are found here; the Lean text is that proof with this unit's gates and list.
  python3 gen_no11.py <step id> <statement file> <out.lean>      exit 0 written; 3 the argument does not apply"""
import re, sys
step, sf, out = sys.argv[1:4]
stmt = open(sf).read().strip()
TPL = __import__('subprocess').run(['git', '-C', '/home/user/pequalnp-proofs', 'show', 'upstream/main:lean/PEqualNP/Outside/L_meta_27140.lean'], capture_output=True, text=True, check=True).stdout
m = re.search(r'C\.gates\.head\? = some ⟨PEqualNP\.CircuitLowerBounds\.GateOp\.(and|or|not), \[([0-9, ]+)\]⟩ ∧\s*C\.gates\.tail\.head\? = some ⟨PEqualNP\.CircuitLowerBounds\.GateOp\.(and|or|not), \[([0-9, ]+)\]⟩\)$', stmt)
if not m or not stmt.startswith('¬ (∃ C') or 'C.size ≤ 11 ∧' not in stmt: print('not a unit of this form'); sys.exit(3)
g1 = (m.group(1), [int(x) for x in m.group(2).split(',')]); g2 = (m.group(3), [int(x) for x in m.group(4).split(',')])
if any(w >= 9 for w in g1[1] + g2[1]) or 'not' in (g1[0], g2[0]) or len(g1[1]) != 2 or len(g2[1]) != 2: print('an opening gate reads a gate wire or is a NOT: the argument does not apply'); sys.exit(3)
def tgt(x):
    b = [x >> i & 1 for i in range(9)]
    return bool((b[0] and b[4] and b[8]) or (b[0] and b[5] and b[7]) or (b[1] and b[3] and b[8]) or (b[1] and b[5] and b[6]) or (b[2] and b[3] and b[7]) or (b[2] and b[4] and b[6]))
def gv(g, x):
    a, b = (x >> g[1][0] & 1), (x >> g[1][1] & 1)
    return (a & b) if g[0] == 'and' else (a | b)
wl = []
for i in range(9):
    w = next((x for x in range(512) if not (x >> i & 1) and tgt(x) != tgt(x ^ (1 << i)) and gv(g1, x) == gv(g1, x ^ (1 << i)) and gv(g2, x) == gv(g2, x ^ (1 << i))), None)
    if w is None: print(f'no pair of inputs for input {i}: the argument does not apply'); sys.exit(3)
    wl.append(w)
ident = step.replace('-', '_')
t = TPL
i0 = t.index('theorem PEqualNP.Outside.L_meta_27140 :'); i1 = t.index(':= by', i0)
t = t[:i0] + 'theorem PEqualNP.Outside.L_meta_27140 : ' + stmt + ' ' + t[i1:]
old_ga = 'def ga : Gate := ⟨GateOp.and, [0, 1]⟩'; old_gb = 'def gb : Gate := ⟨GateOp.and, [0, 5]⟩'; old_wl = 'def wl : List Nat := [272, 96, 80, 132, 68, 66, 20, 12, 10]'
assert t.count(old_ga) == 1 and t.count(old_gb) == 1 and t.count(old_wl) == 1
t = t.replace(old_ga, f'def ga : Gate := ⟨GateOp.{g1[0]}, [{g1[1][0]}, {g1[1][1]}]⟩').replace(old_gb, f'def gb : Gate := ⟨GateOp.{g2[0]}, [{g2[1][0]}, {g2[1][1]}]⟩').replace(old_wl, f'def wl : List Nat := {wl}')
t = t.replace('L_meta_27140', ident)
t = t.replace('import PEqualNP.Defs\n', 'import PEqualNP.Defs\n-- The counting argument and its Lean text are those of the merged L_meta_27140 (same repository, Apache-2.0);\n-- the two opening gates and the list of witness inputs are this unit\'s.\n', 1)
open(out, 'w').write(t); print('written', g1, g2, wl); sys.exit(0)
