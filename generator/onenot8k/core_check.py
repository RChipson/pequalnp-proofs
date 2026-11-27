#!/usr/bin/env python3
"""Check the heavy kernel-evaluated steps of a generated file in a small environment.

A file of a 15-gate graph has steps `... := by decide +kernel` whose evaluation needs more memory than this
machine has once the whole library is loaded (loading it alone takes about 5 GB).  Such a step is a closed
statement about definitions made of Nat, List and Bool only.  This program copies those definitions, word for
word, into a file that imports nothing, and lets Lean's kernel check the same steps there.

  python3 core_check.py <file.lean> <out.lean> [name pattern of the steps, default r[12]_\\d+(_\\d+|_pre)?]
Writes out.lean (the definitions needed and the chosen steps).  It is compiled with compile_capped.py."""
import re, sys
STARTS = ('def ', 'noncomputable def ', 'abbrev ', 'lemma ', 'theorem ', 'private ', 'set_option ', 'section', 'noncomputable section', 'end', 'namespace ',
          'variable ', 'open ', 'inductive ', 'structure ', 'instance ', '@[', 'import ', '--', 'local ', 'omit ', 'include ', 'example ')

def blocks(t):
    out = []; cur = []
    for l in t.split('\n'):
        if l.startswith(STARTS) or (cur and not l.strip()):
            if cur: out.append('\n'.join(cur))
            cur = [l] if l.strip() else []
        elif cur: cur.append(l)
    if cur: out.append('\n'.join(cur))
    # a set_option line belongs to the declaration under it
    merged = []; pre = ''
    for b in out:
        if b.startswith('set_option '): pre += b + '\n'; continue
        merged.append(pre + b); pre = ''
    return merged

def name_of(b):
    m = re.search(r'^(?:noncomputable )?(?:def|abbrev|structure|inductive) ([A-Za-z_][A-Za-z0-9_\']*)', b, re.M)
    return m.group(1) if m else None

def build(t, pat):
    bl = blocks(t); defs = {}; order = []
    for b in bl:
        n = name_of(b)
        if n and n not in defs: defs[n] = b; order.append(n)
    steps = [b for b in bl if re.search(r'^theorem (%s) : [^\n]* := by decide \+kernel$' % pat, b, re.M)]
    need = set(); todo = []
    for s in steps: todo += re.findall(r'[A-Za-z_][A-Za-z0-9_\']*', s)
    while todo:
        w = todo.pop()
        if w in defs and w not in need:
            need.add(w); todo += re.findall(r'[A-Za-z_][A-Za-z0-9_\']*', defs[w])
    body = '\n'.join(defs[n].replace('noncomputable def ', 'def ') for n in order if n in need)
    return 'notation \"ℕ\" => Nat\nnamespace CoreCheck\nnoncomputable section\n' + body + '\n' + '\n'.join(steps) + '\nend\nend CoreCheck\n', len(steps), sorted(need)

if __name__ == '__main__':
    pat = sys.argv[3] if len(sys.argv) > 3 else r'r[12]_\d+(?:_\d+|_pre)?'
    txt, n, need = build(open(sys.argv[1]).read(), pat)
    open(sys.argv[2], 'w').write(txt); print('steps', n, 'definitions', len(need))
