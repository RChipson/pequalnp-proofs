#!/usr/bin/env python3
"""Write the Lean proof for a row "Resolution on the pigeonhole formula with m pigeons and n holes: some
refutation has at most N lines" from a refutation saved by resenc.py (or lns.py).  The proof text is
the checked L-pcx-171 (willakone) with its certificate replaced.

  python3 genres.py <step id> <statement file> <refutation.json> <out.lean>"""
import json, os, re, sys
HERE = os.path.dirname(os.path.abspath(__file__))

def check(m, n, lines, hints):
    import resenc
    ax = [sorted(a) for a in resenc.axioms(m, n)]
    for r, (cl, h) in enumerate(zip(lines, hints)):
        if h is None: assert sorted(cl) in ax, r
        else:
            i, j, v = h; assert i < r and j < r and 2 * v in lines[i] and 2 * v + 1 in lines[j]
            assert sorted(cl) == sorted((set(lines[i]) - {2 * v}) | (set(lines[j]) - {2 * v + 1})), r
    assert [] in [list(c) for c in lines]

def main():
    step, sf, jf, out = sys.argv[1:5]
    stmt = open(sf).read().strip(); d = json.load(open(jf)); m, n, lines, hints = d['m'], d['n'], d['lines'], d['hints']
    mm = re.fullmatch(r'∃ π : List \(PEqualNP\.ProofComplexity\.Clause \(Fin (\d+) × Fin (\d+)\)\), PEqualNP\.ProofComplexity\.IsRefutation \(PEqualNP\.ProofComplexity\.PHP (\d+) (\d+)\) π ∧ π\.length ≤ (\d+)', stmt)
    assert mm and int(mm.group(1)) == m and int(mm.group(2)) == n, 'statement shape'
    bound = int(mm.group(5)); assert len(lines) <= bound, (len(lines), bound)
    check(m, n, lines, hints)
    name = step.replace('-', '_'); ns = f'PEqualNP.Outside.{name}_aux'
    V = f'Fin {m} × Fin {n}'
    def lit(l): return f'(({(l // 2) // n}, {(l // 2) % n}), {"true" if l % 2 == 0 else "false"})'
    def cl(c): return '∅' if not c else '{' + ', '.join(lit(l) for l in c) + '}'
    N = len(lines); ent = []
    for r in range(N - 1, -1, -1):
        h = hints[r]
        if h is None: ent.append(f'  ({cl(lines[r])}, none)')
        else:
            i, j, v = h; ent.append(f'  ({cl(lines[r])}, some ({r - 1 - i}, {r - 1 - j}, ({v // n}, {v % n})))')
    head = open(f'{HERE}/template_171_head.lean').read().replace('L_pcx_171', name)
    head = head.replace('namespace PEqualNP.Outside.' + name + '_aux', '-- The checking code is that of the checked proof of L-pcx-171; only the refutation is new.\nnamespace PEqualNP.Outside.' + name + '_aux', 1)
    body = f'def cert : List (Clause ({V}) × Option (ℕ × ℕ × ({V}))) := [\n' + ',\n'.join(ent) + ']\n\n'
    tail = f'''set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hc : chkR (axPHP {m} {n}) cert = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem hm : (∅ : Clause ({V})) ∈ cert.map Prod.fst := by decide +kernel

set_option maxRecDepth 100000 in
theorem hl : (cert.map Prod.fst).length ≤ {bound} := by decide +kernel

end {ns}

theorem PEqualNP.Outside.{name} : {stmt} := by
  exact ⟨{ns}.cert.map Prod.fst, ⟨{ns}.chkR_sound _ ({ns}.axPHP {m} {n}) ({ns}.axPHP_sound {m} {n}) _ {ns}.hc, {ns}.hm⟩, {ns}.hl⟩
'''
    open(out, 'w').write(head + body + tail)
    print('wrote', out, 'with', N, 'lines for the bound', bound)

if __name__ == '__main__':
    sys.path.insert(0, HERE); main()
