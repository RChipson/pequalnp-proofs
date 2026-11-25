#!/usr/bin/env python3
"""Rectangle-cover steps ("the b-entries of an R by C 0/1 matrix are covered by at most K
all-b rectangles"): search for the cover and write the Lean proof.

  python3 rectcover.py <step id> <statement file> <out.lean> [seconds] [K override for a trial]

The statement is parsed (rows as a list of numbers, bit j of row i is the entry in column j).
If it starts with the negation sign the row says no such cover exists; this tool then only
reports whether a cover is found (which would show that row false), and writes no file.
Exit code 0: a proof file was written. 3: a cover was found for a negated row. 1: none found."""
import os, re, subprocess, sys, time
HERE = os.path.dirname(os.path.abspath(__file__))

def parse(stmt):
    neg = stmt.startswith('¬')
    m = re.search(r'∃ L : List \(Finset \(Fin (\d+)\) × Finset \(Fin (\d+)\)\), L\.length ≤ (\d+) ∧', stmt)
    rows = re.search(r'\(\(\[([0-9, ]+)\] : List ℕ\)\.getD i\.val 0\)\.testBit j\.val = (true|false)', stmt)
    if not m or not rows: return None
    R, C, K = int(m.group(1)), int(m.group(2)), int(m.group(3))
    lit = rows.group(1); vals = [int(x) for x in lit.split(',')]; b = rows.group(2)
    return neg, R, C, K, lit, vals, b

def search(R, C, K, vals, b, seconds, work):
    # the annealer covers zeros; for the colour true the matrix is complemented within C columns
    allc = (1 << C) - 1
    rows = [(vals[i] if i < len(vals) else 0) & allc for i in range(R)]
    if b == 'true': rows = [r ^ allc for r in rows]
    os.makedirs(work, exist_ok=True)
    exe = f'{work}/rc'
    subprocess.run(['gcc', '-O2', '-o', exe, f'{HERE}/rc.c', '-lm'], check=True)
    open(f'{work}/mat.txt', 'w').write(f'{R} {C}\n' + ' '.join(map(str, rows)) + '\n')
    nproc = max(1, (os.cpu_count() or 2) - 1)
    end = time.time() + seconds; seed = int(time.time()) % 100000
    while time.time() < end:
        procs = []
        for p in range(nproc):
            seed += 1
            procs.append(subprocess.Popen([exe, f'{work}/mat.txt', str(K), str(seed), '60000000', '1.5', '0.03', '50'],
                                          stdout=subprocess.PIPE, stderr=subprocess.DEVNULL, text=True))
        found = None
        while procs and not found and time.time() < end + 60:
            for p in list(procs):
                if p.poll() is not None:
                    out = p.stdout.read(); procs.remove(p)
                    if out.startswith('FOUND'):
                        found = [tuple(map(int, l.split())) for l in out.strip().split('\n')[1:]]
            time.sleep(0.5)
        for p in procs: p.kill()
        if found:
            # check the cover here before anything is written
            zero = lambda i, j: not (rows[i] >> j & 1)
            assert len(found) <= K
            for s, q in found:
                assert all(zero(i, j) for i in range(R) if s >> i & 1 for j in range(C) if q >> j & 1)
            assert all(any(s >> i & 1 and q >> j & 1 for s, q in found) for i in range(R) for j in range(C) if zero(i, j))
            return found
    return None

def lean(step, stmt, R, C, lit, b, cover):
    ns = 'PEqualNP.Outside.' + step.replace('-', '_')
    entry = f'(([{lit}] : List ℕ).getD i.val 0).testBit j.val = {b}'
    masks = ', '.join(f'({s}, {q})' for s, q in cover)
    return f'''import Mathlib
import PEqualNP.Defs

namespace {ns}

-- The rectangles, each given by a mask of rows and a mask of columns (found by a search over
-- sets of rows, each taken with all columns that have the wanted entry on the whole set).
def masks : List (ℕ × ℕ) :=
  [{masks}]

def rect (s q : ℕ) : Finset (Fin {R}) × Finset (Fin {C}) :=
  (Finset.univ.filter (fun i : Fin {R} => s.testBit i.val = true),
   Finset.univ.filter (fun j : Fin {C} => q.testBit j.val = true))

def cover : List (Finset (Fin {R}) × Finset (Fin {C})) := masks.map (fun m => rect m.1 m.2)

theorem inside : ∀ m ∈ masks, ∀ (i : Fin {R}) (j : Fin {C}),
    m.1.testBit i.val = true → m.2.testBit j.val = true →
    {entry} := by
  decide +kernel

theorem covered : ∀ (i : Fin {R}) (j : Fin {C}),
    {entry} →
    ∃ m ∈ masks, m.1.testBit i.val = true ∧ m.2.testBit j.val = true := by
  decide +kernel

end {ns}

theorem {ns} : {stmt} := by
  refine ⟨{ns}.cover, ?_, ?_, ?_⟩
  · simp [{ns}.cover, {ns}.masks]
  · intro r hr i hi j hj
    obtain ⟨m, hm, rfl⟩ := List.mem_map.mp hr
    simp only [{ns}.rect, Finset.mem_filter, Finset.mem_univ, true_and] at hi hj
    exact {ns}.inside m hm i j hi hj
  · intro i j h
    obtain ⟨m, hm, h1, h2⟩ := {ns}.covered i j h
    refine ⟨{ns}.rect m.1 m.2, List.mem_map.mpr ⟨m, hm, rfl⟩, ?_, ?_⟩
    · simp [{ns}.rect, h1]
    · simp [{ns}.rect, h2]
'''

def main():
    step, sf, out = sys.argv[1:4]
    seconds = int(sys.argv[4]) if len(sys.argv) > 4 else 600
    stmt = open(sf).read().strip()
    p = parse(stmt)
    if not p: print('not a rectangle-cover statement'); return 2
    neg, R, C, K, lit, vals, b = p
    if len(sys.argv) > 5: K = int(sys.argv[5])
    if C > 63 or R > 64: print('matrix too large for this tool'); return 2
    cover = search(R, C, K, vals, b, seconds, out + '.work')
    if not cover: print(f'no cover with {K} rectangles found in {seconds} s'); return 1
    if neg or len(sys.argv) > 5:
        print(f'a cover with {K} rectangles exists:', cover); return 3
    open(out, 'w').write(lean(step, stmt, R, C, lit, b, cover))
    print('wrote', out); return 0

if __name__ == '__main__':
    sys.exit(main())
