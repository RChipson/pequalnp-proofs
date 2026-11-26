#!/usr/bin/env python3
"""Rows "No AND/OR/NOT circuit of fan-in two with at most k gates represents the n by n graph with mask
M on the one-a-side promise".

Method: the signed live-wire search of the checked proof of L-meta-8718 (k-sandhu; it says it follows
L-meta-8463 and L-meta-1449).  That search shows that more than k AND/OR gates are needed even when
NOT gates are free, for any circuit that is right on 64 sample inputs.  Here the samples are promise
inputs (one left and one right vertex on), 32 where the graph has an edge paired with 32 where it has
none, so a representing circuit is right on all of them and has more than k gates.

  python3 gennone.py <step id> <statement file> <out.lean>
Exit 0: file written.  Exit 1: the search finds a circuit on every sample choice tried (no proof)."""
import os, random, re, subprocess, sys
HERE = os.path.dirname(os.path.abspath(__file__))
PAT = re.compile(r'¬ ∃ C : PEqualNP\.CircuitLowerBounds\.Circuit, PEqualNP\.MetaComplexity\.FanInTwo C ∧ C\.size ≤ (\d+) ∧ PEqualNP\.Represents\.Represents \(fun u v : Fin (\d+) => \((\d+) : ℕ\)\.testBit \((\d+) \* u\.val \+ v\.val\)\) C')

def words(pairs, nv):
    ws = []
    for j in range(nv):
        w = 0
        for i, (p, q) in enumerate(pairs):
            w |= (p >> j & 1) << i; w |= (q >> j & 1) << (32 + i)
        ws.append(w)
    return ws

def samples(n, mask, k, tries=40, seed=1):
    exe = '/tmp/livesearch_gennone'
    subprocess.run(['gcc', '-O2', '-o', exe, f'{HERE}/../sixinput/livesearch.c'], check=True)
    T = [(1 << u) | (1 << (n + v)) for u in range(n) for v in range(n) if mask >> (n * u + v) & 1]
    F = [(1 << u) | (1 << (n + v)) for u in range(n) for v in range(n) if not mask >> (n * u + v) & 1]
    near = [(p, q) for p in T for q in F if bin(p ^ q).count('1') == 2]; far = [(p, q) for p in T for q in F if bin(p ^ q).count('1') == 4]
    rnd = random.Random(seed); best = None
    for t in range(tries):
        a, b = near[:], far[:]; rnd.shuffle(a); rnd.shuffle(b); pairs = (a + b)[:32]
        if len(pairs) < 32: return None
        ws = words(pairs, 2 * n)
        if len(set(ws)) < 2 * n: continue
        try:
            out = subprocess.run([exe, str(k)] + ['%x' % w for w in ws], capture_output=True, text=True, timeout=10).stdout.split()
        except subprocess.TimeoutExpired:
            continue
        if out and out[0] == 'false' and (best is None or int(out[1]) < best[0]): best = (int(out[1]), ws)
        if best and best[0] < 8000 and t >= 6: break
    return best

def lean(step, stmt, n, mask, k, ws):
    name = step.replace('-', '_'); ns = 'PEqualNP.Outside.' + name
    s = open(f'{HERE}/../sixinput/template_8718.lean').read().replace('L_meta_8718', name)
    head = s.split('def targetFun (T : ℕ)', 1)[0]
    head = head.replace('-- The signed live-wire search follows', '-- The search and its soundness proof are those of the checked proof of L-meta-8718; the samples here\n-- are promise inputs, and the final step is new.\n-- The signed live-wire search follows')
    rows = ', '.join('0x%016x' % w for w in ws)
    A = f'({mask} : ℕ).testBit ({n} * u.val + v.val)'
    return head + f'''-- A circuit that is right on the 64 sample inputs needs more than n AND/OR gates, NOT gates being free.
theorem bound_from_samples (n : ℕ) (inputs : List W) (nd : inputs.Nodup) (reject : search n inputs = false)
    (gs : List Gate) (o : ℕ) (hg : ∀ g ∈ gs, legal g)
    (he : ∀ k : Fin 64, Circuit.eval ⟨gs,o⟩ (inputs.map (bit k)) = bit k (~~~goal)) :
    n < binaryCost gs := by
  by_contra! low
  have init : ∀ u ∈ inputs, holds inputs.toFinset u := by
    intro u hu
    exact .inr (.inr ⟨u, List.mem_toFinset.mpr hu, .inl rfl⟩)
  have evaluate (k : Fin 64) :
      (gs.foldl step (inputs.map (bit k))).getD o false = bit k (~~~goal) := he k
  obtain ⟨t, ht, run⟩ := compile gs o hg inputs inputs.toFinset init evaluate
  have lift {{a b : ℕ}} (h : a ≤ b) (hr : build basicOps t a inputs.toFinset) :
      build basicOps t b inputs.toFinset := by
    induction h with
    | refl => exact hr
    | step _ ih => exact Or.inl ih
  exact Bool.noConfusion (reject.symm.trans (search_complete ht n inputs nd (lift low run)))

def rows : List W :=
  [{rows}]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject : search {k} rows = false := by
  decide +kernel

-- Every sample is a promise input, and the graph's value there is the sample's label.
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem samples_ok : ∀ k : Fin 64, ∃ u v : Fin {n}, rows.map (bit k) = PEqualNP.Represents.oneEach u v ∧
    {A} = bit k (~~~goal) := by
  decide +kernel

theorem main : {stmt} := by
  rintro ⟨C, fits, size, rep⟩
  have bound := bound_from_samples {k} rows (by decide) reject C.gates C.output fits (by
    intro k
    obtain ⟨u, v, hrow, hval⟩ := samples_ok k
    rw [hrow]
    exact (rep u v).trans hval)
  have short : binaryCost C.gates ≤ C.gates.length := List.length_filter_le _ _
  have hs : C.size = C.gates.length := rfl
  omega

end {ns}

theorem {ns} : {stmt} := by
  exact {ns}.main
'''

def main():
    step, sf, out = sys.argv[1:4]
    stmt = open(sf).read().strip(); m = PAT.fullmatch(stmt)
    if not m or m.group(2) != m.group(4): print('not a row of this family'); return 2
    k, n, mask = int(m.group(1)), int(m.group(2)), int(m.group(3))
    best = samples(n, mask, k)
    if not best: print(f'the free-NOT search with {k} steps finds a circuit on every sample choice tried'); return 1
    if best[0] > 300000: print('search too large for the checker:', best[0]); return 1
    open(out, 'w').write(lean(step, stmt, n, mask, k, best[1]))
    print(f'wrote {out}: depth {k}, {best[0]} calls'); return 0

if __name__ == '__main__':
    sys.exit(main())
