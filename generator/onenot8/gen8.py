#!/usr/bin/env python3
"""Rows "At fan-in two, one NOT gate saves nothing on edges ..." for graphs on eight vertices.

Method: the gate-elimination proof of the checked L-meta-14076 (k-sandhu; it says its circuit
restrictions are adapted from L-meta-9349 and L-meta-9129).  Its generic part is used unchanged.
The lower bound is a chain of smaller graphs:
  * fixing a vertex to false removes at least one gate (when the rest still has an edge);
  * a vertex of degree one together with its neighbour (of degree at least two) removes at least
    three gates (when the rest still has an edge);
  * a single edge needs one gate.
This program finds the best such chain (exact, over all subsets of vertices), asks a SAT solver
for an AND/OR circuit with exactly that many gates, and if one exists writes the proof file.

  python3 gen8.py <step id> <statement file> <out.lean>
Exit 0: file written.  Exit 1: the chain bound is below the size of the smallest circuit found."""
import functools, os, re, subprocess, sys
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, '..', 'sixinput'))
N = 8

def parse(stmt):
    if stmt.startswith('¬'): return None
    m = re.search(r'∀ x : Fin 8 → Bool, PEqualNP\.CircuitLowerBounds\.Circuit\.eval ⟨gates, o⟩ \(List\.ofFn x\) = decide \(∃ i < \(\[([0-9, ]+)\] : List ℕ\)\.length / 2', stmt)
    if not m or 'gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not' not in stmt: return None
    v = [int(x) for x in m.group(1).split(',')]
    return [(v[2 * i], v[2 * i + 1]) for i in range(len(v) // 2)]

def chain(edges):
    """Best elimination chain.  Returns (bound, steps); a step is ('base', a, b) | ('del', v, w) | ('arm', leaf, inner, w)."""
    @functools.lru_cache(None)
    def best(E):
        E = list(E)
        if not E: return None
        if len(E) == 1: return (1, (('base', E[0][0], E[0][1]),))
        deg = {}
        for a, b in E: deg[a] = deg.get(a, 0) + 1; deg[b] = deg.get(b, 0) + 1
        res = None
        for v in deg:
            rest = tuple(e for e in E if v not in e)
            r = best(rest)
            if r:
                w = next(b if a == v else a for a, b in E if v in (a, b))
                cand = (r[0] + 1, (('del', v, w),) + r[1])
                if res is None or cand[0] > res[0]: res = cand
        for l in deg:
            if deg[l] != 1: continue
            c = next(b if a == l else a for a, b in E if l in (a, b))
            if deg[c] < 2: continue
            rest = tuple(e for e in E if c not in e)
            r = best(rest)
            if r:
                w = next(b if a == c else a for a, b in E if c in (a, b) and l not in (a, b))
                cand = (r[0] + 3, (('arm', l, c, w),) + r[1])
                if res is None or cand[0] > res[0]: res = cand
        return res
    return best(tuple(sorted(tuple(sorted(e)) for e in edges)))

def graph_circuit(edges, k):
    """An AND/OR fan-in-two circuit with exactly k gates for the edge function, or None (SAT).
    A monotone circuit computes the edge function exactly when it is true on every edge and false on
    every maximal independent set, so only those inputs are constrained."""
    import itertools
    from pysat.solvers import Cadical153
    adj = [0] * N
    for a, b in edges: adj[a] |= 1 << b; adj[b] |= 1 << a
    ind = [s for s in range(1 << N) if all(not (adj[i] & s) for i in range(N) if s >> i & 1)]
    mis = [s for s in ind if all((s >> i & 1) or (adj[i] & s) for i in range(N))]
    rows = [((1 << a) | (1 << b), True) for a, b in edges] + [(s, False) for s in mis]
    R = len(rows); nv = [0]
    def new():
        nv[0] += 1; return nv[0]
    cls = []; val = [[bool(rows[r][0] >> i & 1) for r in range(R)] for i in range(N)]; typ = []; sel = []
    for g in range(k):
        c = new(); typ.append(c)
        pairs = list(itertools.combinations(range(N + g), 2)); ps = [new() for _ in pairs]; sel.append((pairs, ps))
        cls.append(list(ps))
        for a, b in itertools.combinations(ps, 2): cls.append([-a, -b])
        row = [new() for _ in range(R)]
        for (i, j), p in zip(pairs, ps):
            for r in range(R):
                x, y, v = val[i][r], val[j][r], row[r]
                for cv in (True, False):
                    for xv in ((True, False) if not isinstance(x, bool) else (x,)):
                        for yv in ((True, False) if not isinstance(y, bool) else (y,)):
                            o = (xv and yv) if cv else (xv or yv)
                            cl = [-p, -c if cv else c]
                            if not isinstance(x, bool): cl.append(-x if xv else x)
                            if not isinstance(y, bool): cl.append(-y if yv else y)
                            cl.append(v if o else -v); cls.append(cl)
        val.append(row)
    for r in range(R): cls.append([val[-1][r] if rows[r][1] else -val[-1][r]])
    with Cadical153(bootstrap_with=cls) as sol:
        if not sol.solve(): return None
        mod = set(l for l in sol.get_model() if l > 0)
    gates = []
    for g in range(k):
        pairs, ps = sel[g]
        i, j = next(pr for pr, p in zip(pairs, ps) if p in mod)
        gates.append(('and' if typ[g] in mod else 'or', i, j))
    return gates

def gexpr(E):
    return ' || '.join(f'(x {a} && x {b})' for a, b in E)

def lean(step, stmt, edges, bound, steps, gates):
    ns = 'PEqualNP.Outside.' + step.replace('-', '_')
    head = open(f'{HERE}/template_14076_head.lean').read().replace('L_meta_14076', step.replace('-', '_'))
    head = head.replace('-- Circuit restrictions adapted from', '-- The method is that of the checked proof of L-meta-14076, applied to this graph.\n-- Circuit restrictions adapted from')
    out = [head, 'def assignment (a : ℕ) (i : Fin 8) : Bool := a.testBit i.val\n']
    # the chain of graphs
    graphs = [list(edges)]; E = list(edges)
    for st in steps:
        if st[0] == 'del': E = [e for e in E if st[1] not in e]
        elif st[0] == 'arm': E = [e for e in E if st[2] not in e]
        else: break
        graphs.append(E)
    for i, G in enumerate(graphs): out.append(f'def graph{i} (x : Fin 8 → Bool) : Bool := {gexpr(G)}\n')
    last = len(graphs) - 1
    _, a, b = steps[-1]
    out.append(f'def graphV (x : Fin 8 → Bool) : Bool := (x {a})\n')
    out.append('lemma lowerV (t : ℕ) (h : HasCircuitSize 8 graphV t) : 0 ≤ t := by\n  exact Nat.zero_le t\n')
    TAUTO = '<;> simp only [Bool.eq_iff_iff, Bool.and_eq_true, Bool.or_eq_true] <;> tauto'
    out.append(f'''lemma lower{last} (t : ℕ) (h : HasCircuitSize 8 graph{last} t) : 1 ≤ t := by
  have eq : fix graph{last} {b} true = graphV := by
    funext x
    simp [fix, Function.update, graph{last}, graphV] {TAUTO}
  have nc : nonconstant (fix graph{last} {b} true) := eq.symm ▸ ⟨assignment 0, assignment {1 << a}, by decide⟩
  obtain ⟨s, hs, reduced⟩ := q70 7 graph{last} {b} true t ⟨assignment {1 << a}, by decide⟩ nc h
  have bound := lowerV s (eq ▸ reduced)
  omega
''')
    k = 1
    for i in range(last - 1, -1, -1):
        st = steps[i]; G2 = graphs[i + 1]; em = (1 << G2[0][0]) | (1 << G2[0][1])
        if st[0] == 'del':
            v, w = st[1], st[2]
            out.append(f'''lemma lower{i} (t : ℕ) (h : HasCircuitSize 8 graph{i} t) : {k + 1} ≤ t := by
  have eq : fix graph{i} {v} false = graph{i + 1} := by
    funext x
    simp [fix, Function.update, graph{i}, graph{i + 1}] {TAUTO}
  have nc : nonconstant (fix graph{i} {v} false) := eq.symm ▸ ⟨assignment 0, assignment {em}, by decide⟩
  obtain ⟨s, hs, reduced⟩ := q70 7 graph{i} {v} false t ⟨assignment {1 << w}, by decide⟩ nc h
  have bound := lower{i + 1} s (eq ▸ reduced)
  omega
''')
            k += 1
        else:
            l, c, w = st[1], st[2], st[3]
            out.append(f'''lemma lower{i} (t : ℕ) (h : HasCircuitSize 8 graph{i} t) : {k + 3} ≤ t := by
  apply arm_lower (n := 7) (leaf := {l}) (inner := {c}) (g := graph{i + 1})
    (k := {k}) _ _ _ _ lower{i + 1} h
  · exact ⟨assignment {1 << c}, by decide⟩
  · intro b
    cases b
    · exact ⟨assignment {1 << w}, by decide⟩
    · exact ⟨assignment 0, by decide⟩
  · exact ⟨assignment 0, assignment {em}, by decide⟩
  · intro b
    cases b <;> funext x <;> simp [fix, Function.update, graph{i}, graph{i + 1}]
      {TAUTO}
''')
            k += 3
    assert k == bound
    g = ', '.join(f'⟨.{op}, [{i}, {j}]⟩' for op, i, j in gates)
    L = '[' + ', '.join(f'{a}, {b}' for a, b in edges) + ']'
    out.append(f'''def witness : List Gate := [{g}]

theorem witnessBasis : ∀ g ∈ witness,
    (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with {' | '.join(['rfl'] * len(gates))} <;> simp

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem witnessCorrect : ∀ x : Fin 8 → Bool,
    Circuit.eval ⟨witness, {N + len(gates) - 1}⟩ (List.ofFn x) = graph0 x := by
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem graph_correct : ∀ x : Fin 8 → Bool, graph0 x = decide (∃ i < ({L} : List ℕ).length / 2, (List.ofFn x).getD (({L} : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (({L} : List ℕ).getD (2 * i + 1) 0) false = true) := by
  decide +kernel

end {ns}

open {ns} PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity in
theorem {ns} :
{stmt} := by
  intro gates o legal _oneNot computes
  have h : HasCircuitSize 8 graph0 gates.length :=
    ⟨⟨gates, o⟩, legal, le_rfl, fun x => (computes x).trans (graph_correct x).symm⟩
  have large := lower0 gates.length h
  have hw : witness.length = {len(gates)} := rfl
  exact ⟨witness, {N + len(gates) - 1}, witnessBasis, by omega, fun x => (witnessCorrect x).trans (graph_correct x)⟩
''')
    return '\n'.join(out)

def main():
    if sys.argv[1] == 'bound':
        edges = [tuple(map(int, e.split('-'))) for e in sys.argv[2].split()]
        print(chain(edges)); return 0
    step, sf, outp = sys.argv[1:4]
    stmt = open(sf).read().strip()
    edges = parse(stmt)
    if not edges: print('not an eight-vertex one-NOT row'); return 2
    r = chain(edges)
    if not r: print('no chain'); return 1
    bound, steps = r
    import gen6
    gen6.N = 8
    T = sum(1 << x for x in range(256) if any(x >> a & 1 and x >> b & 1 for a, b in edges))
    try:
        res = subprocess.run([sys.executable, os.path.abspath(__file__), 'synth', ' '.join(f'{a}-{b}' for a, b in edges), str(bound)], capture_output=True, text=True, timeout=int(os.environ.get('SYNTH8', '90')))
    except subprocess.TimeoutExpired:
        print(f'chain bound {bound}: the search for a circuit of that size timed out'); return 1
    if not res.stdout.startswith('GATES'):
        print(f'chain bound {bound}: no AND/OR circuit with that many gates (the bound is not tight)'); return 1
    gates = eval(res.stdout[5:])
    assert gen6.check_circuit(T, gates)
    open(outp, 'w').write(lean(step, stmt, edges, bound, steps, gates))
    print(f'wrote {outp}: bound {bound}, chain {[s[0] for s in steps]}'); return 0

if __name__ == '__main__':
    if len(sys.argv) > 1 and sys.argv[1] == 'synth':
        g = graph_circuit([tuple(map(int, e.split('-'))) for e in sys.argv[2].split()], int(sys.argv[3]))
        print('GATES' + repr(g) if g else 'NONE'); sys.exit(0)
    sys.exit(main())
