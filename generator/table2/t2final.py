# The statement-specific tail of a Table 2 proof file: the row checks, cut into pieces.
import re
import t2lib, t2search
from t2search import Search, tests, cmpX, cM

def parse_statement(stmt):
    m = re.fullmatch(r'∀ t : ℕ, PEqualNP\.MetaComplexity\.HasCircuitSize 8 \(fun x : Fin 8 → Bool => (.*)\) t → (\d+) ≤ t', stmt.strip())
    assert m, 'statement is not of the Table 2 shape'
    body, bound = m.group(1), int(m.group(2))
    parts = body.split(' || ')
    E = []
    for p in parts:
        mm = re.fullmatch(r'\(x (\d) && x (\d)\)', p)
        assert mm, 'unexpected term ' + p
        E.append((int(mm.group(1)), int(mm.group(2))))
    return body, bound, E

DEC = 'set_option maxRecDepth 100000 in\n'
import os
ROWS = int(os.environ.get('T2_ROWS', '8'))

class Planner:
    def __init__(self, row, K, thresh, out):
        self.row, self.K, self.thresh, self.out = row, K, thresh, out
        self.n = 0
        self.leaves = []
    def name(self, kind):
        self.n += 1
        return f'{kind}{self.row.i}_{self.n}'
    def pstr(self, path):
        return '[' + ', '.join(f'({a}, {b})' for a, b in path) + ']'
    def leaf(self, kind, stmt, cost):
        nm = self.name(kind)
        self.out.append(f'  have {nm} : {stmt} := by decide +kernel')
        self.leaves.append(cost)
        return nm
    def node(self, k, st, path):
        # proves: sS i K path k = false   (k steps left at the state st, k >= 1)
        i, K, P = self.row.i, self.K, self.pstr(path)
        tl = tests(st[0])
        costs = []
        for t in tl:
            s = Search(self.row)
            assert not s.cand(k - 1, st, t), 'a circuit was found'
            costs.append(s.cost)
        order = sorted(range(len(tl)), key=lambda x: -costs[x])
        rest = sum(costs)
        skip = []
        for idx in order:
            if rest <= self.thresh or costs[idx] == 0:
                break
            skip.append(idx)
            rest -= costs[idx]
        skip.sort()
        assert skip, 'node below the threshold'
        rn = self.leaf('r', f'rO {i} {K} {P} {k - 1} [{", ".join(map(str, skip))}] = true', rest)
        cts = []
        for idx in skip:
            t = tl[idx]
            if costs[idx] <= self.thresh:
                cts.append(self.leaf('c', f'cT {i} {K} {P} {k - 1} {idx} = false', costs[idx]))
                continue
            tts = []
            for d in range(4):
                s = Search(self.row)
                assert not s.tryT(k - 1, st, t, d)
                if s.cost <= self.thresh:
                    tts.append(self.leaf('t', f'tT {i} {K} {P} {k - 1} {idx} {d} = false', s.cost))
                else:
                    child = self.node(k - 1, s.kid(st, t, d), [(idx, d)] + path)
                    nm = self.name('t')
                    self.out.append(f'  have {nm} : tT {i} {K} {P} {k - 1} {idx} {d} = false :=\n'
                                    f'    tT_of {i} {K} {P} {k - 1} {idx} {d} {child}')
                    tts.append(nm)
            nm = self.name('c')
            self.out.append(f'  have {nm} : cT {i} {K} {P} {k - 1} {idx} = false := by\n'
                            f'    refine cT_of {i} {K} {P} {k - 1} {idx} (fun d hd => ?_)\n'
                            f'    interval_cases d\n' + '\n'.join(f'    · exact {x}' for x in tts))
            cts.append(nm)
        nm = self.name('s')
        lines = [f'  have {nm} : sS {i} {K} {P} {k} = false := by',
                 f'    refine sS_of {i} {K} {P} {k - 1} [{", ".join(map(str, skip))}] {rn} (fun idx hmem => ?_)',
                 f'    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem']
        if len(skip) == 1:
            lines += ['    rw [hmem]', f'    exact {cts[0]}']
        else:
            lines.append('    rcases hmem with ' + ' | '.join(['e'] * len(skip)))
            for c in cts:
                lines += ['    · rw [e]', f'      exact {c}']
        self.out.append('\n'.join(lines))
        return nm

def split_row(row, K, thresh, out):
    i = row.i
    pl = Planner(row, K, thresh, out)
    sn = pl.node(K, row.root(K), [])
    out.append(f'  have rt_{i} : rootTest {i} {K} = false := root_of {i} {K} {sn}')
    out.append(f'  have ckl_{i} : chkL {i} {K} = true := by decide +kernel')
    out.append(f'  have ckh_{i} : chk {i} = true := chk_of_light {i} {K} ckl_{i} rt_{i}')
    return pl.leaves

def tail(stmt, tab, thresh=5000, log=None):
    body, bound, E = parse_statement(stmt)
    N = len(tab)
    PI = [t2lib.pack(x) for x in t2lib.XT]
    word = ' ||| '.join(f'(PIl.getD (({a} : Fin 8) : Nat) 0 &&& PIl.getD (({b} : Fin 8) : Nat) 0)' for a, b in E)
    out = []
    out.append(f'def rootW : Nat := {word}\n')
    out.append(f'''theorem sample_ok (s : Nat) :
    (fun x : Fin 8 → Bool => {body}) (fun j => (PIl.getD (j : Nat) 0).testBit s) = rootW.testBit s := by
  unfold rootW
  simp only [Nat.testBit_or, Nat.testBit_and]
''')
    out.append(f'{DEC}theorem root_eq : rootW = pack (keyAt cI0) := by decide +kernel\n')
    out.append('theorem root_bd : Nat.land rootW FU = rootW := by decide +kernel\n')
    out.append(f'theorem root_val : valAt cI0 = {bound} := by decide +kernel\n')
    out.append('theorem root_lt : cI0 < cN := by decide +kernel\n')
    pieces = []
    items = []      # ('split', i) | ('range', a, n)
    a, acc = None, 0
    total, biggest = 0, 0
    for i in range(N):
        row = t2search.Row(tab, i, PI)
        ok, costs = t2search.row_cost(row)
        if not ok:
            raise SystemExit(f'row {i} does not close: its bound {tab[i][1]} is not proved by this search')
        c = sum(x for _, x in costs)
        total += c
        if c > thresh:
            heavy = [k for k, x in costs if x > thresh]
            assert len(heavy) == 1, 'two heavy levels in one row'
            if a is not None:
                items.append(('range', a, i - a)); a = None
            items.append(('split', i))
            lv = split_row(row, heavy[0], thresh, pieces)
            biggest = max([biggest] + lv)
            if log: log(f'row {i}: rank {row.rank}, bound {row.V}, cost {c}, cut into {len(lv)} pieces (largest {max(lv)})')
        else:
            if a is not None and (acc + c > thresh or i - a >= ROWS):
                items.append(('range', a, i - a)); a = None
            if a is None:
                a, acc = i, 0
            acc += c
            biggest = max(biggest, acc)
    if a is not None:
        items.append(('range', a, N - a))
    for it in items:
        if it[0] == 'range':
            _, a, n = it
            pieces.append(f'  have ck_{a} : allFrom chk {n} {a} = true := by decide +kernel')
    lines = ['-- All the kernel checks run inside this one proof, one after the other.',
             'set_option maxRecDepth 100000 in',
             'set_option maxHeartbeats 8000000 in',
             'theorem hall : ∀ j, j < cN → chk j = true := by'] + pieces + ['  intro j hj', f'  have hj2 : j < {N} := hj']
    def use(it, ind):
        if it[0] == 'split':
            return [f'{ind}have e : j = {it[1]} := by omega', f'{ind}rw [e]', f'{ind}exact ckh_{it[1]}']
        _, a, n = it
        return [f'{ind}exact allFrom_ok chk {n} {a} ck_{a} j (by omega) (by omega)']
    for it in items[:-1]:
        end = it[1] + (1 if it[0] == 'split' else it[2])
        lines.append(f'  rcases Nat.lt_or_ge j {end} with h{end} | h{end}')
        u = use(it, '    ')
        lines.append('  · ' + u[0].strip())
        lines += u[1:]
    lines += use(items[-1], '  ')
    out.append('\n'.join(lines) + '\n')
    out.append(f'''theorem main : ∀ t : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 8 (fun x : Fin 8 → Bool => {body}) t → {bound} ≤ t := by
  intro t ht
  obtain ⟨C, hC, hsz, he⟩ := ht
  have hB := bound_at hall (rankAt cI0) cI0 rfl root_lt
  obtain ⟨p0, p1, _, _⟩ := chk_parts cI0 (hall cI0 root_lt)
  rw [← root_eq] at p0 p1
  obtain ⟨zs, hl, hs, ht2⟩ := circuit_slp (fun x : Fin 8 → Bool => {body}) rootW ⟨p0, p1⟩ root_bd
    (fun s _ => sample_ok s) C hC he
  have h1 := hB zs hs (by rw [← root_eq]; exact ht2)
  rw [root_val, hl] at h1
  exact le_trans h1 hsz
''')
    if log: log(f'total cost {total}, largest single piece {biggest}')
    return '\n'.join(out), bound, E, total, biggest
