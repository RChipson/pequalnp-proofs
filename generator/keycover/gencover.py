#!/usr/bin/env python3
"""Write a Lean proof for a "fixed n by n graph given by its table" row of the desk:
   some AND/OR/NOT circuit of fan-in two with at most k gates is right on the promise inputs
   (one row and one column on).

The circuit comes from a cover of the ones of the table by all-ones blocks (rows S, columns T):
OR the rows of each block, OR its columns, AND the two, OR all blocks.  ORs are shared between
blocks (cse.paar).  The proof replays the circuit with the project's helper
PEqualNP.Library.Helpers.PromiseColTree.represents_of_tcols.

usage: gencover.py <step id> <statement file> <cover file> <out.lean> [tries]
The cover file has lines  B <S hi> <S lo> <T hi> <T lo>  (hex, 128 bits as two words)."""
import sys, re, random, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from cse import paar
import pairsa

def build(n, blocks, seed, pair_seconds=0):
    rnd = random.Random(seed) if seed else None
    bits = lambda x: frozenset(i for i in range(n) if x >> i & 1)
    gates = []                       # (op, a, b) on wire numbers; wires 0..n-1 rows, n..2n-1 columns
    def side(sets, off):
        wire = {i: off + i for i in range(n)}
        if pair_seconds:
            sets, defs0 = pairsa.pre_pairs(sets, pair_seconds, rnd or random.Random(1))
            sets = [frozenset(x) for x in sets]
            for z, a, b in defs0:
                gates.append(('or', wire[a], wire[b])); wire[z] = 2 * n + len(gates) - 1
        g, defs, cur = paar(sets, rnd)
        for z, a, b in defs:
            gates.append(('or', wire[a], wire[b])); wire[z] = 2 * n + len(gates) - 1
        out = []; memo = {}
        for s in cur:
            k = frozenset(s)
            if k not in memo:
                l = sorted(wire[i] for i in s); w = l[0]
                for x in l[1:]:
                    gates.append(('or', w, x)); w = 2 * n + len(gates) - 1
                memo[k] = w
            out.append(memo[k])
        return out
    xs = side([bits(S) for S, T in blocks], 0)
    ys = side([bits(T) for S, T in blocks], n)
    acc = None
    for x, y in zip(xs, ys):
        gates.append(('and', x, y)); w = 2 * n + len(gates) - 1
        if acc is None: acc = w
        else:
            gates.append(('or', acc, w)); acc = 2 * n + len(gates) - 1
    return gates, acc

def simulate(n, gates, out):
    """every wire as a set of cells u*n+v (a number of n*n bits)"""
    full = (1 << (n * n)) - 1
    W = []
    for u in range(n): W.append(((1 << n) - 1) << (u * n))
    for v in range(n): W.append(sum(1 << (u * n + v) for u in range(n)))
    for op, a, b in gates:
        if op == 'and': W.append(W[a] & W[b])
        elif op == 'or': W.append(W[a] | W[b])
        else: W.append(full ^ W[a])
    return W[out]

def load_blocks(covf):
    blocks = []
    for l in open(covf):
        p = l.split()
        if p and p[0] == 'B': blocks.append((int(p[1] + p[2], 16), int(p[3] + p[4], 16)))
    return blocks

def best_circuit(n, blocks, tries):
    best = None
    for t in range(tries):
        gates, out = build(n, blocks, t)
        if best is None or len(gates) < len(best[0]): best = (gates, out)
    return best

def parse_statement(st):
    rows = [int(h, 16) for h in re.findall(r'0x([0-9a-f]+)', st)]
    n = len(rows)
    k = int(re.search(r'C\.size ≤ (\d+)', st).group(1))
    assert re.search(r'fun u v : Fin %d =>' % n, st) and 'getD u.val 0).testBit v.val' in st
    return rows, n, k

def write_lean(step, st, rows, n, gates, out, outf, tree=True):
    target = sum(rows[u] << (u * n) for u in range(n))
    assert simulate(n, gates, out) == target, 'circuit is wrong'
    N = 0
    while (1 << N) < n * n: N += 1
    D = 0
    while (1 << D) < 2 * n + len(gates): D += 1
    ns = 'PEqualNP.Outside.' + step.replace('-', '_') + '_aux'
    nm = {'and': 'GateOp.and', 'or': 'GateOp.or', 'not': 'GateOp.not'}
    gl = ',\n  '.join('⟨%s, [%d, %d]⟩' % (nm[op], a, b) if op != 'not' else '⟨GateOp.not, [%d]⟩' % a for op, a, b in gates)
    mod = 'PromiseColTree' if tree else 'PromiseCol'
    L = []
    L.append('import Mathlib\nimport PEqualNP.Defs\nimport PEqualNP.Library.Helpers.%s\n' % mod)
    L.append('-- A gate list for the table.  The ones of the table are covered by all-ones blocks; the circuit ORs the rows')
    L.append('-- of a block, ORs its columns, ANDs the two and ORs the blocks, sharing ORs between blocks.  It is replayed')
    L.append('-- on the promise inputs by the helper %s.\n' % mod)
    L.append('namespace ' + ns + '\n')
    L.append('open PEqualNP.CircuitLowerBounds\n')
    L.append('set_option maxRecDepth 1000000 in\ndef wit : Circuit := ⟨[\n  ' + gl + '], %d⟩\n' % out)
    L.append('def okB (g : Gate) : Bool :=\n  (match g.op with\n   | GateOp.and => true\n   | GateOp.or => true\n   | GateOp.not => true\n   | _ => false) && decide (g.inputs.length ≤ 2)\n')
    L.append('set_option maxRecDepth 1000000 in\ntheorem fan : PEqualNP.MetaComplexity.FanInTwo wit := by\n  intro g hg\n  have h : wit.gates.all okB = true := by decide +kernel\n  have h2 := List.all_eq_true.mp h g hg\n  obtain ⟨op, ins⟩ := g\n  cases op <;> simp_all [okB]\n')
    L.append('end ' + ns + '\n')
    L.append('set_option maxRecDepth 1000000 in\ntheorem PEqualNP.Outside.' + step.replace('-', '_') + ' : ' + st + ' := by')
    L.append('  refine ⟨%s.wit, %s.fan, ?_, ?_⟩' % (ns, ns))
    L.append('  · decide +kernel')
    if tree:
        L.append('  · refine PEqualNP.Library.Helpers.PromiseColTree.represents_of_tcols (N := %d) (D := %d) ?_ _ _ ?_ ?_ ?_ ?_' % (N, D))
        L.append('    · norm_num')
        L.append('    · decide +kernel')
        L.append('    · decide +kernel')
        L.append('    · decide +kernel')
        L.append('    · decide +kernel')
    else:
        L.append('  · refine PEqualNP.Library.Helpers.PromiseCol.represents_of_pcols (N := %d) ?_ _ _ ?_ ?_ ?_' % N)
        L.append('    · norm_num')
        L.append('    · decide +kernel')
        L.append('    · decide +kernel')
        L.append('    · decide +kernel')
    open(outf, 'w').write('\n'.join(L) + '\n')

def main():
    step, stf, covf, outf = sys.argv[1:5]
    tries = int(sys.argv[5]) if len(sys.argv) > 5 else 20
    tree = not (len(sys.argv) > 6 and sys.argv[6] == 'list')
    st = open(stf).read().strip()
    rows, n, k = parse_statement(st)
    gates, out = best_circuit(n, load_blocks(covf), tries)
    print('gates', len(gates), 'bound', k)
    if len(gates) > k: print('too many gates'); sys.exit(2)
    write_lean(step, st, rows, n, gates, out, outf, tree)
    print('wrote', outf, os.path.getsize(outf), 'bytes')

if __name__ == '__main__':
    main()
