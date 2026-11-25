#!/usr/bin/env python3
"""Write the Lean proof file of one Table 2 step (8 vertices, AND/OR/NOT gates of fan-in two,
bound = edges + cover number - 1).

Usage: gen_table2.py <step id, e.g. L-meta-8517> <statement file> <out file> [edges, e.g. 0-1 0-2 ...]

The edges are read from the statement; when given on the command line they must agree with it.
The proof is a table of all restrictions of the edge function (inputs fixed to 0 or 1), each with
the bound |A| + |E| + cover - 1, and one kernel check per row: a search over the first gates of a
circuit, cut by the bounds of the rows below it. Before the file is written the same search is
run here in Python (t2search.py); no file is written if a row does not close. Heavy rows are cut
into pieces (T2_THRESH, default 5000 search steps a piece) so that no single kernel check needs
much memory. Files t2lib.py, t2search.py, t2final.py, t2_core_a.txt and t2_core_b.txt (next to
this script) hold the data layer, the Python copy of the search and the fixed Lean text.
"""
import os, sys
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import t2lib, t2final

def main():
    step, stmt_file, out = sys.argv[1], sys.argv[2], sys.argv[3]
    ident = step.replace('-', '_')
    stmt = open(stmt_file).read().strip()
    body, bound, E = t2final.parse_statement(stmt)
    if len(sys.argv) > 4:
        E2 = [tuple(int(v) for v in e.split('-')) for e in sys.argv[4:]]
        assert E2 == E, 'the edges given do not match the statement'
    root, tab = t2lib.build_table(E)
    data, N, i0 = t2lib.table_data(tab, root)
    if tab[i0][1] != bound:
        sys.exit(f'the table gives {tab[i0][1]} for this graph, the statement says {bound}: no file written')
    pi = [t2lib.pack(x) for x in t2lib.XT]
    ns = f'PEqualNP.Outside.{ident}'
    thresh = int(os.environ.get('T2_THRESH', '5000'))
    tail, _, _, total, biggest = t2final.tail(stmt, tab, thresh, log=lambda m: print(m, file=sys.stderr))
    parts = []
    parts.append('import Mathlib\nimport PEqualNP.Defs\n')
    parts.append('-- Lower bound for the edge function of one eight-vertex graph, AND/OR/NOT gates of fan-in two.\n'
                 '-- Method: a table of all restrictions of the function (inputs fixed to 0 or 1), each with its\n'
                 '-- bound; each row is checked by a kernel search over the first gates of a circuit, cut by the\n'
                 '-- bounds of the rows that fix more inputs (a gate that collapses under a restriction is paid for\n'
                 '-- by the restricted function). The words are truth tables over 129 blocks of 256 rows.\n'
                 '-- The coverage bookkeeping (addCov, takeOne, takeTwo, dropped) and the reading of a circuit as\n'
                 '-- words on its wires follow the accepted proof L-meta-1007 of this repository, moved from\n'
                 '-- bit vectors to natural numbers; the rest of the file is new.\n')
    parts.append(f'namespace {ns}\n')
    parts.append(''.join(f'def {k} : Nat := {hex(v)}\n\n' for k, v in t2lib.CONSTS.items()))
    parts.append(open(os.path.join(HERE, 't2_core_a.txt')).read())
    parts.append('def PIl : List Nat := [' + ',\n  '.join(hex(x) for x in pi) + ']\n')
    parts.append(data)
    parts.append(open(os.path.join(HERE, 't2_core_b.txt')).read())
    parts.append(tail)
    parts.append(f'end {ns}\n')
    parts.append(f'theorem {ns} : {stmt} :=\n  {ns}.main\n')
    src = '\n'.join(parts)
    assert '"' not in src
    assert len(src.encode()) <= 524288, f'file too large: {len(src.encode())} bytes'
    open(out, 'w').write(src)
    print(f'wrote {out}: {N} table rows, root row {i0}, bound {bound}, {len(src.encode())} bytes, '
          f'search cost {total} (largest piece {biggest})')

if __name__ == '__main__':
    main()
