#!/usr/bin/env python3
"""Exact search for a monotone (AND/OR, fan-in two) circuit that represents an n by m bipartite graph on the
one-a-side promise inputs (wires 0..n-1 left, n..n+m-1 right), with exactly G gates.
  python3 promise_mono.py <kind> <n> <G> <seconds> [seed]
kinds: stair (u+v <= n-1), crown (u != v), crowns2 (two disjoint 4 by 4 crowns, n = 8)
       sep (not a graph: n inputs, separate one input on from two inputs on; the crown after the n ORs x_u or y_u)"""
import sys
from msynth import search, check
kind, n, G, secs = sys.argv[1], int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4])
seed = int(sys.argv[5]) if len(sys.argv) > 5 else 0
if kind == 'sep':
    rows = [(1 << i, 0) for i in range(n)] + [((1 << i) | (1 << j), 1) for i in range(n) for j in range(i)]
    nin = n
else:
    f = {'stair': lambda u, v: u + v <= n - 1, 'crown': lambda u, v: u != v, 'crowns2': lambda u, v: u // 4 == v // 4 and u % 4 != v % 4}[kind]
    rows = [((1 << u) | (1 << (n + v)), int(f(u, v))) for u in range(n) for v in range(n)]
    nin = 2 * n
R = len(rows)
incols = [sum(1 << r for r in range(R) if rows[r][0] >> i & 1) for i in range(nin)]
target = sum(1 << r for r in range(R) if rows[r][1])
res = search(nin, incols, R, [target], G, 'andor', secs, seed)
if isinstance(res, tuple):
    gates, outs = res
    assert check(nin, incols, R, [target], gates, outs)
    print(kind, n, G, 'FOUND', gates, outs)
else:
    print(kind, n, G, res)
