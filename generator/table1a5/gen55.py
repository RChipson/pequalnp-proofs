#!/usr/bin/env python3
"""Lower bound for a 5-by-5 Table 1a entry: port of the accepted proof L-meta-9214 (same file
for every mask; only the mask and its lists of one and zero positions change).
Usage: gen55.py <step id> <mask> <statement file> <out file>"""
import re, subprocess, sys
step, M, stmt_file, out = sys.argv[1], int(sys.argv[2]), sys.argv[3], sys.argv[4]
ident = step.replace('-', '_')
src = subprocess.run(['git', '-C', '/home/user/pequalnp-proofs', 'show',
                      'upstream/main:lean/PEqualNP/Outside/L_meta_9214.lean'],
                     capture_output=True, text=True, check=True).stdout
M0 = 7579446
ones0 = [p for p in range(25) if (M0 >> p) & 1]; zeros0 = [p for p in range(25) if not (M0 >> p) & 1]
assert f'def OO : List ℕ := {ones0}' in src and f'def ZZ : List ℕ := {zeros0}' in src, 'template lists differ'
ones = [p for p in range(25) if (M >> p) & 1]; zeros = [p for p in range(25) if not (M >> p) & 1]
src = src.replace(f'def MM : ℕ := {M0}', f'def MM : ℕ := {M}')
src = src.replace(f'def OO : List ℕ := {ones0}', f'def OO : List ℕ := {ones}')
src = src.replace(f'def ZZ : List ℕ := {zeros0}', f'def ZZ : List ℕ := {zeros}')
i = src.index('theorem PEqualNP.Outside.L_meta_9214 :')
j = src.index(':= by', i)
stmt = open(stmt_file).read().strip()
src = src[:i] + 'theorem PEqualNP.Outside.L_meta_9214 : ' + stmt + ' ' + src[j:]
assert str(M0) not in src, 'old mask left somewhere'
src = src.replace('L_meta_9214', ident)
open(out, 'w').write(src)
print('wrote', out, len(src.encode()), 'bytes; ones', len(ones))
