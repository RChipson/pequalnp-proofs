#!/usr/bin/env python3
"""Last resort for a unit the desk handed us and no special rule fits: run the responder's generic provers on
it (a gate list spelled out in the notes; a small graph to find a circuit for, with or without NOT gates; a
floor by sample search or certificate).  Prints the path of a proof that compiles.
  python3 generator/respond/try_unit.py <step id>      exit 0: proof ready; 3: nothing found"""
import json, os, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import auto_respond as A
step = sys.argv[1]
d = json.load(open(f'/home/user/pequalnp-proofs/.pnp/{step}.json')); g = d['gap']; stmt = g['statement'].strip()
for name, h in A.HANDLERS:
    try: out = h(step, g, stmt)
    except Exception as e: out = None
    if out: print(name); print(out); sys.exit(0)
sys.exit(3)
