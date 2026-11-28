#!/usr/bin/env python3
"""The responder's generic provers (a gate list spelled out in the notes; a small graph to find a circuit for; a
floor by sample search or certificate) run on a row as the PUBLIC list shows it, before the row is taken.
Nothing is asked of the desk.  Prints the prover's name and the path of a proof that compiles.
  python3 generator/respond/try_public.py <step id> <file with the list's entry as JSON>     exit 0: proof ready; 3: nothing found"""
import json, os, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import auto_respond as A
step = sys.argv[1]
g = json.load(open(sys.argv[2])); stmt = g['statement'].strip()
for name, h in A.HANDLERS:
    try: out = h(step, g, stmt)
    except Exception as e: out = None
    if out: print(name); print(out); sys.exit(0)
sys.exit(3)
