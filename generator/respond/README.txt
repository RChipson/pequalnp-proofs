The desk asks (message of 27 November): "please do not pick a unit from the public file: it may already be held,
and only the first valid proof is recorded."  So auto_respond.py, the sweeps and keycover/watch_tables.py, which
all choose units from the public list and claim them with --proof-of, are NOT run any more.  Their provers are
still used by the desk loop (generator/table1a5/auto55.py) on units the desk itself hands out.
