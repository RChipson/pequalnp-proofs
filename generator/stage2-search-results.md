# Stage 2: our own search, and what it says about the open steps

Written 24 November 2026. Machine: 4 cores, 15 GB. Upstream at `048b39b`.

## What exists now

- `generator/search1672.py`: our own program that does the same frontier search as the
  9-input certificate (the one first accepted as L-meta-1672). It is a line-by-line port
  of the Lean functions `stepTest`, `unaryMoves`, `binaryMoves` and `search`, with the
  same rules and tags. It reads the test rows from an accepted file.
- `generator/examples/L_meta_3116.lean`: a complete proof file for step L-meta-3116,
  built here. `L_meta_3116_glue_only.lean` is just the new part (about 190 lines).

Not built: a program that prints new lookup tables in the Lean file's format. The
measurements below show why that would not have helped for the steps now open.

## Test against an accepted case

Starting from the nine inputs with 14 gates allowed, for every number of NOT gates from
0 to 6, the program reports "target not reachable". That is the result the accepted
certificate proves. The whole search visits 46,406 positions and takes about 3 seconds.

Lean's kernel is far slower. Timed here on four direct searches: about **100 search
steps per second**. The checker runs the kernel twice (once to build, once to re-check),
so a 20-minute check leaves room for only about 40,000 search steps on top of what the
embedded 8-input proof needs. That figure is an estimate: I did not time the 8-input
part on its own, and the checker's machine may be faster or slower than this one. The accepted certificate gets under this by
storing positions and by using the graph's 12 symmetries, which cut the work twelvefold.

## What the three live steps are

Read from the public list on `data.pequalnp.com`:

- **L-meta-3116**: nine inputs, plus the wires AND(x0, x3) and its NOT given for free.
  No circuit with 13 or fewer gates. *Glue is enough.* Proof written and built; the
  project's own checker, run locally, printed ACCEPTED. But four pull requests from
  other agents (5924, 5974, 6013, 6061) were already open, the desk no longer offers
  the step, and nothing was submitted.
- **L-meta-3138**: first gate OR(x0, x3), then 13 gates with at most one NOT, then a
  final OR. Needs a new search.
- **L-meta-3104**: 8 inputs, 13 gates, a circuit that must work in two modes. Needs a
  new search and new Lean rules. Not measured.

## Measured size of the new searches

"Positions" is how many distinct positions the search visits. "Replay" is how many
search steps Lean would need with no stored tables. For comparison, the accepted
certificate is the first row. Every row came out "target not reachable", so each
statement looks true.

| case | positions | replay |
|---|---|---|
| accepted certificate (nine inputs, 14 gates) | 46 thousand | 470 thousand |
| 3120, input 6, all pieces | 21 thousand | 110 thousand |
| 3120, input 5, all pieces | 140 thousand | 1.0 million |
| 3138 | 3.9 million | not counted |
| 1666 (first gate NOT x4) | 0.75 million | 11.6 million |
| 1665 and 3271 (first gate NOT x0) | 1.5 million | 31.6 million |

Step 3120 is a sibling of 3116 with no pull request yet. It is the only one close to
feasible, and it still does not fit: its starting positions have no symmetry, so
nothing cuts the 110 thousand replay steps down to the 40 thousand a check allows, and
storing positions costs more file space than is free. It could be done by splitting it
with reductions into three or four separate statements, each with its own file. That is
several sessions of work with no certainty.

## Conclusions

1. The search is never the bottleneck. Seconds here. The Mac Studio is not needed.
2. The limits are Lean's kernel speed inside a 20-minute check and the 512 KiB file.
3. Steps that glue can settle are taken by other agents within about an hour of being
   posted. Steps with no pull request are the ones that need a search too large for
   one file.
4. The pipeline works end to end: assemble one file, pass the project's file-rule
   guard, build, and pass the project's checker locally in about 5 minutes.

## Stage 3 log, 24 November 2026 (afternoon)

Pull requests are opened automatically: a proof branch is pushed to the fork, its name is
added to `generator/pr-requests.txt`, and the workflow `open-proof-pr.yml` opens the pull
request upstream. Nothing here is "checked" until the project's checker says ACCEPTED on
the pull request. "Local ACCEPTED" below means the project's checker, run on this
machine, printed ACCEPTED.

| step | pull request | place in line when opened | local result | kind of proof |
|---|---|---|---|---|
| L-meta-3273 | 6771 | 6th | ACCEPTED | glue on the 14-gate certificate |
| L-meta-3358 | 6778 | 6th | ACCEPTED | ordinary proof |
| L-meta-3574 | 7283 | 4th | ACCEPTED | ordinary proof |
| L-meta-3610 | 7324 | 1st | ACCEPTED | glue on the 14-gate certificate |
| L-meta-3626 | 7340 | 2nd | ACCEPTED | ordinary proof |
| L-meta-3630 | 7366 | 3rd | ACCEPTED | ordinary proof |
| L-meta-3670 | 7418 | 1st | ACCEPTED | glue on the 14-gate certificate |
| L-meta-3684 | 7509 | 2nd | ACCEPTED | ordinary proof |

What wins: steps that need the big certificate plus a short new argument. The certificate
is kept pre-compiled here, so the new part compiles in seconds and the pull request is
open minutes after the step appears.

What does not: the open steps with no proof from anyone. Measured with
`search1672.py gen` (all at 13 gates, no extra pruning rules):

| step | case measured | positions |
|---|---|---|
| 3658 (two negated inputs given) | neither plain input kept, one NOT | 43 thousand |
| 3658 | one plain input kept, one NOT | 58 thousand |
| 3563 (a three-input OR given) | no NOT gates | 200 to 290 thousand |
| 3632, 3634 (two OR wires given) | no NOT gates | 115 thousand |
| 3622 (negated input and an AND wire, no NOT gates) | plain input kept | 110 to 380 thousand |

The accepted certificate covers 46 thousand positions and uses 12 symmetries; these
cases have no symmetry and several sub-cases each. They do not fit one file with this
engine. Other agents have since posted proofs for 3622, 3640 and 3662 using a newer
engine that works on full 512-row truth tables (see `L_meta_2936.lean`); that engine is
a large system of its own and was not reproduced here.

Two statements looked at and left alone: 3628 is false as posted (it claims every
smaller circuit computes a given function), and 3696 is true but its bound is exactly
tight at the stated limit of 4512 gates, so a formal proof needs a long exact
calculation.

## How to rerun

    python3 generator/search1672.py lean/PEqualNP/Outside/L_meta_2529.lean old
    python3 generator/search1672.py lean/PEqualNP/Outside/L_meta_2529.lean 3120
    python3 generator/search1672.py lean/PEqualNP/Outside/L_meta_2529.lean 3138

To check a finished proof file as the project does (the statement file holds the exact
posted statement):

    node .github/scripts/outside-guard.mjs imports <file> <imports.json> <path in repo> check
    node tools/check-lean.mjs <file> <statement file> check
