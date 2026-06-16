# Sliding Puzzle — Roadmap

## 1. Finish the current proofs

The `Parity.lean` file has the key building block (`slideMove_flips_sign`) and a
clear proof sketch in its closing comment. What remains:

- **Inductive invariant** — prove that every board reachable from `solvedBoard`
  by a sequence of `slideMove` calls satisfies
  `sign(board) = (-1)^taxicabDist(blank, goal)`.
  Requires: a notion of "reachable" (e.g. a `List Position` path) and induction
  on it using `slideMove_flips_sign` for the step.

- **Unsolvability corollary** — prove that any board violating the invariant is
  unreachable.  This is the formal Lean statement of what `isSolvable` checks
  at runtime.

- **Blank-distance bookkeeping** — one slide move changes `taxicabDist` by
  exactly ±1.  This needs its own small lemma (grid geometry, not parity) to
  complete the inductive step.

## 2. Understand all the steps

Before writing up, make sure each proof step is legible:

- Re-read `Parity.lean` comments; extend them where anything is unclear.
- Annotate `slideMove_flips_sign` with the full equational chain it performs.
- Trace through `isSolvable` on paper for the Sam Loyd board and the "15 to 1"
  toy puzzle to confirm the numbers.
- Revisit Aaron Archer's paper (`15-puzzle.pdf`) to check our invariant matches
  his Theorem 2 statement exactly.

## 3. Write up tutorial and readme

- **README.md** — project overview, how to build and run (`lake build`,
  `lake exe sliding`, `lake exe sliding4x4`), what each file contains.
- **Tutorial** — walk through the key design decisions:
  - Why `Equiv.Perm` over `List` or `Vector`
  - What `blankTile`, `blankPosition`, `slideMove` do
  - How the parity invariant emerges
  - How `isSolvable` uses it as a runtime check
- The `writeup.md` quote from the American Journal of Mathematics (1879) is
  a good opener.

## 4. Share on GitHub and elsewhere

- Clean up any `sorry`-free status (all proofs should be complete).
- Push to GitHub; write a short post for Lean/Mathlib community (Zulip, Reddit
  r/lean4, etc.).
- Consider submitting the parity proof as a Mathlib-style example or blog post.

---

## Near-term technical work

### 5.1 — Sam Loyd's puzzle is solvable on a non-bipartite board (concrete result)

The hook: the same board that is *provably impossible* on a flat grid becomes
*provably solvable* when the graph is non-bipartite.

**Important caveat**: a simple 4×4 cylinder (wrapping 4 columns into a loop)
is STILL bipartite — a 4-cell loop is an even cycle, and adding even cycles
doesn't break bipartiteness. Sam Loyd's board is still unsolvable on it.

To actually break the parity invariant you need an **odd cycle**. Options:
- A **3-wide grid** cylinder (wrapping 3 columns creates 3-cycles — odd)
- A 5-wide grid cylinder
- A Möbius-like twisted connection (connect opposite edges with a shift)

This follows from Wilson's theorem (cited at the end of Archer's paper):
for any connected graph without cut vertices, all permutations are reachable
iff the graph is non-bipartite; only even permutations are reachable
iff it is bipartite.

Steps:
- Choose a non-bipartite variant (e.g. a 3×6 sliding puzzle, or a 4×4 with
  a twist).
- Add the appropriate adjacency function to `Grid.lean`.
- Find a concrete solution path for Sam Loyd's board under the new adjacency
  (BFS in `#eval`).
- State and prove a theorem: a `List Position` of moves takes `samLoydBoard`
  to `solvedBoard`. Proof: `decide` or `native_decide` on the path.

This does NOT depend on the Unsolvability Corollary — it only needs
`slideMove` and the new adjacency function.

### 5.2 — All boards are reachable on a cylinder (general theorem, next article)

The general claim: unlike the flat grid, the cylinder puzzle has no unreachable
states.

Proof strategy (different from the square — these are siblings, not parent/child):
- Prove a **loop lemma**: there exists a sequence of cylinder moves that starts
  and ends with the blank at the goal position but performs a net *odd*
  permutation of the tiles (the blank travels around the cylinder).
- Combined with `slideMove_flips_sign` (already proved), this means both even
  and odd permutations are reachable with the blank at goal — so the parity
  invariant that restricts the flat grid places *no* restriction on the cylinder.
- Conclude: every board is reachable.

This proof uses `slideMove_flips_sign` but does NOT use the square
Unsolvability Corollary. The two results have the same parent but are
independent of each other.

### Formal proof of solvability (converse)
- The runtime checker `isSolvable` rejects boards that violate the invariant,
  but does not yet prove they are solvable if they pass.
- The full proof (invariant is both necessary *and* sufficient) is harder;
  see Archer's paper for the completeness argument.

---

## Geometric lower bounds for IDA* solvers

See `parity_pruning.md` for a full treatment with references.

The hierarchy of lower bounds (weakest to strongest):

| Bound | Key idea | Formalizable? |
|-------|----------|---------------|
| Manhattan distance | individual tile distances | yes, straightforward |
| + Parity (sign) | each move = transposition, sign flips | ✓ done in `Parity.lean` |
| + Row parity + col parity | 2 independent mod-2 constraints | follows from `Parity.lean` |
| + Linear conflict | pairs in same row/col that must pass each other → +2 per pair | yes |
| Inversion distance | vertical move passes over 3 tiles → fixes ≤ 3 inversions; lb = inv/3 + inv%3 | yes |
| Walking distance | exact min row-moves + col-moves from occupancy tables | yes (with tables) |
| Pattern databases | precomputed exact costs for tile subsets | harder, needs lookup |

**Inversion Distance** is the next natural target after parity:
- `horizontal_move_inversion_stable` — horizontal moves fix 0 inversions
- `vertical_move_inversion_change` — vertical moves fix 1 or 3 inversions
- Lower bound theorem follows as a corollary of these two lemmas

### Other geometric constraints (to investigate)

**Symmetry reduction**: the 4×4 grid has 8-fold dihedral symmetry (4 rotations × 2
reflections). Any board is equivalent to its most "canonical" symmetric form.
Searching canonical forms only gives up to 8× fewer states — not a lower bound
improvement but a direct search speedup.

**Cycle costs**: if tiles A, B, C form a rotation cycle (A needs B's spot, B needs
C's, C needs A's), the minimum moves to resolve it grows with cycle length. Linear
conflict catches 2-cycles; longer cycles may give a stronger lower bound.
Potentially formalizable as a generalisation of linear conflict.

**Blank routing overhead**: the blank must travel to the neighbourhood of each tile
to move it. The minimum extra blank travel not directly advancing any tile toward
its goal is a lower bound component — related to a Steiner tree on the board graph.
Hard to compute exactly (NP-hard in general) but approximable.

**Subsquare constraints**: the 4×4 grid contains 9 overlapping 2×2 subsquares.
The parity of tiles within each subsquare changes with boundary crossings. These
6 boundary-crossing parities (3 row + 3 col) were discussed in `parity_pruning.md`;
the subsquare view shows how they decompose spatially.

---

## Longer-term / exploratory

| Idea | Notes |
|------|-------|
| **Hex grid tiles** | Six-neighbour adjacency; `hexAdj` in `Grid.lean`. |
| **Triangular tiles** | Mixed three/four-neighbour cells. |
| **Gourd / irregular shapes** | Gardiner's "escaping donkey" style puzzles where tile shapes are non-square. |
| **Optimal solvers** | Formalise that A\* or IDA\* finds shortest paths; compare with the literature (`2302.02985`). |
| **Other related puzzles** | Tower of Hanoi, Rubik's cube — same Lean machinery (permutation groups, reachability, parity). |
