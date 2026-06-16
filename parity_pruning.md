# Parity Pruning in Sliding Tile Puzzle Solvers

## Overview

IDA* (Iterative Deepening A*) solves sliding tile puzzles optimally by repeatedly
running a depth-first search with an increasing threshold `t`, pruning any node where:

```
g (moves so far) + h (heuristic lower bound) > t
```

Parity constraints give two kinds of savings:

1. **Iteration skipping** — entire IDA* depths can be skipped
2. **Node-level pruning** — nodes at exactly the threshold can be pruned

---

## The Hierarchy of Lower Bounds

Both Manhattan distance and walking distance are *lower bounds* on the optimal solution.
Walking distance is tighter:

```
walking_distance ≥ manhattan_distance ≥ 0
                                         ↑ optimal solution is somewhere here
```

### 1. Manhattan Distance
Sum of taxicab distances of each tile from its goal position. Fast to compute.
Every tile move changes the sum by ±1, so it's a valid lower bound.

### 2. Walking Distance
Tracks the minimum row-moves and column-moves needed separately, based on the
occupancy pattern of tiles in each row and column (not just individual distances).
Much stronger than Manhattan but requires precomputed lookup tables.

**Reference**: Ken'ichiro Takahashi, walking distance tables for 15-puzzle solvers
(widely cited in competitive puzzle solving, circa 2000s).

### 3. Linear Conflict
If two tiles are in their goal row/column but in the wrong relative order, they
must pass through each other — at least 2 extra moves required per conflict pair.
Adds multiples of 2 on top of Manhattan distance. Independent of parity.

**Reference**: Hansson, Mayer, Yung (1992). "Generating Admissible Heuristics by
Criticizing Solutions to Relaxed Models." Also in: Korf & Taylor (1996),
"Finding Optimal Solutions to the Twenty-Four Puzzle."

### 4. Pattern Databases
Precompute exact move counts for subsets of tiles. The (6-6-3) partition is standard
for 15-puzzle. Implicitly captures all modular constraints for those tiles.
Strongest practical lower bound.

**Reference**: Culberson & Schaeffer (1998). "Pattern Databases."
*Computational Intelligence* 14(3): 318–334.

---

## Parity Constraints

### Total Parity (1 constraint)

Each slide move is algebraically a transposition — it composes the board permutation
with `Equiv.swap (board pos) blankTile`. Transpositions have sign −1, so:

```
sign(board after k moves) = (−1)^k × sign(initial board)
```

The invariant is: `sign(board) = (−1)^taxicabDist(blankPos, goal)`

This is preserved by every legal move. Any board violating it is unreachable.
For a solvable board, the optimal solution length must have a specific parity:

```
optimal_moves ≡ taxicabDist(blank, goal)  (mod 2)
```

**References**:
- Aaron F. Archer (1999). "A Modern Treatment of the 15 Puzzle."
  *American Mathematical Monthly* 106(9): 793–799.
  — The key observation: "Each move causes a transposition of the 16 blocks."
- W. W. Johnson (1879). "Note on the '15' puzzle."
  *American Journal of Mathematics* 2: 397–399.
- R. M. Wilson (1974). "Graph puzzles, homotopy, and the alternating group."
  *Journal of Combinatorial Theory (Series B)* 16: 86–96.
  — General result: bipartite graph ↔ only even permutations reachable.
    Non-bipartite ↔ all permutations reachable.

**Formal proof in this project**: `Sliding/Parity.lean`, theorem `slideMove_flips_sign`.

### Why No Mod-3 (or Odd-Prime) Constraint Exists

A mod-3 constraint would require a group homomorphism from the reachable permutations
to Z/3Z. Each legal move is a transposition, which has order 2. Z/3Z has no element of
order 2. So the only homomorphism S_n → Z/3Z is trivial.

More generally: the sign (Z/2Z) is the *only* nontrivial homomorphism from S_n to
any finite cyclic group. This follows from A_n being the unique index-2 subgroup of
S_n, and A_n being simple for n ≥ 5.

Richer invariants (e.g. Rubik's cube mod-3 corner twist) arise only when generators
have order > 2, which transpositions do not.

### Row Parity + Column Parity (2 independent constraints)

Every board move is either horizontal (H) or vertical (V). The blank's net displacement
decomposes:

```
H ≡ |Δcol_blank|  (mod 2)      — horizontal moves have fixed parity
V ≡ |Δrow_blank|  (mod 2)      — vertical moves have fixed parity
```

These are **two independent mod-2 constraints**. The total parity constraint
(sign invariant) is their sum: H + V ≡ taxicabDist (mod 2). The split gives
strictly more information.

In IDA*: a node at depth g with g_H horizontal moves and g_V vertical moves can
be pruned if the remaining heuristic h cannot be split into (h_H, h_V) satisfying
both parities simultaneously.

### Boundary Crossing Parity (up to 6 independent constraints)

The 4×4 grid has 3 horizontal boundaries (between rows 0-1, 1-2, 2-3) and
3 vertical boundaries (between columns 0-1, 1-2, 2-3). For each boundary, the
number of times the blank crosses it has fixed parity (determined by whether
the boundary lies between blank_start and blank_goal).

This gives up to **6 independent mod-2 constraints**, one per boundary.
These subsume the row/column parity constraints above.

The walking distance lower bound is the full (non-modular) version of this idea:
instead of just the parity of boundary crossings, it computes the exact minimum.

**Note on diagonals**: Diagonal quantities (r+c) mod 2 and (r−c) mod 2 both change
with every move and are always equal. They give no constraint independent of the
total parity.

**Note on corners**: Corner positions have no special constraint beyond chessboard
parity — they reduce to the same total-move parity.

---

## How Parity Pruning Helps IDA*

### Saving 1: Iteration Skipping (the large saving)

IDA* runs searches at increasing thresholds: 10, 11, 12, 13, ...

If parity says the solution length must be even, skip all odd thresholds:

```
Without parity:  search at depths 10, 11, 12, 13, 14 ...
With parity:     search at depths 10, 12, 14 ...
```

Each IDA* iteration is roughly 2–3× more expensive than the previous one (branching
factor ≈ 2–3 for 15-puzzle). Skipping one full depth saves roughly one iteration's
worth of work — a 30–50% reduction in total nodes searched.

### Saving 2: Node-Level Pruning (at the threshold boundary)

During the depth-t search, parity prunes a node when:

```
g + h = t   (exactly at threshold)
AND h has the wrong parity for the remaining moves
→ effective h = h + 1, effective f = t + 1 > t → PRUNE
```

Example (threshold t = 14, even solution required):

| g  | h | f  | Remaining parity needed | h parity | Action        |
|----|---|----|------------------------|----------|---------------|
| 10 | 4 | 14 | even                   | even ✓   | proceed       |
| 11 | 3 | 14 | odd                    | odd ✓    | proceed       |
| 10 | 3 | 13 | even                   | odd ✗    | eff. f=14, proceed |
| 11 | 2 | 13 | odd                    | even ✗   | eff. f=14, proceed |
| 12 | 3 | 15 | —                      | —        | standard prune |

The pruning triggers when g + h = t (not g + h < t), so it applies only to nodes
right at the frontier. However, in IDA*, a large fraction of explored nodes sit at
exactly f = t, so this is a meaningful saving.

With row+col parity (2 constraints), pruning applies whenever either the horizontal
or vertical heuristic has wrong parity — roughly doubling the node-level pruning
compared to total-parity alone.

---

## Summary Table

| Constraint              | Type         | Pruning effect            | Cost to compute |
|-------------------------|--------------|---------------------------|-----------------|
| Manhattan distance      | lower bound  | baseline                  | O(n)            |
| Total parity (sign)     | mod 2        | skip ~half of IDA* depths | O(1)            |
| Row parity + col parity | 2× mod 2     | more node pruning         | O(1)            |
| Boundary parity         | 6× mod 2     | uncertain; overlaps WD    | O(1) with tables|
| Linear conflict         | lower bound  | +2 per conflict           | O(n)            |
| Walking distance        | lower bound  | strongest single bound    | O(1) with tables|
| Pattern databases       | lower bound  | subsumes all of the above | O(1) with tables|

---

## Further Reading

- Korf, R. E. (1985). "Depth-first iterative-deepening: An optimal admissible tree
  search." *Artificial Intelligence* 27(1): 97–109. — Original IDA* paper.

- Korf, R. E. & Taylor, L. A. (1996). "Finding Optimal Solutions to the Twenty-Four
  Puzzle." *AAAI*, pp. 1202–1207. — Pattern databases, linear conflict.

- Culberson, J. & Schaeffer, J. (1998). "Pattern Databases."
  *Computational Intelligence* 14(3): 318–334.

- Felner, A., Korf, R. E. & Hanan, S. (2004). "Additive Pattern Database Heuristics."
  *Journal of Artificial Intelligence Research* 22: 279–318.

- Wilson, R. M. (1974). "Graph puzzles, homotopy, and the alternating group."
  *Journal of Combinatorial Theory (Series B)* 16: 86–96.

- Archer, A. F. (1999). "A Modern Treatment of the 15 Puzzle."
  *American Mathematical Monthly* 106(9): 793–799.
