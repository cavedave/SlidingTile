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

## Inversion Distance — Extending Parity to a Lower Bound

Source: Ken'ichiro Takahashi (takaken). English description at:
https://michael.kim/blog/puzzle

### Inversions

Unravel the board into a single row (row-major, left-to-right top-to-bottom).
An **inversion** is a pair of tiles (i, j) where tile i appears before tile j
but i > j. The blank has no number and does not contribute to inversions.

The inversion count and the permutation sign are the same thing:
```
inversion_count mod 2  =  0 if sign = +1 (even permutation)
                        =  1 if sign = −1 (odd permutation)
```

So our `slideMove_flips_sign` theorem, restated in terms of inversions, is:
"each legal move changes the inversion count by an odd number."

### Why Horizontal Moves Change Inversions by 0

A horizontal move swaps the blank with a tile one position left or right in
row-major order. Since the blank has no value, no inversion is created or
destroyed. The inversion count is unchanged.

Therefore: **inversion_count mod 2 changes only with vertical moves.**
This is exactly the vertical parity constraint (V ≡ |Δrow_blank| mod 2).

### Why Vertical Moves Change Inversions by ±1 or ±3

A vertical move shifts a tile by 4 positions in row-major order (for a 4×4 board),
passing over exactly 3 other tiles. Each skipped tile either adds or removes one
inversion with the moved tile:

- All 3 skipped tiles smaller (or all larger): net ±3 inversions
- 2 smaller, 1 larger (or vice versa): net ±1 inversions

So a single vertical move fixes at most 3 inversions. This gives a lower bound:

```
vertical_moves_needed ≥ invcount / 3 + invcount % 3
```

(Fix 3 per move for the floor(invcount/3) chunk, then 1 per move for the remainder.)

### Horizontal Inversion Distance

Repeat with column-major ordering (top-to-bottom, left-to-right). Now:
- Vertical moves leave horizontal inversions unchanged
- Horizontal moves change horizontal inversions by ±1 or ±3

```
horizontal_moves_needed ≥ h_invcount / 3 + h_invcount % 3
```

### Combined Lower Bound

Since vertical and horizontal moves are mutually exclusive:

```
ID = (v_invcount / 3 + v_invcount % 3) + (h_invcount / 3 + h_invcount % 3)
```

The horizontal inversion count mod 2 = horizontal parity constraint
(H ≡ |Δcol_blank| mod 2). So Inversion Distance implicitly contains **both**
independent parity constraints from the row+col section above.

### Connection to the /3 Structure

The group-theoretic argument earlier showed: no mod-3 constraint on the
*permutation* exists (because transpositions have order 2 in S_n).

Inversion Distance is different: it is a mod-3-like constraint on the
*inversion count as an integer*, arising from the board geometry (a tile
passes over 3 others per vertical move). The /3 comes from the grid width, not
the group structure. On a 3-wide board, vertical moves pass over 2 tiles (±1
or ±2 inversions); on a 5-wide board, over 4 tiles. The formula generalises to
`invcount / (width−1) + invcount % (width−1)`.

### Lean Formalisation Sketch

```lean
lemma horizontal_move_inversion_stable (board : Board) (pos : Position)
    (h : isHorizontal pos (blankPosition board)) :
    inversions (slideMove board pos) = inversions board

lemma vertical_move_inversion_change (board : Board) (pos : Position)
    (h : isVertical pos (blankPosition board)) :
    let d := (inversions (slideMove board pos) : Int) - inversions board
    d = 1 ∨ d = -1 ∨ d = 3 ∨ d = -3
```

`slideMove_flips_sign` follows from `horizontal_move_inversion_stable` alone
(inversion count parity is stable under horizontal moves, changes under vertical).
The lower bound theorem is a corollary of `vertical_move_inversion_change`.

---

---

## Blank Routing Overhead and the Steiner Tree Lower Bound

### The Hidden Cost Manhattan Distance Ignores

Manhattan distance counts, for each tile, the minimum moves needed to reach its
goal — as if the blank is always conveniently adjacent and ready to make the next
move. In reality the blank is a physical piece that must travel to where it is needed.
This travel costs moves, and those moves are not counted by Manhattan distance.

Call this the **blank routing overhead**: moves spent repositioning the blank rather
than directly advancing any tile toward its goal.

### A Simple Example

Suppose three tiles each need one vertical move to reach their goal rows, and the
blank starts in the opposite corner. Manhattan distance says: 3 moves minimum.
But the blank must physically travel to tile 1's neighbourhood, make that move,
then travel to tile 2's neighbourhood, make that move, then travel to tile 3's
neighbourhood. The inter-tile travel is overhead.

In the best case the blank can route through all three neighbourhoods on a single
efficient path. In the worst case it must backtrack significantly. The minimum
blank travel to service all the tiles is the core of the Steiner tree problem.

### The Steiner Tree Formulation

Model the board as a graph:
- **Nodes**: the 16 positions
- **Edges**: adjacencies (same as the move graph)

For each tile that needs to move, the blank must visit at least one position
adjacent to that tile before the tile can be advanced. Call these the **waypoints**:
the positions the blank must pass through at some point during the solution.

The **Steiner tree problem** asks: what is the minimum-length connected path (or
tree of paths) in the board graph that starts at the blank's current position and
passes through all the waypoints?

```
blank_overhead ≥ cost(minimum Steiner tree connecting blank_start and all waypoints)
```

This is a genuine lower bound on extra blank moves beyond what Manhattan distance
already accounts for. It captures the gap between "the ideal where the blank is
always already in position" and "the reality where the blank must travel."

### Is the Steiner Tree a Lower Bound?

Yes. The blank must physically visit the neighbourhood of each tile to move it.
The Steiner tree is the minimum-cost connected path structure that does this.
Since the blank cannot shortcut or teleport:

```
blank_routing_overhead ≥ Steiner_tree_cost(blank_start, all waypoints)
```

The Steiner tree cost is a **lower bound on blank routing**, which is in turn a
lower bound on total overhead, which is a lower bound on the gap between Manhattan
distance and the optimal solution.

### Why It Is Hard to Compute Exactly

The Steiner tree problem is NP-hard, even on grid graphs. It cannot be used
directly as a per-node heuristic in IDA*.

We need a **lower bound on the Steiner tree** — something cheaper to compute that
is guaranteed to be ≤ Steiner tree ≤ blank routing overhead.

**Important**: the minimum spanning tree (MST) on the waypoints is an *upper* bound
on the Steiner tree (MST ≥ Steiner, because the Steiner tree can use intermediate
"Steiner points" not in the terminal set to reduce total edge length). MST is
*not* a lower bound.

**Computable lower bounds on the Steiner tree:**

| Bound | How | Tightness |
|-------|-----|-----------|
| `max_pairwise_distance / 2` | largest taxicab distance between any two waypoints, halved | very loose |
| `sum_of_nearest_neighbour_distances / 2` | for each waypoint, distance to nearest other waypoint, summed, halved | moderate |
| **1-tree relaxation** | fix blank_start; compute MST on all waypoints; add the shortest two edges from blank_start to that MST | tight (this is the Held-Karp lower bound for TSP) |

The 1-tree bound is the classical approach from the TSP literature. It gives a lower
bound on the optimal blank tour (visiting all waypoints and returning), and since
blank routing ≥ optimal tour ≥ 1-tree, it is a valid lower bound.

**In practice**: pattern databases implicitly compute blank routing exactly for
subsets of tiles. A 6-tile pattern database precomputes the exact minimum moves for
those 6 tiles to reach their goals including all blank repositioning within the
group. This subsumes the Steiner tree calculation for that subset, but requires
O(16! / 10!) ≈ 5 million stored values per table.

### Relationship to the Other Heuristics

Manhattan distance = minimum tile moves, ignoring blank routing.
Blank routing overhead = additional moves the blank must make between tile moves.
Optimal solution ≥ Manhattan distance + blank routing overhead.

Linear conflict already picks up some blank routing: when two tiles conflict in a
row, the blank must route around them, which costs at least 2 extra moves. The
Steiner tree bound generalises this to all tiles simultaneously.

Walking distance also captures some routing cost: by tracking row and column
occupancy, it implicitly accounts for cases where the blank must make multiple
passes through a boundary to sort tiles on each side.

The Steiner / blank routing perspective is most useful for understanding *why* the
gap between Manhattan distance and the optimal solution exists — and for designing
new heuristics that close that gap.

### Where This Fits in the Hierarchy

```
optimal solution length
  ≥  Manhattan  +  blank_routing_overhead
  ≥  Manhattan  +  Steiner_tree_cost(waypoints)       ← lower bound on routing
  ≥  Manhattan  +  1-tree_relaxation(waypoints)       ← lower bound on Steiner (computable)
  ≥  Manhattan  +  max_pairwise_dist(waypoints) / 2   ← cheapest approximation

  ≥  walking_distance           (captures routing via row/col occupancy)
  ≥  inversion_distance
  ≥  manhattan_distance
```

These rows are not strictly nested — walking distance and the Manhattan + Steiner
family are different approaches that may give different values on any specific board.
Walking distance and inversion distance implicitly capture blank routing cost via
occupancy structure, without framing it explicitly as a routing problem.

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
