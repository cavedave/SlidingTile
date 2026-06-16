import Mathlib.GroupTheory.Perm.Sign
import Sliding.Puzzle

/-!
# Parity of Slide Moves

## What is the sign of a permutation?

Every permutation can be written as a product of transpositions (swaps of two elements).
The **sign** (or parity) records whether you needed an even or odd number of swaps:
- sign = +1 means an even number of swaps (even permutation)
- sign = -1 means an odd number of swaps (odd permutation)

Mathlib provides `Equiv.Perm.sign : Equiv.Perm α →* ℤˣ`, a group homomorphism into
the multiplicative group `{1, -1}`. Key facts used here:
  `sign_refl  : sign (Equiv.refl α) = 1`         -- identity is even
  `sign_trans : sign (f.trans g)   = sign g * sign f`  -- composition multiplies signs
  `sign_swap  : x ≠ y → sign (swap x y) = -1`    -- every transposition is odd

## Why every slide move flips the sign

`slideMove` produces `board.trans (Equiv.swap t blank)` where `t` is the tile being
moved and `blank` is the blank label. This is the board composed with a transposition,
so by `sign_trans` and `sign_swap`:

  sign(board.trans (swap t blank)) = sign(swap t blank) * sign(board) = -1 * sign(board)

Each move multiplies the sign by -1, flipping it.

## Why this matters (the solvability invariant)

The solved board is `Equiv.refl`, which has sign +1. Starting there:
- after 0 moves : sign = +1, blank is 0 steps from goal → distance parity even
- after 1 move  : sign = -1, blank is 1 step from goal  → distance parity odd
- after k moves : sign = (-1)^k, blank is k steps from goal (same parity)

So the invariant `sign(board) = (-1)^(taxicabDist(blankPos, goalPos))` is preserved
by every slide move. Any board that violates it is unreachable from the solved state.

The classic example: swap tiles 14 and 15 on an otherwise-solved 15-puzzle.
That transposition makes the sign -1, but the blank stays at the goal (distance 0),
so (-1)^0 = +1 ≠ -1. Unreachable — Sam Loyd's famous $1000 challenge.
-/

namespace SlidingPuzzle

variable (cfg : PuzzleConfig)

/-- The blank tile label is the image of the blank *position* under the board.
    This is just the `Equiv` law `σ (σ⁻¹ x) = x`, stated in our vocabulary:
    wherever the blank is sitting, the board maps that position to `blankTile`. -/
lemma blankTile_eq_board_blankPosition (board : Equiv.Perm (Fin cfg.size)) :
    board (blankPosition cfg board) = blankTile cfg :=
  board.apply_symm_apply (blankTile cfg)

/-- If `pos` is not the blank's current position, then the tile at `pos` is not
    the blank label.  Proof: if it were, injectivity of `board` would force
    `pos = blankPosition`, contradicting the hypothesis. -/
lemma tile_at_pos_ne_blank (board : Equiv.Perm (Fin cfg.size)) (pos : Fin cfg.size)
    (h : pos ≠ blankPosition cfg board) :
    board pos ≠ blankTile cfg := by
  intro heq
  -- Rewrite `blankTile` as `board (blankPosition ...)` using the previous lemma
  rw [← blankTile_eq_board_blankPosition cfg board] at heq
  -- Now `heq : board pos = board (blankPosition ...)`,
  -- so injectivity gives `pos = blankPosition ...`
  exact absurd (board.injective heq) h

/-- **Every slide move flips the sign of the board permutation.**

    `slideMove` replaces `board` with `board.trans (swap (board pos) blankTile)`.
    This is `board` composed with a single transposition, so the sign is multiplied
    by -1 (using `Equiv.Perm.sign_trans` and `Equiv.Perm.sign_swap`).

    The hypothesis `pos ≠ blankPosition cfg board` ensures the two labels being
    swapped are distinct — if the moved tile *were* the blank, there would be no
    move at all.  Any non-reflexive adjacency (including `squareAdj`) guarantees
    this whenever `canMove = true`. -/
theorem slideMove_flips_sign (board : Equiv.Perm (Fin cfg.size)) (pos : Fin cfg.size)
    (h : pos ≠ blankPosition cfg board) :
    Equiv.Perm.sign (board.trans (Equiv.swap (board pos) (blankTile cfg))) =
    -Equiv.Perm.sign board := by
  -- The two labels swapped are distinct — required for sign_swap
  have h_ne : board pos ≠ blankTile cfg := tile_at_pos_ne_blank cfg board pos h
  -- sign(f.trans g) = sign(g) * sign(f)   [sign_trans reverses order]
  -- sign(swap x y)  = -1                   [sign_swap, needs x ≠ y]
  rw [Equiv.Perm.sign_trans, Equiv.Perm.sign_swap h_ne]
  -- Goal: -1 * sign board = -sign board
  simp

/-!
## Next steps (not yet proved)

The following corollary would complete the picture:

  **Invariant**: for every board reachable from `solvedBoard` by a sequence of
  slide moves, `Equiv.Perm.sign board = (-1)^(taxicabDist (blankPosition cfg board) goalPos)`.

  Proof sketch:
  - Base case: `solvedBoard` has sign 1, blank at goal, distance 0.  1 = (-1)^0. ✓
  - Inductive step: one `slideMove` flips both sides by ×(-1) — the sign flips
    (by `slideMove_flips_sign`) and the blank moves one step (distance ±1).

  Boards that violate the invariant — including any position reached by directly
  applying `Equiv.swap` to two non-blank tiles on a solved board — are unreachable
  from `solvedBoard`, and therefore unsolvable.
-/

end SlidingPuzzle
