import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Data.Fintype.Card

/-!
# Generic Sliding Puzzle

A sliding puzzle on any finite set of positions, parametrized by:
- `size : Nat`  — number of cells (must be positive)
- `adj`         — which cells are neighbours

The blank tile is always the highest-labelled tile (`Fin.last`).
A board is an `Equiv.Perm (Fin size)`: `board p` gives the tile at position `p`.

This module is geometry-independent. Square grids, cylinder grids, hex grids, etc.
are all instances — they differ only in their `adj` function.
-/

structure PuzzleConfig where
  size     : Nat
  size_pos : 0 < size
  adj      : Fin size → Fin size → Bool

namespace SlidingPuzzle

variable (cfg : PuzzleConfig)

/-- The blank tile label: the highest element of `Fin cfg.size`, i.e. `cfg.size - 1`.
    We construct it directly using `cfg.size_pos` to prove the bound. -/
def blankTile : Fin cfg.size :=
  ⟨cfg.size - 1, Nat.sub_lt cfg.size_pos Nat.one_pos⟩

/-- The solved board: tile `i` sits at position `i` (identity permutation). -/
def solvedBoard : Equiv.Perm (Fin cfg.size) := Equiv.refl _

/-- The position currently occupied by the blank tile.
    Uses the inverse permutation: given the blank label, find where it sits. -/
def blankPosition (board : Equiv.Perm (Fin cfg.size)) : Fin cfg.size :=
  board.symm (blankTile cfg)

/-- Can the tile at `pos` slide into the blank?
    Yes iff `pos` is a neighbour of the blank's current position. -/
def canMove (board : Equiv.Perm (Fin cfg.size)) (pos : Fin cfg.size) : Bool :=
  cfg.adj pos (blankPosition cfg board)

/-- Slide the tile at `pos` into the blank. Returns `none` if the move is illegal.
    Implemented as a label swap: the tile at `pos` and the blank exchange labels. -/
def slideMove (board : Equiv.Perm (Fin cfg.size)) (pos : Fin cfg.size)
    : Option (Equiv.Perm (Fin cfg.size)) :=
  if canMove cfg board pos then
    some (board.trans (Equiv.swap (board pos) (blankTile cfg)))
  else
    none

/-- Is every tile in its home position? -/
def isSolved (board : Equiv.Perm (Fin cfg.size)) : Bool :=
  decide (∀ i : Fin cfg.size, board i = i)

end SlidingPuzzle
