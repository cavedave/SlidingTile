import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Data.Fintype.Card

-- ============================================================
-- Core types
-- ============================================================

-- Total number of cells on the board (4 for a 2×2 grid).
def PUZZLE_SIZE : Nat := 4

-- A Position is a cell index: Fin 4 = {0, 1, 2, 3}.
abbrev Position := Fin PUZZLE_SIZE

-- A Board is a *permutation* of positions.
-- Concretely: `board pos` = the tile label sitting at that position.
-- `Equiv.Perm (Fin 4)` is a bijection Fin 4 → Fin 4 with a built-in inverse.
-- This means: no two positions can ever hold the same label. Guaranteed by the type.
abbrev Board := Equiv.Perm (Fin PUZZLE_SIZE)

-- Tile labels 0–2 are the numbered tiles; label 3 is the blank.
-- `Fin.last 3` is the value ⟨3, by omega⟩ — the largest element of Fin 4.
def blankTile : Fin PUZZLE_SIZE := Fin.last (PUZZLE_SIZE - 1)

-- The solved board is the identity permutation: tile i sits at position i.
-- After all moves, we want to reach this state.
def solvedBoard : Board := Equiv.refl (Fin PUZZLE_SIZE)

-- Bundle the board with a move counter.
structure PuzzleState where
  board : Board
  moves : Nat

-- The starting state: solved board, zero moves.
def initialState : PuzzleState :=
  { board := solvedBoard, moves := 0 }

-- ============================================================
-- Helper Predicates
-- ============================================================

-- The 2×2 grid has width 2. Position p maps to:
--   row = p.val / 2,  col = p.val % 2
-- Positions: 0=(0,0)  1=(0,1)
--            2=(1,0)  3=(1,1)
def gridWidth : Nat := 2

-- Two positions are adjacent if they share a row and differ by 1 column,
-- or share a column and differ by 1 row. No diagonals.
def isAdjacent (p q : Position) : Bool :=
  let pr := p.val / gridWidth;  let pc := p.val % gridWidth
  let qr := q.val / gridWidth;  let qc := q.val % gridWidth
  (pr == qr && (pc + 1 == qc || qc + 1 == pc)) ||
  (pc == qc && (pr + 1 == qr || qr + 1 == pr))

-- Where is the blank tile right now?
-- `board.symm` is the inverse of `board`: given a tile label, it tells us
-- which position holds that label.
def blankPosition (board : Board) : Position :=
  board.symm blankTile

-- ============================================================
-- Game rules
-- ============================================================

-- Can we slide the tile at `pos` into the blank?
-- Yes if and only if `pos` is adjacent to the blank's position.
def canMove (board : Board) (pos : Position) : Bool :=
  isAdjacent pos (blankPosition board)

-- Slide the tile at `pos` into the blank space.
--
-- How this works in terms of permutations:
--   `board pos`  = the tile currently at `pos`  (some numbered tile)
--   `blankTile`  = the tile currently at `blankPosition board`
--   `Equiv.swap t1 t2` = the permutation that swaps two tile labels everywhere
--   `board.trans swap` = run `board` first (map positions to labels),
--                        then apply the swap (exchange those two label values)
--
-- Net result: position `pos` now shows `blankTile`,
--             old blank position now shows the numbered tile. All other positions unchanged.
def slideMove (board : Board) (pos : Position) : Option Board :=
  if canMove board pos then
    some (board.trans (Equiv.swap (board pos) blankTile))
  else
    none

-- Is the puzzle solved?
-- `decide` turns the proposition "∀ i, board i = i" into a Bool at compile time.
-- It works because `Fin PUZZLE_SIZE` is a `Fintype` with decidable equality,
-- so Lean can check every position in a finite loop.
def isSolved (board : Board) : Bool :=
  decide (∀ i : Position, board i = i)
