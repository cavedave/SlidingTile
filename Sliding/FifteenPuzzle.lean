import Mathlib.GroupTheory.Perm.Sign
import Sliding.Puzzle
import Sliding.Grid

/-!
# The 15-Puzzle (4 × 4 Sliding Tile Puzzle)

Tiles are labelled 0–14; tile 15 is the blank.
Positions 0–15 are in row-major order:

   0   1   2   3
   4   5   6   7
   8   9  10  11
  12  13  14  15  ← blank starts here on the solved board
-/

namespace FifteenPuzzle

private def cfg : PuzzleConfig :=
  { size     := 16
    size_pos := by decide
    adj      := squareAdj 4 }

abbrev Position := Fin 16
abbrev Board    := Equiv.Perm Position

def blankTile   : Position := SlidingPuzzle.blankTile cfg
def solvedBoard : Board    := SlidingPuzzle.solvedBoard cfg

def blankPosition (board : Board) : Position :=
  SlidingPuzzle.blankPosition cfg board

def canMove (board : Board) (pos : Position) : Bool :=
  SlidingPuzzle.canMove cfg board pos

def slideMove (board : Board) (pos : Position) : Option Board :=
  SlidingPuzzle.slideMove cfg board pos

def isSolved (board : Board) : Bool :=
  SlidingPuzzle.isSolved cfg board

/-- Is this board reachable from the solved state?

    The solvability invariant (proved structurally in `Parity.lean`):
      sign(board) = (-1) ^ taxicabDist(blankPos, goalPos)

    - `sign = 1`  (even permutation) iff blank is an even number of steps from its goal.
    - `sign = -1` (odd  permutation) iff blank is an odd  number of steps from its goal.

    The blank's goal position on a solved board is `blankTile` (position = label = 15).
    We check that the two parities agree. -/
def isSolvable (board : Board) : Bool :=
  let blankPos := blankPosition board
  let dist     := squareTaxicabDist 4 blankPos blankTile
  let signEven := Equiv.Perm.sign board == (1 : ℤˣ)
  signEven == (dist % 2 == 0)

structure PuzzleState where
  board : Board
  moves : Nat

def initialState : PuzzleState := { board := solvedBoard, moves := 0 }

end FifteenPuzzle
