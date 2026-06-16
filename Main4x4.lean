import Sliding.FifteenPuzzle

open FifteenPuzzle

-- ============================================================
-- Display
-- ============================================================

-- 3-char tile label: single-digit tiles get a leading space; blank is " _"
def tileStr4 (t : Fin 16) : String :=
  if t == blankTile then "  _"
  else if t.val < 10 then s!"  {t.val}"
  else s!" {t.val}"

-- Print a 4×4 grid.  Each cell is 3 chars wide inside " | " separators.
def displayBoard4 (board : Board) : IO Unit := do
  let tile := fun n (h : n < 16) => tileStr4 (board ⟨n, h⟩)
  let sep  := "+-----+-----+-----+-----+"
  IO.println sep
  IO.println s!"| {tile  0 (by decide)} | {tile  1 (by decide)} | {tile  2 (by decide)} | {tile  3 (by decide)} |"
  IO.println sep
  IO.println s!"| {tile  4 (by decide)} | {tile  5 (by decide)} | {tile  6 (by decide)} | {tile  7 (by decide)} |"
  IO.println sep
  IO.println s!"| {tile  8 (by decide)} | {tile  9 (by decide)} | {tile 10 (by decide)} | {tile 11 (by decide)} |"
  IO.println sep
  IO.println s!"| {tile 12 (by decide)} | {tile 13 (by decide)} | {tile 14 (by decide)} | {tile 15 (by decide)} |"
  IO.println sep

-- ============================================================
-- Input parsing
-- ============================================================

-- Accept any string whose digit characters form a number 0–15.
def parsePosition4 (s : String) : Option Position :=
  match (String.ofList (s.toList.filter Char.isDigit)).toNat? with
  | none   => none
  | some n => if h : n < 16 then some ⟨n, h⟩ else none

-- ============================================================
-- Game loop
-- ============================================================

partial def gameLoop4 (state : PuzzleState) : IO Unit := do
  IO.println ""
  IO.println s!"── Move {state.moves} ──────────────────────"
  IO.println "Position guide:  0  1  2  3"
  IO.println "                 4  5  6  7"
  IO.println "                 8  9 10 11"
  IO.println "                12 13 14 15"
  displayBoard4 state.board
  if isSolved state.board then
    IO.println s!"\nSolved in {state.moves} moves!"
    return
  IO.print "\nSlide tile at position (0-15): "
  let stdin ← IO.getStdin
  let input ← stdin.getLine
  if input.isEmpty then
    IO.println "\nGame ended."
    return
  match parsePosition4 input with
  | none =>
    IO.println s!"Not a valid position (0-15). Try again."
    gameLoop4 state
  | some pos =>
    match slideMove state.board pos with
    | none =>
      IO.println s!"Position {pos.val} is not adjacent to the blank — try another."
      gameLoop4 state
    | some newBoard =>
      gameLoop4 { board := newBoard, moves := state.moves + 1 }

-- ============================================================
-- Random scrambling
-- ============================================================

-- All positions from which the blank can be reached in one move.
def validMoves4 (board : Board) : List Position :=
  (List.finRange 16).filter (canMove board)

-- Random walk: apply `steps` random legal moves starting from `board`.
-- Each step draws one byte from the OS entropy pool — no seed, different every run.
-- Every intermediate state is a legal Board, so the result is always solvable.
def randomScramble4 (board : Board) (steps : Nat) : IO Board := do
  let mut b := board
  for _ in List.range steps do
    let moves := validMoves4 b
    if !moves.isEmpty then
      let bytes ← IO.getRandomBytes 1
      let pos := moves[bytes[0]!.toNat % moves.length]!
      if let some newB := slideMove b pos then
        b := newB
  return b

-- ============================================================
-- Entry point
-- ============================================================

def main : IO Unit := do
  IO.println "+------------------------------------------+"
  IO.println "|   4x4 Sliding Tile Puzzle (15-Puzzle)    |"
  IO.println "+------------------------------------------+"
  IO.println "Tiles 0-14 are numbered.  _ is the blank."
  IO.println "Goal: reach  0  1  2  3"
  IO.println "             4  5  6  7"
  IO.println "             8  9 10 11"
  IO.println "            12 13 14  _"
  IO.println ""
  IO.println "Type the position number of the tile to slide."
  let startBoard ← randomScramble4 solvedBoard 200
  gameLoop4 { board := startBoard, moves := 0 }
