import Sliding.Basic

-- ============================================================
-- Display
-- ============================================================

-- Show one tile: blank prints as " _", numbered tiles print their label.
def tileStr (t : Fin PUZZLE_SIZE) : String :=
  if t == blankTile then " _" else s!" {t.val}"

-- Print the board as a 2×2 grid alongside its position numbers.
-- The position numbers tell the player what to type.
--
--   +----+----+        positions:  0 | 1
--   |  0 |  1 |                   -----
--   +----+----+                   2 | 3
--   |  2 |  _ |
--   +----+----+
def displayBoard (board : Board) : IO Unit := do
  let t := fun n h => tileStr (board ⟨n, h⟩)
  IO.println "+----+----+     positions:"
  IO.println s!"| {t 0 (by decide)} | {t 1 (by decide)} |     0 | 1"
  IO.println "+----+----+     ------"
  IO.println s!"| {t 2 (by decide)} | {t 3 (by decide)} |     2 | 3"
  IO.println "+----+----+"

-- ============================================================
-- Input parsing
-- ============================================================

-- Try to read a position 0–3 from a line of text.
-- Returns none if the input is not a valid number in range.
-- We keep only digit characters so trailing newlines are ignored automatically.
def parsePosition (s : String) : Option Position :=
  match (String.ofList (s.toList.filter Char.isDigit)).toNat? with
  | none   => none
  | some n => if h : n < PUZZLE_SIZE then some ⟨n, h⟩ else none

-- ============================================================
-- Game loop
-- ============================================================

-- `partial` because the user can play as many moves as they like —
-- Lean cannot prove this terminates. Everything inside is still type-safe:
-- slideMove returns Option so bad moves are handled without crashing.
partial def gameLoop (state : PuzzleState) : IO Unit := do
  IO.println ""
  IO.println s!"── Move {state.moves} ──────────────────"
  displayBoard state.board
  if isSolved state.board then
    IO.println s!"\nSolved in {state.moves} moves!"
    return
  IO.print "\nSlide tile at position (0-3): "
  let stdin ← IO.getStdin
  let input ← stdin.getLine
  -- getLine returns "" on EOF (Ctrl-D or piped input ending)
  if input.isEmpty then
    IO.println "\nGame ended."
    return
  match parsePosition input with
  | none =>
    IO.println s!"'{String.ofList (input.toList.filter Char.isDigit)}' is not a valid position. Enter 0, 1, 2, or 3."
    gameLoop state
  | some pos =>
    match slideMove state.board pos with
    | none =>
      IO.println s!"Position {pos.val} is not next to the blank — try another."
      gameLoop state
    | some newBoard =>
      gameLoop { board := newBoard, moves := state.moves + 1 }

-- ============================================================
-- Random scrambling
-- ============================================================

def validMoves2 (board : Board) : List Position :=
  (List.finRange 4).filter (canMove board)

-- 50 random moves is more than enough for the 2×2 (only 12 reachable states).
def randomScramble2 (board : Board) (steps : Nat) : IO Board := do
  let mut b := board
  for _ in List.range steps do
    let moves := validMoves2 b
    if !moves.isEmpty then
      let bytes ← IO.getRandomBytes 1
      if let some pos := moves[bytes[0]!.toNat % moves.length]? then
        if let some newB := slideMove b pos then
          b := newB
  return b

-- ============================================================
-- Entry point
-- ============================================================

def main : IO Unit := do
  IO.println "+---------------------------------+"
  IO.println "|   2x2 Sliding Tile Puzzle       |"
  IO.println "+---------------------------------+"
  IO.println "Tiles 0 1 2 are numbered.  _ is the blank."
  IO.println "Goal: reach   0 | 1"
  IO.println "              2 | _"
  IO.println ""
  IO.println "Type the position number of the tile you want to slide."
  let startBoard ← randomScramble2 solvedBoard 50
  gameLoop { board := startBoard, moves := 0 }
