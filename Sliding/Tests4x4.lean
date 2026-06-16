import Sliding.FifteenPuzzle

open FifteenPuzzle

/-!
# Tests for the 4×4 (15-Puzzle)

Solved board layout (position → tile label):
   0   1   2   3
   4   5   6   7
   8   9  10  11
  12  13  14   _   ← blank (tile 15) at position 15
-/

-- ============================================================
-- canMove tests
-- ============================================================

-- pos 14 (row 3, col 2) is adjacent to blank at pos 15 (same row, cols differ by 1)
#guard canMove solvedBoard ⟨14, by decide⟩ = true

-- pos 11 (row 2, col 3) is adjacent to blank at pos 15 (same col, rows differ by 1)
#guard canMove solvedBoard ⟨11, by decide⟩ = true

-- pos 13 (row 3, col 1) is in the same row as blank but 2 columns away — not adjacent
#guard canMove solvedBoard ⟨13, by decide⟩ = false

-- pos 0 (top-left corner) is far from blank — not adjacent
#guard canMove solvedBoard ⟨0, by decide⟩ = false

-- ============================================================
-- slideMove tests
-- ============================================================

-- VALID: slide tile 14 (at pos 14) into blank (at pos 15)
-- Before: ... 14  _      After: ...  _  14
#guard (slideMove solvedBoard ⟨14, by decide⟩).map (· ⟨14, by decide⟩) == some blankTile
#guard (slideMove solvedBoard ⟨14, by decide⟩).map (· ⟨15, by decide⟩) == some ⟨14, by decide⟩
-- All other positions unchanged
#guard (slideMove solvedBoard ⟨14, by decide⟩).map (· ⟨0,  by decide⟩) == some ⟨0,  by decide⟩

-- INVALID: pos 0 is not adjacent to blank at pos 15
#guard (slideMove solvedBoard ⟨0, by decide⟩).isNone

-- ============================================================
-- isSolved tests
-- ============================================================

-- The solved board is solved.
#guard isSolved solvedBoard = true

-- Swapping tiles at positions 0 and 1 gives an unsolved board.
def twoTilesSwapped4 : Board := Equiv.swap ⟨0, by decide⟩ ⟨1, by decide⟩
#guard isSolved twoTilesSwapped4 = false

-- Round-trip: slide a tile out and back gives the solved board again.
#guard (do
  let b1 ← slideMove solvedBoard ⟨14, by decide⟩  -- slide tile 14 into blank
  let b2 ← slideMove b1 ⟨15, by decide⟩           -- slide tile 14 back
  return isSolved b2) == some true

-- ============================================================
-- Type definition sanity checks
-- ============================================================

-- There are 16 positions (0–15).
example : Fintype.card Position = 16 := by decide

-- The blank label is 15 (the last Fin 16 value).
example : blankTile.val = 15 := by decide

-- All positions are in range.
example (p : Position) : p.val < 16 := p.isLt

-- ============================================================
-- Bijection guarantees (same as 2×2, now at 4×4 scale)
-- ============================================================

-- No two positions can hold the same tile on any valid board.
example (board : Board) (t : Position)
    (h0 : board ⟨0, by decide⟩ = t)
    (h1 : board ⟨1, by decide⟩ = t) : False :=
  absurd (board.injective (h0.trans h1.symm)) (by decide)

-- Every tile label appears somewhere on any valid board.
example (board : Board) : ∀ tile : Position, ∃ pos, board pos = tile :=
  board.surjective

-- ============================================================
-- Solvability checker
-- ============================================================

-- The solved board is solvable: sign = 1 (identity), blank at goal, distance 0.
-- 1 = (-1)^0 ✓
#guard isSolvable solvedBoard = true

-- Sam Loyd's impossible puzzle: tiles 13 and 14 are swapped, blank stays in place.
--
-- In the classic 15-puzzle this is "swap 14 and 15"; in our 0-indexed version
-- tiles 0-14 are numbered and tile 15 is the blank, so the equivalent is swapping
-- tiles 13 and 14.
--
-- This board has sign = -1 (one transposition), but blank is still at position 15
-- (taxicabDist to goal = 0, so expected sign = (-1)^0 = 1).
-- -1 ≠ 1 → invariant violated → unreachable from solved → unsolvable.
def samLoydBoard : Board := Equiv.swap ⟨13, by decide⟩ ⟨14, by decide⟩
#guard isSolvable samLoydBoard = false

-- ============================================================
-- Toy puzzle solvability checks
-- ============================================================
-- Boards photographed from the back of a physical sliding tile toy.
-- Toy tile labels are 1–15 (blank = _); we convert: toy tile k → our tile k-1,
-- toy blank → our tile 15.
-- Each list: entry at index p = tile at position p.
--
-- We use `Equiv.mk` directly (not `Equiv.ofBijective`) because `ofBijective`
-- uses classical choice to build the inverse, making it `noncomputable`.
-- `Equiv.mk` is just a structure; we supply the inverse list ourselves
-- and let `by decide` check the two lists are genuine inverses.

@[reducible] private def look (l : List (Fin 16)) (p : Fin 16) : Fin 16 :=
  l.getD p.val ⟨0, by decide⟩

-- "1 to 15": tiles in reading order — this IS the solved board.
def toyBoard_1to15 : Board := solvedBoard

-- "15 to 1": tiles in reverse order.  The permutation is self-inverse
-- (swaps k↔14-k for k=0..6, fixes 7 and 15).
def toyBoard_15to1 : Board where
  toFun    := look [14,13,12,11,10, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0,15]
  invFun   := look [14,13,12,11,10, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0,15]
  left_inv  := by decide
  right_inv := by decide

-- "Vertical Numbers": column-major order — also self-inverse.
def toyBoard_vertical : Board where
  toFun    := look [ 0, 4, 8,12, 1, 5, 9,13, 2, 6,10,14, 3, 7,11,15]
  invFun   := look [ 0, 4, 8,12, 1, 5, 9,13, 2, 6,10,14, 3, 7,11,15]
  left_inv  := by decide
  right_inv := by decide

-- "Skip Odd to Even": within each row, odd tiles before even — self-inverse.
def toyBoard_skipOddEven : Board where
  toFun    := look [ 0, 2, 1, 3, 4, 6, 5, 7, 8,10, 9,11,12,14,13,15]
  invFun   := look [ 0, 2, 1, 3, 4, 6, 5, 7, 8,10, 9,11,12,14,13,15]
  left_inv  := by decide
  right_inv := by decide

-- "2nd Skip Odd to Even": odd tiles fill rows 0-1, even tiles fill rows 2-3.
-- Inverse is "Vertical Odd/Even" (they are mutual inverses).
def toyBoard_skipOddEven2 : Board where
  toFun    := look [ 0, 2, 4, 6, 8,10,12,14, 1, 3, 5, 7, 9,11,13,15]
  invFun   := look [ 0, 8, 1, 9, 2,10, 3,11, 4,12, 5,13, 6,14, 7,15]
  left_inv  := by decide
  right_inv := by decide

-- "Vertical Odd/Even": interleave column-major odd and even groups.
-- Inverse of "2nd Skip Odd to Even".
def toyBoard_verticalOddEven : Board where
  toFun    := look [ 0, 8, 1, 9, 2,10, 3,11, 4,12, 5,13, 6,14, 7,15]
  invFun   := look [ 0, 2, 4, 6, 8,10,12,14, 1, 3, 5, 7, 9,11,13,15]
  left_inv  := by decide
  right_inv := by decide

-- "Skip Odd/Even": blank at position 12 (row 3, col 0) — not bottom-right!
def toyBoard_skipOddEven3 : Board where
  toFun    := look [ 0, 3, 4, 7, 1, 2, 5, 6, 8, 9,12,13,15,10,11,14]
  invFun   := look [ 0, 4, 5, 1, 2, 6, 7, 3, 8, 9,13,14,10,11,15,12]
  left_inv  := by decide
  right_inv := by decide

private def showResult (name : String) (b : Board) : IO Unit :=
  IO.println s!"{if isSolvable b then "✓ solvable  " else "✗ UNSOLVABLE"}  {name}"

#eval do
  showResult "1 to 15  (= solved)"  toyBoard_1to15
  showResult "15 to 1"              toyBoard_15to1
  showResult "Vertical Numbers"     toyBoard_vertical
  showResult "Skip Odd to Even"     toyBoard_skipOddEven
  showResult "2nd Skip Odd to Even" toyBoard_skipOddEven2
  showResult "Vertical Odd/Even"    toyBoard_verticalOddEven
  showResult "Skip Odd/Even"        toyBoard_skipOddEven3
