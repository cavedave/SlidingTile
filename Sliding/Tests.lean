import Sliding.Basic

-- ============================================================
-- Setup: starting board [1,2,3,4], blank (4) at position 3
-- 1 2
-- 3 4
-- ============================================================

def startBoard : Board := ⟨#[1, 2, 3, 4], by decide⟩

-- ============================================================
-- canMove tests
-- ============================================================

-- Position 1 (value 2) is adjacent to blank (position 3) — same column
#guard canMove startBoard ⟨1, by decide⟩ = true

-- Position 2 (value 3) is adjacent to blank (position 3) — same row
#guard canMove startBoard ⟨2, by decide⟩ = true

-- Position 0 (value 1) is diagonal to blank (position 3) — NOT adjacent
#guard canMove startBoard ⟨0, by decide⟩ = false

-- ============================================================
-- slideMove tests
-- ============================================================

-- VALID MOVE: slide tile 2 (pos 1) into blank (pos 3)
-- 1 2        1 4
-- 3 4   ->   3 2
#guard slideMove startBoard ⟨1, by decide⟩ == some ⟨#[1, 4, 3, 2], by decide⟩

-- should fail as 2 2s are not allowed in the board
#guard !slideMove startBoard ⟨1, by decide⟩ == some ⟨#[1, 2, 3, 2], by decide⟩

-- should fail as 5 tiles are not allowed in the board
--#check_failure !slideMove startBoard ⟨1, by decide⟩ == some ⟨#[1, 2, 3, 4,5], by decide⟩

-- A 5-element array can never have size 4
example : ¬ (#[1, 2, 3, 4, 5] : Array Tile).size = PUZZLE_SIZE := by decide

-- INVALID MOVE: try to slide tile 1 (pos 0, diagonal) into blank
-- Should return none
#guard slideMove startBoard ⟨0, by decide⟩ = none

-- Sanity check: tile 1 exists in the initial board, at position 0
example : ∃ pos, initialState.board.get pos = (Tile.mk 1) := by
  exact ⟨⟨0, by decide⟩, by decide⟩

example : initialState.board.toList.contains (Tile.mk 1) = true := by decide
