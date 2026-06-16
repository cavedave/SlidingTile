import Sliding.Basic

-- ============================================================
-- Setup
-- ============================================================
-- We use `solvedBoard` as our test board: blank (tile 3) sits at position 3.
--
-- Grid layout (position → tile on solved board):
--   pos 0 (row 0, col 0) → tile 0
--   pos 1 (row 0, col 1) → tile 1
--   pos 2 (row 1, col 0) → tile 2
--   pos 3 (row 1, col 1) → tile 3 = blank

-- ============================================================
-- canMove tests
-- ============================================================

-- pos 1 (top-right) is adjacent to blank at pos 3 (same column, rows differ by 1)
#guard canMove solvedBoard ⟨1, by decide⟩ = true

-- pos 2 (bottom-left) is adjacent to blank at pos 3 (same row, cols differ by 1)
#guard canMove solvedBoard ⟨2, by decide⟩ = true

-- pos 0 (top-left) is diagonal to blank — NOT adjacent
#guard canMove solvedBoard ⟨0, by decide⟩ = false

-- ============================================================
-- slideMove tests
-- ============================================================

-- VALID MOVE: slide tile 1 (at pos 1) into blank (at pos 3)
-- Before:  [0, 1, 2, blank]
-- After:   [0, blank, 2, 1]
#guard (slideMove solvedBoard ⟨1, by decide⟩).map (· ⟨0, by decide⟩) == some ⟨0, by decide⟩
#guard (slideMove solvedBoard ⟨1, by decide⟩).map (· ⟨1, by decide⟩) == some blankTile
#guard (slideMove solvedBoard ⟨1, by decide⟩).map (· ⟨2, by decide⟩) == some ⟨2, by decide⟩
#guard (slideMove solvedBoard ⟨1, by decide⟩).map (· ⟨3, by decide⟩) == some ⟨1, by decide⟩

-- INVALID MOVE: pos 0 is diagonal to blank — should return none
#guard (slideMove solvedBoard ⟨0, by decide⟩).isNone

-- ============================================================
-- isSolved tests
-- ============================================================

-- A board with two tiles swapped is NOT solved.
-- This echoes Sam Loyd's challenge: swap tiles 0 and 1 and try to restore order.
-- `Equiv.swap` produces the transposition (0 1) — tiles at pos 0 and pos 1 are exchanged.
-- isSolved must correctly reject this.
def twoTilesSwapped : Board := Equiv.swap ⟨0, by decide⟩ ⟨1, by decide⟩
#guard isSolved twoTilesSwapped = false

-- Sliding a tile out and then back gives a solved board again (round-trip).
-- This confirms slideMove is a true inverse of itself for a single step.
#guard (do
  let b1 ← slideMove solvedBoard ⟨1, by decide⟩  -- slide tile 1 into blank
  let b2 ← slideMove b1 ⟨3, by decide⟩           -- slide tile 1 back
  return isSolved b2) == some true

-- ============================================================
-- Type definition sanity checks
-- ============================================================
-- These prove that our type definitions are reasonable — not that any
-- specific board is correct, but that the types themselves make sense.

-- PUZZLE_SIZE is positive: a puzzle with 0 cells would be nonsensical.
example : 0 < PUZZLE_SIZE := by decide

-- All tile values are non-negative.
-- `Fin` wraps `Nat` which has no negatives — this is guaranteed structurally.
example (t : Fin PUZZLE_SIZE) : 0 ≤ t.val := Nat.zero_le _

-- All tile values are strictly less than PUZZLE_SIZE.
-- This is `t.isLt` — the proof that was stored inside the Fin when it was constructed.
example (t : Fin PUZZLE_SIZE) : t.val < PUZZLE_SIZE := t.isLt

-- The blank tile is in range.
example : blankTile.val < PUZZLE_SIZE := blankTile.isLt

-- The blank LABEL is 3 (the last value in Fin 4).
-- Note: this is the *label*, not the *position*.
-- `blankTile` is a fixed constant — the name we gave to the blank piece.
-- `blankPosition board` is what changes with each move: it tells you where
-- on the board the blank label currently sits. A board with the blank at
-- position 1 is perfectly valid — just not solved.
example : blankTile.val = PUZZLE_SIZE - 1 := by decide

-- The number of possible tile labels equals the number of positions.
-- Tiles and positions share the same type (Fin PUZZLE_SIZE), so
-- there is one slot for every label and one label for every slot.
example : Fintype.card (Fin PUZZLE_SIZE) = Fintype.card Position := by decide

-- ============================================================
-- Negative type examples
-- ============================================================
-- To build an `Equiv.Perm`, Lean requires you to prove the function has a left inverse.
-- For an illegal board, that proof obligation is *false* — `decide` can confirm it.
-- These examples show the type-level barrier that replaces `wellFormedPuzzle`.

-- DUPLICATE TILE: [1, 1, 2, blank]
-- Positions 0 and 1 both hold tile 1. This function is not injective.
-- To build an Equiv.Perm Lean needs: ∀ a b, f a = f b → a = b.
-- `decide` finds a counterexample (pos 0 and pos 1) and proves that requirement false.
private def duplicateTileAttempt : Fin 4 → Fin 4
  | ⟨0, _⟩ => ⟨1, by decide⟩  -- tile 1
  | ⟨1, _⟩ => ⟨1, by decide⟩  -- tile 1 again  ← illegal
  | ⟨2, _⟩ => ⟨2, by decide⟩  -- tile 2
  | _       => ⟨3, by decide⟩  -- blank

-- `decide` can find a concrete counterexample to injectivity:
-- positions 0 and 1 are different but map to the same tile.
example : ∃ a b : Fin 4, duplicateTileAttempt a = duplicateTileAttempt b ∧ a ≠ b := by decide

-- MISSING TILE: [1, 2, blank, blank]
-- Tile 0 never appears; blank appears twice. This function is not surjective.
-- To build an Equiv.Perm Lean needs: ∀ b, ∃ a, f a = b.
-- `decide` shows tile 0 has no preimage, so that requirement is false.
private def missingTileAttempt : Fin 4 → Fin 4
  | ⟨0, _⟩ => ⟨1, by decide⟩  -- tile 1
  | ⟨1, _⟩ => ⟨2, by decide⟩  -- tile 2
  | ⟨2, _⟩ => ⟨3, by decide⟩  -- blank
  | _       => ⟨3, by decide⟩  -- blank again  ← tile 0 missing

-- `decide` confirms tile 0 has no preimage in the above function.
example : ∀ a : Fin 4, missingTileAttempt a ≠ ⟨0, by decide⟩ := by decide

-- ============================================================
-- Universal bijection guarantees (for every valid Board)
-- ============================================================

-- DUPLICATE TILE IS IMPOSSIBLE for any Board:
-- If board p = board q then p = q — injectivity is a field of Equiv.Perm.
example (board : Board) (t : Fin PUZZLE_SIZE)
    (h0 : board ⟨0, by decide⟩ = t)
    (h1 : board ⟨1, by decide⟩ = t) : False :=
  absurd (board.injective (h0.trans h1.symm)) (by decide)

-- MISSING TILE IS IMPOSSIBLE for any Board:
-- For ALL tile labels, there EXISTS a position on the board that holds it.
-- Both quantifiers are needed: ∀ (pick any tile) then ∃ (find its position).
-- The old `tileExistsInWellFormed` needed ~15 lines. Now it is one word.
example (board : Board) : ∀ tile : Fin PUZZLE_SIZE, ∃ pos, board pos = tile :=
  board.surjective

-- NUMBER OF DISTINCT TILES = PUZZLE_SIZE:
-- The set of tile values that appear on the board has exactly PUZZLE_SIZE members.
-- This is the type-level equivalent of `assert len(set(board)) == PUZZLE_SIZE` in Python.
-- It follows from injectivity: an injective function on a set of size n
-- produces exactly n distinct output values.
example (board : Board) :
    (Finset.univ (α := Fin PUZZLE_SIZE) |>.image board).card = PUZZLE_SIZE := by
  rw [Finset.card_image_of_injective _ board.injective]
  decide

-- OUT OF RANGE TILE IS A COMPILE ERROR:
-- `⟨-1, by decide⟩ : Fin -1` does not compile — `decide` cannot prove `-1 >0 `.
-- There is no runtime check needed; the type simply has no such value.
-- Uncomment to see the error:
--example : Fin -1 := ⟨-1, by decide⟩  -- error: decide tactic failed
