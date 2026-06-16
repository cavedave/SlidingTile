-- Sliding Tile Puzzle (2×2 for now, generalizable to 4×4)
-- Goal state: [1, 2, 3, 4] where 4 = blank

-- ============================================================
-- Data Types
-- ============================================================

#check @Vector.set


-- Tile: Nat where 4 = blank, 1..3 = numbered tiles
structure Tile where
  val : Nat
deriving Repr, DecidableEq

-- Lean needs to know a default Tile value
deriving instance Inhabited for Tile

-- Allow numerals to be interpreted as Tiles
  instance : OfNat Tile n where
  ofNat := { val := n }

-- Board: Vector of 4 tiles in row-major order
-- [0, 1, 2, 3] = row 0, col 0/1, row 1, col 0/1

  def PUZZLE_SIZE : Nat := 4
  def Board := Vector Tile PUZZLE_SIZE deriving Repr, BEq
  def Position := Fin PUZZLE_SIZE
--def Board := Vector Tile 4 deriving Repr, BEq

-- Position on board: Fin 4 (0..3)
--def Position := Fin 4

-- Puzzle state
structure PuzzleState where
  board : Board
  moves : Nat
deriving Repr

-- ============================================================
-- Helper Predicates
-- ============================================================

def isBlank (tile : Tile) : Bool :=
  tile.val == 4  -- 2×2: blank is tile 4

def blankPosition (board : Board) : Option Position :=
  board.toList.findIdx isBlank |> fun idx =>
    if h : idx < 4 then some ⟨idx, h⟩ else none

-- ============================================================
-- Game Rules
-- ============================================================

-- Is this position adjacent to the blank?
def canMove (board : Board) (pos : Position) : Bool :=
  match blankPosition board with
  | none => false
  | some blankPos =>
    -- Adjacent means: same row (differ by 1 col) or same col (differ by 1 row)
    let row1 := pos.val / 2
    let col1 := pos.val % 2
    let row2 := blankPos.val / 2
    let col2 := blankPos.val % 2
    (row1 == row2 && (col1 + 1 == col2 || col1 == col2 + 1)) ||
    (col1 == col2 && (row1 + 1 == row2 || row1 == row2 + 1))

-- Apply a move: slide tile at pos into blank (swap positions)
-- Apply a move: slide tile at pos into blank (swap positions)
-- Apply a move: slide tile at pos into blank (swap positions)
def slideMove (board : Board) (pos : Position) : Option Board :=
  match blankPosition board with
  | none => none
  | some blankPos =>
    if canMove board pos then
      let tileAtPos := board.get pos
      let tileAtBlank := board.get blankPos
      let newBoard := (board.set pos.val tileAtBlank pos.isLt).set blankPos.val tileAtPos blankPos.isLt
      some newBoard
    else
      none

-- Is the board solved?
-- Is the board solved?
-- Is the board solved?
def isSolved (board : Board) : Bool :=
  board == ⟨#[{ val := 1 }, { val := 2 }, { val := 3 }, { val := 4 }], by decide⟩

-- Well-formed puzzle: each tile 1..4 appears exactly once
-- Well-formed puzzle: each tile 1..4 appears exactly once
--def wellFormedPuzzle (state : PuzzleState) : Bool :=
--  let sorted := state.board.toList.mergeSort (fun a b => a.val < b.val)
--  sorted == [{ val := 1 }, { val := 2 }, { val := 3 }, { val := 4 }]

-- Well-formed puzzle: each tile 1..4 appears exactly once
-- Helper: Check if list contains all tiles from 1 to n
--def containsAllTiles (list : List Tile) (n : Nat) : Bool :=
--  (List.range n).all (fun i =>
--    let tile : Tile := { val := i + 1 }
--    list.contains tile)

def containsAllTiles (list : List Tile) (n : Nat) : Bool :=
  (List.range n).all (fun i => list.contains { val := i + 1 })

-- Well-formed puzzle: has all tiles 1..4
  def wellFormedPuzzle (state : PuzzleState) : Bool :=
    let list := state.board.toList
    list.length == PUZZLE_SIZE && containsAllTiles list PUZZLE_SIZE


-- ============================================================
-- Initial State
-- ============================================================

def initialState : PuzzleState :=
  { board := ⟨#[1, 2, 3, 4], by decide⟩, moves := 0 }

-- ============================================================
-- Theorems (to be proven)
-- ============================================================

-- Theorem 1: Initial state is well-formed
-- Theorem 1: Initial state is well-formed
theorem initialStateIsWellFormed : wellFormedPuzzle initialState := by
  unfold wellFormedPuzzle initialState
  decide
--  norm_num [List.mergeSort, Tile.instBEq]
--  rfl

-- Find a position with a specific tile value
def findTile (board : Board) (tileVal : Nat) : Option Position :=
  let list := board.toList
  match list.findIdx (fun tile => tile.val == tileVal) with
  | idx =>
    if h : idx < PUZZLE_SIZE then
      some ⟨idx, h⟩
    else
      none

-- Theorem 2: Blank exists in well-formed puzzle
-- General theorem: If list contains all tiles 1..n, then tile k exists (where 1 ≤ k ≤ n)

theorem tileExistsInWellFormed (state : PuzzleState) (k : Nat)
  (h : wellFormedPuzzle state)
  (hk : 1 ≤ k ∧ k ≤ PUZZLE_SIZE) :
  ∃ pos, state.board.get pos = (Tile.mk k) := by
  unfold wellFormedPuzzle at h
  rw [Bool.and_eq_true] at h
  obtain ⟨hlen, hcontains⟩ := h
  unfold containsAllTiles at hcontains
  rw [List.all_eq_true] at hcontains
  have hmem_range : (k - 1) ∈ List.range PUZZLE_SIZE := by
    rw [List.mem_range]
    omega
  have hk_contains : state.board.toList.contains (Tile.mk ((k - 1) + 1)) = true :=
    hcontains (k - 1) hmem_range
  have hk_eq : (k - 1) + 1 = k := by omega
  rw [hk_eq] at hk_contains
  rw [List.contains_iff_mem] at hk_contains
  obtain ⟨i, hi_eq⟩ := List.mem_iff_get.mp hk_contains
  have hlen' : state.board.toList.length = PUZZLE_SIZE := by
    simpa using hlen
  let pos : Position := Fin.cast hlen' i
  refine ⟨pos, ?_⟩
  have hget : state.board.get pos = state.board.toList.get i := by
    simp [pos, List.get_eq_getElem, Fin.cast]
    rfl
  rw [hget, hi_eq]
  --sorry



example (board : Board) (pos : Position) (newBoard : Board)
    (h : slideMove board pos = some newBoard) :
    canMove board pos = true := by
  unfold slideMove at h
  split at h
  · -- blankPosition = none case, h : none = some newBoard, contradiction
    exact absurd h (by simp)
  · -- blankPosition = some blankPos case
    split at h
    · -- canMove = true, this is what we want
      assumption
    · -- canMove = false, h : none = some newBoard, contradiction
      exact absurd h (by simp)


-- Theorem 3: Moving preserves well-formedness
theorem slideMovePreservesWellFormedness
  (state : PuzzleState)
  (pos : Position)
  (newBoard : Board)
  (hWellFormed : wellFormedPuzzle state)
  (hCanMove : canMove state.board pos = true)
  (hNewBoard : slideMove state.board pos = some newBoard)
  : wellFormedPuzzle { board := newBoard, moves := state.moves + 1 } := by
  -- unfold slideMove to extract what newBoard actually is
  unfold slideMove at hNewBoard
  -- Case split on blankPosition state.board
  split at hNewBoard
  · -- blankPosition = none: hNewBoard : none = some newBoard, contradiction
    exact absurd hNewBoard (by simp)
  · -- blankPosition = some blankPos
    rename_i blankPos hblank
    -- Now case split on the `if canMove ... then ... else ...`
    split at hNewBoard
    · -- canMove = true: hNewBoard gives us the explicit newBoard
      rename_i hcm
      injection hNewBoard with hNewBoard
      subst hNewBoard
      -- Now the goal is about wellFormedPuzzle applied to this double-set expression.
      unfold wellFormedPuzzle at hWellFormed ⊢
      -- Split the && into two separate goals: length, and containsAllTiles
      rw [Bool.and_eq_true] at hWellFormed ⊢
      obtain ⟨hlen, hcontains⟩ := hWellFormed
      constructor
      · -- length is preserved: .set doesn't change Vector size
        simp [hlen]
      · -- containsAllTiles is preserved: need to show swapping two elements
        -- doesn't change which tiles are present
        sorry
    · -- canMove = false: contradiction with hCanMove
      rename_i hcm
      exact absurd hCanMove (by simp [hcm])

-- Theorem 4: Move count increments
theorem movesIncrement
  (state : PuzzleState)
  (pos : Position)
  (hCanMove : canMove state.board pos = true)
  (hNewBoard : slideMove state.board pos = some newBoard)
  : state.moves + 1 = state.moves + 1 := by --should state.moves relate to a newState.moves?
  rfl
