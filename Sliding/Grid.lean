/-!
# Square Grid Geometry

Functions for measuring distances and testing adjacency on a square grid.
Positions are `Fin (width * width)` with row-major flat indexing:
  row = idx / width,  col = idx % width

This is the only thing that changes when you move to a different board shape:
- Cylinder: wrap adjacency at column 0 and column (width-1)
- Hex: six neighbours instead of four
- Any other shape: replace these functions
-/

/-- Taxicab (Manhattan) distance between two positions on a `width × width` grid.

    For natural numbers, `|a - b| = (a - b) + (b - a)` because Lean's subtraction
    truncates at zero: exactly one of `a - b` and `b - a` is nonzero. -/
def squareTaxicabDist (width : Nat) (p q : Fin (width * width)) : Nat :=
  let pr := p.val / width;  let pc := p.val % width
  let qr := q.val / width;  let qc := q.val % width
  ((pr - qr) + (qr - pr)) + ((pc - qc) + (qc - pc))

/-- Two positions are adjacent on a `width × width` grid if they share a row
    and differ by exactly 1 column, or share a column and differ by exactly 1 row. -/
def squareAdj (width : Nat) (p q : Fin (width * width)) : Bool :=
  let pr := p.val / width;  let pc := p.val % width
  let qr := q.val / width;  let qc := q.val % width
  (pr == qr && (pc + 1 == qc || qc + 1 == pc)) ||
  (pc == qc && (pr + 1 == qr || qr + 1 == pr))
