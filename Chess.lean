-- =============================================================================
-- TYPES
-- =============================================================================

-- Primitives
inductive Color: Type
 | white | black
 deriving Repr, DecidableEq

inductive castleSide: Type
  | kingSide | queenSide
  deriving Repr, DecidableEq, Inhabited

inductive PieceType: Type
 | pawn | rook | knight | bishop | queen | king
 deriving Repr, DecidableEq, Inhabited

-- Piece: (color: Color, pieceType: PieceType)

structure Piece : Type where
  pieceType: PieceType
  color : Color
  deriving Repr

-- Define the types needed for the coordinates
inductive File : Type
  | A | B | C | D | E | F | G | H
  deriving Repr, DecidableEq, Inhabited

inductive Rank : Type
  | _1 | _2 | _3 | _4 | _5 | _6 | _7 | _8
  deriving Repr, DecidableEq, Inhabited

structure Coord : Type where
  file : File
  rank : Rank
  deriving Repr, DecidableEq

namespace Coord

-- 1. Define these on the Types themselves, not on Coord
-- This makes them much easier to reuse.
def File.toNat : File → Nat
  | .A => 0 | .B => 1 | .C => 2 | .D => 3
  | .E => 4 | .F => 5 | .G => 6 | .H => 7

def Rank.toNat : Rank → Nat
  | ._1 => 0 | ._2 => 1 | ._3 => 2 | ._4 => 3
  | ._5 => 4 | ._6 => 5 | ._7 => 6 | ._8 => 7

-- 2. Update Coord wrappers to just call the helpers
def file_ord (c : Coord) : Nat := File.toNat c.file
def rank_ord (c : Coord) : Nat := Rank.toNat c.rank

-- 3. The Proofs become trivial
-- We prove it for the Piece type first
theorem File.toNat_bound (f : File) : File.toNat f < 8 := by
  cases f <;> simp [toNat]

theorem Rank.toNat_bound (r : Rank) : Rank.toNat r < 8 := by
  cases r <;> simp [toNat]

-- Then the Coord proofs just refer to those
theorem file_ord_bound (c : Coord) : c.file_ord < 8 := File.toNat_bound c.file
theorem rank_ord_bound (c : Coord) : c.rank_ord < 8 := Rank.toNat_bound c.rank

-- 4. Reverse Conversion
-- The syntax `_ + 8` is valid but sometimes brittle in matches.
-- Here is a robust way to handle the "impossible" Nat case.

def fileFromOrd (n : Nat) (h : n < 8) : File :=
  match n with
  | 0 => File.A
  | 1 => File.B
  | 2 => File.C
  | 3 => File.D
  | 4 => File.E
  | 5 => File.F
  | 6 => File.G
  | 7 => File.H

def rankFromOrd (n : Nat) (h : n < 8) : Rank :=
  match n with
  | 0 => Rank._1
  | 1 => Rank._2
  | 2 => Rank._3
  | 3 => Rank._4
  | 4 => Rank._5
  | 5 => Rank._6
  | 6 => Rank._7
  | 7 => Rank._8


end Coord

def BoardType := Fin 8 → Fin 8 → Option Piece

structure Board : Type where
  data : BoardType


def Board.pieceAt (board : Board) (file rank : Nat) (hf : file < 8) (hr : rank < 8) : Option Piece :=
  board.data ⟨file, hf⟩ ⟨rank, hr⟩


def hasStraightPath (from_ : Coord) (to_ : Coord) : Bool :=
  from_.file == to_.file || from_.rank == to_.rank

def coordSum (c : Coord) : Int :=
  (Coord.file_ord c : Int) + (Coord.rank_ord c : Int)

def coordDiff (c : Coord) : Int :=
  (Coord.file_ord c : Int) - (Coord.rank_ord c : Int)

def hasDiagonalPath (from_ to_ : Coord) : Bool :=
  (coordSum from_ == coordSum to_) || (coordDiff from_ == coordDiff to_)


def straightPathCoords (from_ to_ : Coord) : List Coord :=
  if from_.file == to_.file then
    -- CASE 1: Vertical
    let r1 := from_.rank_ord
    let r2 := to_.rank_ord
    let low := min r1 r2
    let high := max r1 r2

    -- "count" is the number of steps. If adjacent, count is 0.
    -- (high - low - 1) works because Nat subtraction stops at 0.
    let count := high - low - 1

    -- FIX: We use '.attach' to carry the proof inside the loop
    (List.range count).attach.map fun ⟨i, h_mem⟩ =>
      -- 'i' is the index
      -- 'h_mem' is the proof that i ∈ List.range count

      let k := low + 1 + i

      have h_bound : k < 8 := by
        -- 1. Extract the fact that i < count from h_mem
        have h_i_lt_count : i < count := List.mem_range.mp h_mem

        -- 2. Establish that high is a valid rank index
        have h_high_bound : high < 8 := by
          have h1 := Coord.rank_ord_bound from_
          have h2 := Coord.rank_ord_bound to_
          omega -- Max of two numbers < 8 is also < 8

        -- 3. Solve the inequality
        -- We know: k = low + 1 + i
        -- We know: i < high - low - 1
        -- Therefore: k < high < 8
        omega

      { file := from_.file, rank := Coord.rankFromOrd k h_bound }

  else if from_.rank == to_.rank then
    -- CASE 2: Horizontal
    let f1 := from_.file_ord
    let f2 := to_.file_ord
    let low := min f1 f2
    let high := max f1 f2
    let count := high - low - 1

    (List.range count).attach.map fun ⟨i, h_mem⟩ =>
      let k := low + 1 + i

      have h_bound : k < 8 := by
        have h_i_lt_count : i < count := List.mem_range.mp h_mem
        have h_high_bound : high < 8 := by
          have h1 := Coord.file_ord_bound from_
          have h2 := Coord.file_ord_bound to_
          omega
        omega

      { file := Coord.fileFromOrd k h_bound, rank := from_.rank }

  else
    []

def intToCoord (f r : Int) : Option Coord :=
  -- Runtime check: Is it within 0..7?
  if h : 0 ≤ f ∧ f < 8 ∧ 0 ≤ r ∧ r < 8 then
    -- If we are inside this block, 'h' is the proof we need!
    -- We can just pass 'h' to the conversion functions.
    let file := Coord.fileFromOrd f.toNat (by omega)
    let rank := Coord.rankFromOrd r.toNat (by omega)
    some { file, rank }
  else
    none


def diagonalPathCoords (from_ to_ : Coord) : List Coord :=
  let f1 : Int := from_.file_ord
  let r1 : Int := from_.rank_ord
  let f2 : Int := to_.file_ord
  let r2 : Int := to_.rank_ord

  let df := f2 - f1
  let dr := r2 - r1

  -- Is it actually a diagonal?
  if df.natAbs != dr.natAbs || df == 0 then
    []
  else
    let stepF : Int := if df > 0 then 1 else -1
    let stepR : Int := if dr > 0 then 1 else -1
    let count := df.natAbs - 1

    -- THE ALGORITHM:
    -- 1. Generate range 0..count
    -- 2. Map to raw Integers
    -- 3. Try to convert to Coord (filtering out 'none')
    -- if count == 0
    --   then []
    -- else
    List.range count |>.filterMap fun i =>
      let k : Nat := i + 1
      let targetF := f1 + stepF * k
      let targetR := r1 + stepR * k

      -- If this returns 'none' (out of bounds), filterMap drops it.
      -- If it returns 'some c', filterMap keeps 'c'.
      intToCoord targetF targetR


-- Helper: Get a piece using a Coord directly
-- This wraps the low-level 'pieceAt' that requires proofs.
def getPiece (board : Board) (c : Coord) : Option Piece :=
  board.data
    ⟨Coord.file_ord c, Coord.file_ord_bound c⟩
    ⟨Coord.rank_ord c, Coord.rank_ord_bound c⟩


-- Helper: Checks if the path segments are empty.
-- Assumes 'path' contains the coordinates *between* from and to.
def isPathEmpty (board : Board) (path : List Coord) : Bool :=
  path.all (fun c => (getPiece board c).isNone)

def isClearStraightPath (board : Board) (from_ to_ : Coord) : Bool :=
  if hasStraightPath from_ to_ then
    isPathEmpty board (straightPathCoords from_ to_)
  else
    false

def isClearDiagonalPath (board : Board) (from_ to_ : Coord) : Bool :=
  if hasDiagonalPath from_ to_ then
    isPathEmpty board (diagonalPathCoords from_ to_)
  else
    false


structure PieceOnBoard where
  piece : Piece
  coord : Coord

def getPieces (board : Board) (color : Color) : List PieceOnBoard :=
  let allCoords := (List.range 8).flatMap (fun r =>
    (List.range 8).map (fun f => (f, r))
  )

  -- We filterMap: Try to convert (f,r) to a piece.
  -- If it exists and matches the color, keep it.
  allCoords.filterMap fun (f, r) =>
    -- We can verify bounds here since we generated them from range 8
    if hf : f < 8 then
      if hr : r < 8 then
        let c : Coord := {
          file := Coord.fileFromOrd f hf,
          rank := Coord.rankFromOrd r hr
        }
        match getPiece board c with
        | some p => if p.color == color then some { piece := p, coord := c } else none
        | none   => none
      else
        none
    else
      none


-- 2. Pawn Logic
-- We MUST know the color, because White attacks 'Up' and Black attacks 'Down'.
def squaresThreatenedByPawn (coord : Coord) (color : Color) : List Coord :=
  let f : Int := Coord.file_ord coord
  let r : Int := Coord.rank_ord coord

  -- Determine direction based on color
  let rankDir : Int := match color with
    | .white => 1  -- White moves up indices (0 -> 7)
    | .black => -1 -- Black moves down indices (7 -> 0)

  let targetRank := r + rankDir

  -- Pawns capture on adjacent files (f-1 and f+1)
  let targetFiles := [f - 1, f + 1]

  -- 'filterMap' runs intToCoord on the list and keeps only the valid ones
  targetFiles.filterMap (fun targetFile => intToCoord targetFile targetRank)


-- 3. Knight Logic
-- Knights move in an "L" shape (2 steps one way, 1 step the other)
def squaresThreatenedByKnight (coord : Coord) : List Coord :=
  let f : Int := Coord.file_ord coord
  let r : Int := Coord.rank_ord coord

  -- All 8 possible L-shape jumps (File Delta, Rank Delta)
  let jumps : List (Int × Int) := [
    (1,  2), (-1,  2),  -- Up 2, Left/Right 1
    (1, -2), (-1, -2),  -- Down 2, Left/Right 1
    (2,  1), (2, -1),   -- Right 2, Up/Down 1
    (-2, 1), (-2, -1)   -- Left 2, Up/Down 1
  ]

  jumps.filterMap fun (df, dr) =>
    intToCoord (f + df) (r + dr)


def squareThreatened (board : Board) (target : Coord) (byColor : Color) : Bool :=
  -- 1. Get all enemy pieces
  let attackers := getPieces board byColor

  -- 2. Check if ANY of them attack the target
  attackers.any fun attacker =>
    let start := attacker.coord

    match attacker.piece.pieceType with
    | .rook =>
        isClearStraightPath board start target

    | .bishop =>
        isClearDiagonalPath board start target

    | .queen =>
        isClearStraightPath board start target ||
        isClearDiagonalPath board start target

    | .knight =>
        -- Check if 'target' is in the list of squares this knight hits
        (squaresThreatenedByKnight start).contains target

    | .pawn =>
        -- Check if 'target' is in the list of squares this pawn hits
        (squaresThreatenedByPawn start byColor).contains target

    | .king =>
        -- King attacks if distance in both Rank and File is <= 1
        let df := (Coord.file_ord start : Int) - (Coord.file_ord target : Int)
        let dr := (Coord.rank_ord start : Int) - (Coord.rank_ord target : Int)
        let distF := df.natAbs
        let distR := dr.natAbs
        -- Must be adjacent (distance <= 1) but not the same square
        (distF ≤ 1 && distR ≤ 1) && (distF + distR > 0)


-- Find king position (returns Option to handle missing king gracefully)
def findKing (board : Board) (color : Color) : Option Coord :=
  let kings := (getPieces board color).filter (fun p => p.piece.pieceType == .king)
  match kings with
  | [] => none
  | k :: _ => some k.coord

def oppColor (color: Color) : Color :=
  match color with
  | .white => .black
  | .black => .white

-- Check if a player is in check (returns false if king not found)
def isCheck (board: Board) (color: Color) : Bool :=
  match findKing board color with
  | some kingCoord => squareThreatened board kingCoord (oppColor color)
  | none => false  -- No king means can't be in check

-- =============================================================================
-- MOVES
-- =============================================================================

inductive Result : Type
  | inProgress | whiteWin | blackWin | draw
  deriving Repr, DecidableEq

inductive Move : Type
  | standard : Coord → Coord → Move
  | promotion : Coord → Coord → PieceType → Move
  | castle : castleSide → Move
  | enPassant : Coord → Coord → Coord → Move
  | resign : Move
  deriving Repr

structure BoardState where
  board: Board
  turnColor: Color
  result: Result
  history: List Move
  whiteCastleKingSide: Bool
  whiteCastleQueenSide: Bool
  blackCastleKingSide: Bool
  blackCastleQueenSide: Bool
  enPassantTarget: Option Coord
  halfMoveClock: Nat  -- For fifty-move rule (resets on pawn move or capture)
  positionHashes: List Nat  -- Zobrist hashes for threefold repetition detection

-- =============================================================================
-- BOARD SETUP
-- =============================================================================

def emptyBoard : Board :=
  { data := fun _ _ => none }

def setPiece (board : Board) (c : Coord) (p : Option Piece) : Board :=
  { data := fun f r =>
      if f.val == Coord.file_ord c ∧ r.val == Coord.rank_ord c then
        p
      else
        board.data f r
  }

def initialBoard : Board :=
  let b := emptyBoard
  -- White pieces (rank 0 and 1)
  let b := setPiece b {file := .A, rank := ._1} (some {pieceType := .rook, color := .white})
  let b := setPiece b {file := .B, rank := ._1} (some {pieceType := .knight, color := .white})
  let b := setPiece b {file := .C, rank := ._1} (some {pieceType := .bishop, color := .white})
  let b := setPiece b {file := .D, rank := ._1} (some {pieceType := .queen, color := .white})
  let b := setPiece b {file := .E, rank := ._1} (some {pieceType := .king, color := .white})
  let b := setPiece b {file := .F, rank := ._1} (some {pieceType := .bishop, color := .white})
  let b := setPiece b {file := .G, rank := ._1} (some {pieceType := .knight, color := .white})
  let b := setPiece b {file := .H, rank := ._1} (some {pieceType := .rook, color := .white})
  let b := setPiece b {file := .A, rank := ._2} (some {pieceType := .pawn, color := .white})
  let b := setPiece b {file := .B, rank := ._2} (some {pieceType := .pawn, color := .white})
  let b := setPiece b {file := .C, rank := ._2} (some {pieceType := .pawn, color := .white})
  let b := setPiece b {file := .D, rank := ._2} (some {pieceType := .pawn, color := .white})
  let b := setPiece b {file := .E, rank := ._2} (some {pieceType := .pawn, color := .white})
  let b := setPiece b {file := .F, rank := ._2} (some {pieceType := .pawn, color := .white})
  let b := setPiece b {file := .G, rank := ._2} (some {pieceType := .pawn, color := .white})
  let b := setPiece b {file := .H, rank := ._2} (some {pieceType := .pawn, color := .white})
  -- Black pieces (rank 6 and 7)
  let b := setPiece b {file := .A, rank := ._7} (some {pieceType := .pawn, color := .black})
  let b := setPiece b {file := .B, rank := ._7} (some {pieceType := .pawn, color := .black})
  let b := setPiece b {file := .C, rank := ._7} (some {pieceType := .pawn, color := .black})
  let b := setPiece b {file := .D, rank := ._7} (some {pieceType := .pawn, color := .black})
  let b := setPiece b {file := .E, rank := ._7} (some {pieceType := .pawn, color := .black})
  let b := setPiece b {file := .F, rank := ._7} (some {pieceType := .pawn, color := .black})
  let b := setPiece b {file := .G, rank := ._7} (some {pieceType := .pawn, color := .black})
  let b := setPiece b {file := .H, rank := ._7} (some {pieceType := .pawn, color := .black})
  let b := setPiece b {file := .A, rank := ._8} (some {pieceType := .rook, color := .black})
  let b := setPiece b {file := .B, rank := ._8} (some {pieceType := .knight, color := .black})
  let b := setPiece b {file := .C, rank := ._8} (some {pieceType := .bishop, color := .black})
  let b := setPiece b {file := .D, rank := ._8} (some {pieceType := .queen, color := .black})
  let b := setPiece b {file := .E, rank := ._8} (some {pieceType := .king, color := .black})
  let b := setPiece b {file := .F, rank := ._8} (some {pieceType := .bishop, color := .black})
  let b := setPiece b {file := .G, rank := ._8} (some {pieceType := .knight, color := .black})
  let b := setPiece b {file := .H, rank := ._8} (some {pieceType := .rook, color := .black})
  b

def initialState : BoardState :=
  { board := initialBoard
    turnColor := .white
    result := .inProgress
    history := []
    whiteCastleKingSide := true
    whiteCastleQueenSide := true
    blackCastleKingSide := true
    blackCastleQueenSide := true
    enPassantTarget := none
    halfMoveClock := 0
    positionHashes := []
  }

-- =============================================================================
-- MOVE VALIDATION
-- =============================================================================

def canPieceMove (board : Board) (piece : Piece) (fromCoord toCoord : Coord) : Bool :=
  match piece.pieceType with
  | .pawn =>
      let forward := if piece.color == .white then 1 else -1
      let fromR : Int := Coord.rank_ord fromCoord
      let toR : Int := Coord.rank_ord toCoord
      let fromF : Int := Coord.file_ord fromCoord
      let toF : Int := Coord.file_ord toCoord
      let startRank := if piece.color == .white then 1 else 6

      -- Forward one square
      if fromF == toF && toR == fromR + forward && (getPiece board toCoord).isNone then
        true
      -- Forward two squares from starting position (must check intermediate square!)
      else if fromF == toF && Coord.rank_ord fromCoord == startRank &&
              toR == fromR + 2 * forward && (getPiece board toCoord).isNone then
        -- Check intermediate square is also empty
        let intermediateRankNat := (fromR + forward).toNat
        if h : intermediateRankNat < 8 then
          let intermediateRank := Coord.rankFromOrd intermediateRankNat h
          let intermediate := {file := fromCoord.file, rank := intermediateRank}
          (getPiece board intermediate).isNone
        else
          false
      -- Capture diagonally
      else if (toF == fromF + 1 || toF == fromF - 1) && toR == fromR + forward then
        match getPiece board toCoord with
        | some p => p.color != piece.color
        | none => false
      else
        false

  | .knight =>
      (squaresThreatenedByKnight fromCoord).contains toCoord

  | .bishop =>
      isClearDiagonalPath board fromCoord toCoord

  | .rook =>
      isClearStraightPath board fromCoord toCoord

  | .queen =>
      isClearStraightPath board fromCoord toCoord || isClearDiagonalPath board fromCoord toCoord

  | .king =>
      let df := ((Coord.file_ord fromCoord : Int) - (Coord.file_ord toCoord : Int)).natAbs
      let dr := ((Coord.rank_ord fromCoord : Int) - (Coord.rank_ord toCoord : Int)).natAbs
      (df ≤ 1 && dr ≤ 1) && (df + dr > 0)

-- Generate all possible destination squares for all pieces of a color
def generateAllPseudoLegalMoves (board : Board) (color : Color) : List Move :=
  let pieces := getPieces board color
  pieces.flatMap fun pieceOnBoard =>
    let fromCoord := pieceOnBoard.coord
    -- Generate all possible destination squares
    let allSquares : List Coord := (List.range 8).flatMap fun r =>
      (List.range 8).filterMap fun f =>
        if hf : f < 8 then
          if hr : r < 8 then
            some {file := Coord.fileFromOrd f hf, rank := Coord.rankFromOrd r hr}
          else none
        else none
    -- Filter to valid moves for this piece
    allSquares.filterMap fun toCoord =>
      if fromCoord != toCoord && canPieceMove board pieceOnBoard.piece fromCoord toCoord then
        -- Check destination is valid (empty or opponent)
        match getPiece board toCoord with
        | some destPiece =>
            if destPiece.color != color then some (Move.standard fromCoord toCoord) else none
        | none => some (Move.standard fromCoord toCoord)
      else none

-- Check if a move would leave the moving player's king in check
def leavesKingInCheck (state : BoardState) (move : Move) : Bool :=
  match move with
  | .standard fromCoord toCoord =>
      -- Simulate the move
      match getPiece state.board fromCoord with
      | none => false
      | some piece =>
          let tempBoard := setPiece (setPiece state.board fromCoord none) toCoord (some piece)
          isCheck tempBoard piece.color
  | .promotion fromCoord toCoord promoteTo =>
      -- Simulate the promotion
      match getPiece state.board fromCoord with
      | none => false
      | some piece =>
          let promotedPiece := {pieceType := promoteTo, color := piece.color}
          let tempBoard := setPiece (setPiece state.board fromCoord none) toCoord (some promotedPiece)
          isCheck tempBoard piece.color
  | .enPassant fromCoord toCoord capturedSquare =>
      -- Simulate en passant
      match getPiece state.board fromCoord with
      | none => false
      | some piece =>
          let tempBoard := setPiece (setPiece (setPiece state.board fromCoord none) toCoord (some piece)) capturedSquare none
          isCheck tempBoard piece.color
  | _ => false

-- Generate all legal moves (doesn't leave king in check)
def generateLegalMoves (state : BoardState) : List Move :=
  let pseudoLegal := generateAllPseudoLegalMoves state.board state.turnColor
  pseudoLegal.filter fun move => not (leavesKingInCheck state move)

-- Check if player has any legal moves
def hasLegalMoves (state : BoardState) : Bool :=
  not (generateLegalMoves state).isEmpty

-- Checkmate: in check and no legal moves
def isCheckmate (state : BoardState) : Bool :=
  isCheck state.board state.turnColor && not (hasLegalMoves state)

-- Stalemate: not in check but no legal moves
def isStalemate (state : BoardState) : Bool :=
  not (isCheck state.board state.turnColor) && not (hasLegalMoves state)

-- =============================================================================
-- ZOBRIST HASHING FOR THREEFOLD REPETITION
-- =============================================================================

-- Simple pseudo-random number generator for Zobrist hashing
-- Uses a linear congruential generator: next = (a * seed + c) mod m
def lcgNext (seed : Nat) : Nat :=
  -- Parameters from Numerical Recipes
  let a := 1664525
  let c := 1013904223
  let m := 2^32
  (a * seed + c) % m

-- Generate a sequence of pseudo-random numbers
partial def generateRandoms (seed count : Nat) : List Nat :=
  let rec go (s : Nat) (n : Nat) (acc : List Nat) : List Nat :=
    if n == 0 then acc.reverse
    else
      let next := lcgNext s
      go next (n - 1) (next :: acc)
  go seed count []

-- Zobrist hash table: pre-computed random numbers for each piece/square/feature
-- We need: 12 piece types × 64 squares + 4 castling rights + 8 en passant files + 1 turn
def zobristSeed : Nat := 42  -- Arbitrary seed for reproducibility
def zobristTable : List Nat := generateRandoms zobristSeed (12 * 64 + 4 + 8 + 1)

-- Get Zobrist value for a piece at a square
def zobristPieceSquare (piece : Piece) (coord : Coord) : Nat :=
  let pieceIndex := match piece.color, piece.pieceType with
    | .white, .pawn   => 0
    | .white, .knight => 1
    | .white, .bishop => 2
    | .white, .rook   => 3
    | .white, .queen  => 4
    | .white, .king   => 5
    | .black, .pawn   => 6
    | .black, .knight => 7
    | .black, .bishop => 8
    | .black, .rook   => 9
    | .black, .queen  => 10
    | .black, .king   => 11
  let squareIndex := Coord.rank_ord coord * 8 + Coord.file_ord coord
  let index := pieceIndex * 64 + squareIndex
  zobristTable.getD index 0

-- Get Zobrist values for castling rights
def zobristCastling (wks wqs bks bqs : Bool) : Nat :=
  let base := 12 * 64
  let hash := 0
  let hash := if wks then hash ^^^ (zobristTable.getD base 0) else hash
  let hash := if wqs then hash ^^^ (zobristTable.getD (base + 1) 0) else hash
  let hash := if bks then hash ^^^ (zobristTable.getD (base + 2) 0) else hash
  let hash := if bqs then hash ^^^ (zobristTable.getD (base + 3) 0) else hash
  hash

-- Get Zobrist value for en passant file
def zobristEnPassant (target : Option Coord) : Nat :=
  match target with
  | none => 0
  | some coord =>
      let base := 12 * 64 + 4
      let fileIndex := Coord.file_ord coord
      zobristTable.getD (base + fileIndex) 0

-- Get Zobrist value for turn
def zobristTurn (color : Color) : Nat :=
  if color == .black then
    zobristTable.getD (12 * 64 + 4 + 8) 0
  else
    0

-- Compute full Zobrist hash for a position
def zobristHash (state : BoardState) : Nat :=
  -- Hash all pieces on the board
  let pieces := (List.range 8).flatMap fun r =>
    (List.range 8).filterMap fun f =>
      if hf : f < 8 then
        if hr : r < 8 then
          let coord := {file := Coord.fileFromOrd f hf, rank := Coord.rankFromOrd r hr}
          match getPiece state.board coord with
          | some piece => some (zobristPieceSquare piece coord)
          | none => none
        else none
      else none

  let pieceHash := pieces.foldl (· ^^^ ·) 0

  -- Combine with castling rights
  let castlingHash := zobristCastling
    state.whiteCastleKingSide
    state.whiteCastleQueenSide
    state.blackCastleKingSide
    state.blackCastleQueenSide

  -- Combine with en passant
  let epHash := zobristEnPassant state.enPassantTarget

  -- Combine with turn
  let turnHash := zobristTurn state.turnColor

  pieceHash ^^^ castlingHash ^^^ epHash ^^^ turnHash

-- Check for threefold repetition
def isThreefoldRepetition (state : BoardState) : Bool :=
  let currentHash := zobristHash state
  let count := state.positionHashes.filter (· == currentHash) |>.length
  count >= 2  -- Current position + 2 previous occurrences = 3 total

-- Helper to add current position hash to state
def addPositionHash (state : BoardState) : BoardState :=
  let hash := zobristHash state
  { state with positionHashes := hash :: state.positionHashes }

def isValidMove (state : BoardState) (move : Move) : Bool :=
  match move with
  | .standard fromCoord toCoord =>
      match getPiece state.board fromCoord with
      | none => false
      | some piece =>
          if piece.color != state.turnColor then false
          else
            -- Check destination is empty or has opponent piece
            let destOk := match getPiece state.board toCoord with
              | some destPiece => destPiece.color != piece.color
              | none => true
            -- Check piece can move there and doesn't leave king in check
            destOk &&
            canPieceMove state.board piece fromCoord toCoord &&
            not (leavesKingInCheck state move)
  | .promotion fromCoord toCoord promoteTo =>
      match getPiece state.board fromCoord with
      | none => false
      | some piece =>
          if piece.color != state.turnColor then false
          else if piece.pieceType != .pawn then false
          else
            -- Check pawn is moving to last rank
            let lastRank := if piece.color == .white then 7 else 0
            if Coord.rank_ord toCoord != lastRank then false
            else
              -- Check promotion piece is valid (not king or pawn)
              if promoteTo == .king || promoteTo == .pawn then false
              else
                -- Check the move is valid pawn movement
                let destOk := match getPiece state.board toCoord with
                  | some destPiece => destPiece.color != piece.color
                  | none => true
                destOk &&
                canPieceMove state.board piece fromCoord toCoord &&
                not (leavesKingInCheck state move)
  | .castle side =>
      let color := state.turnColor
      let rank := if color == .white then 0 else 7
      -- Check castling rights
      let hasRight := match color, side with
        | .white, .kingSide => state.whiteCastleKingSide
        | .white, .queenSide => state.whiteCastleQueenSide
        | .black, .kingSide => state.blackCastleKingSide
        | .black, .queenSide => state.blackCastleQueenSide
      if not hasRight then false
      else
        -- Check king is not in check
        if isCheck state.board color then false
        else
          -- Check squares between king and rook are empty
          let passFiles := match side with
            | .kingSide => [5, 6]  -- F and G
            | .queenSide => [1, 2, 3]  -- B, C, D
          let allClear := passFiles.all fun f =>
            if hf : f < 8 then
              if hr : rank < 8 then
                let coord := {file := Coord.fileFromOrd f hf, rank := Coord.rankFromOrd rank hr}
                (getPiece state.board coord).isNone
              else false
            else false
          if not allClear then false
          else
            -- Check king doesn't pass through or land on attacked square
            let kingPassSquares := match side with
              | .kingSide => [4, 5, 6]  -- E, F, G
              | .queenSide => [4, 3, 2]  -- E, D, C
            kingPassSquares.all fun f =>
              if hf : f < 8 then
                if hr : rank < 8 then
                  let coord := {file := Coord.fileFromOrd f hf, rank := Coord.rankFromOrd rank hr}
                  not (squareThreatened state.board coord (oppColor color))
                else false
              else false
  | .enPassant fromCoord toCoord _capturedSquare =>
      match getPiece state.board fromCoord with
      | none => false
      | some piece =>
          if piece.color != state.turnColor then false
          else if piece.pieceType != .pawn then false
          else
            -- Check en passant target matches
            match state.enPassantTarget with
            | none => false
            | some target =>
                if toCoord != target then false
                else
                  -- Check the move is a valid diagonal pawn move
                  let fromF : Int := Coord.file_ord fromCoord
                  let toF : Int := Coord.file_ord toCoord
                  let fromR : Int := Coord.rank_ord fromCoord
                  let toR : Int := Coord.rank_ord toCoord
                  let forward := if piece.color == .white then 1 else -1
                  (toF == fromF + 1 || toF == fromF - 1) &&
                  toR == fromR + forward &&
                  not (leavesKingInCheck state move)
  | .resign => true


-- =============================================================================
-- APPLY MOVE
-- =============================================================================

-- Helper to update castling rights based on piece movement
def updateCastlingRights (state : BoardState) (piece : Piece) (fromCoord : Coord) : BoardState :=
  let loseCastling :=
    -- If king moves, lose both sides
    if piece.pieceType == .king then
      match piece.color with
      | .white => {state with whiteCastleKingSide := false, whiteCastleQueenSide := false}
      | .black => {state with blackCastleKingSide := false, blackCastleQueenSide := false}
    -- If rook moves from starting position, lose that side
    else if piece.pieceType == .rook then
      let fileOrd := Coord.file_ord fromCoord
      let rankOrd := Coord.rank_ord fromCoord
      if piece.color == .white && rankOrd == 0 then
        if fileOrd == 0 then {state with whiteCastleQueenSide := false}
        else if fileOrd == 7 then {state with whiteCastleKingSide := false}
        else state
      else if piece.color == .black && rankOrd == 7 then
        if fileOrd == 0 then {state with blackCastleQueenSide := false}
        else if fileOrd == 7 then {state with blackCastleKingSide := false}
        else state
      else state
    else state
  loseCastling

def applyMove (state : BoardState) (move : Move) : BoardState :=
  match move with
  | .standard fromCoord toCoord =>
      match getPiece state.board fromCoord with
      | none => state  -- Invalid move, return unchanged
      | some piece =>
          let isCapture := (getPiece state.board toCoord).isSome
          let isPawnMove := piece.pieceType == .pawn
          let newBoard := setPiece (setPiece state.board fromCoord none) toCoord (some piece)

          -- Set en passant target if pawn moved two squares
          let newEnPassant :=
            if isPawnMove then
              let fromR : Int := Coord.rank_ord fromCoord
              let toR : Int := Coord.rank_ord toCoord
              if (toR - fromR).natAbs == 2 then
                -- En passant target is the square the pawn passed over
                let passedRank := ((fromR + toR) / 2).toNat
                if h : passedRank < 8 then
                  some {file := fromCoord.file, rank := Coord.rankFromOrd passedRank h}
                else none
              else none
            else none

          let stateWithRights := updateCastlingRights state piece fromCoord
          let newState := { stateWithRights with
            board := newBoard
            turnColor := oppColor state.turnColor
            history := move :: state.history
            enPassantTarget := newEnPassant
            halfMoveClock := if isPawnMove || isCapture then 0 else state.halfMoveClock + 1
          }
          let newStateWithHash := addPositionHash newState
          -- Check for game-ending conditions
          if isCheckmate newStateWithHash then
            let winner := if newStateWithHash.turnColor == .white then Result.blackWin else Result.whiteWin
            { newStateWithHash with result := winner }
          else if isStalemate newStateWithHash then
            { newStateWithHash with result := Result.draw }
          else if newStateWithHash.halfMoveClock >= 100 then  -- 50-move rule
            { newStateWithHash with result := Result.draw }
          else if isThreefoldRepetition newStateWithHash then
            { newStateWithHash with result := Result.draw }
          else
            newStateWithHash
  | .promotion fromCoord toCoord promoteTo =>
      match getPiece state.board fromCoord with
      | none => state
      | some piece =>
          let promotedPiece := {pieceType := promoteTo, color := piece.color}
          let newBoard := setPiece (setPiece state.board fromCoord none) toCoord (some promotedPiece)
          let stateWithRights := updateCastlingRights state piece fromCoord
          let newState := { stateWithRights with
            board := newBoard
            turnColor := oppColor state.turnColor
            history := move :: state.history
            enPassantTarget := none
            halfMoveClock := 0  -- Pawn move resets clock
          }
          let newStateWithHash := addPositionHash newState
          if isCheckmate newStateWithHash then
            let winner := if newStateWithHash.turnColor == .white then Result.blackWin else Result.whiteWin
            { newStateWithHash with result := winner }
          else if isStalemate newStateWithHash then
            { newStateWithHash with result := Result.draw }
          else if isThreefoldRepetition newStateWithHash then
            { newStateWithHash with result := Result.draw }
          else
            newStateWithHash
  | .castle side =>
      let color := state.turnColor
      let rank := if color == .white then 0 else 7
      if hr : rank < 8 then
        let (kingFrom, kingTo, rookFrom, rookTo) := match side with
          | .kingSide => (4, 6, 7, 5)   -- E→G, H→F
          | .queenSide => (4, 2, 0, 3)  -- E→C, A→D
        if hkf : kingFrom < 8 then if hkt : kingTo < 8 then
          if hrf : rookFrom < 8 then if hrt : rookTo < 8 then
            let kingFromCoord := {file := Coord.fileFromOrd kingFrom hkf, rank := Coord.rankFromOrd rank hr}
            let kingToCoord := {file := Coord.fileFromOrd kingTo hkt, rank := Coord.rankFromOrd rank hr}
            let rookFromCoord := {file := Coord.fileFromOrd rookFrom hrf, rank := Coord.rankFromOrd rank hr}
            let rookToCoord := {file := Coord.fileFromOrd rookTo hrt, rank := Coord.rankFromOrd rank hr}

            let king := {pieceType := .king, color := color}
            let rook := {pieceType := .rook, color := color}
            let newBoard := setPiece (setPiece (setPiece (setPiece state.board kingFromCoord none) rookFromCoord none) kingToCoord (some king)) rookToCoord (some rook)

            -- Lose castling rights
            let newState := match color with
              | .white => { state with
                  board := newBoard
                  turnColor := oppColor state.turnColor
                  history := move :: state.history
                  whiteCastleKingSide := false
                  whiteCastleQueenSide := false
                  enPassantTarget := none
                  halfMoveClock := state.halfMoveClock + 1
                }
              | .black => { state with
                  board := newBoard
                  turnColor := oppColor state.turnColor
                  history := move :: state.history
                  blackCastleKingSide := false
                  blackCastleQueenSide := false
                  enPassantTarget := none
                  halfMoveClock := state.halfMoveClock + 1
                }
            let newStateWithHash := addPositionHash newState
            if isCheckmate newStateWithHash then
              let winner := if newStateWithHash.turnColor == .white then Result.blackWin else Result.whiteWin
              { newStateWithHash with result := winner }
            else if isStalemate newStateWithHash then
              { newStateWithHash with result := Result.draw }
            else if newStateWithHash.halfMoveClock >= 100 then
              { newStateWithHash with result := Result.draw }
            else if isThreefoldRepetition newStateWithHash then
              { newStateWithHash with result := Result.draw }
            else
              newStateWithHash
          else state else state
        else state else state
      else state
  | .enPassant fromCoord toCoord capturedSquare =>
      match getPiece state.board fromCoord with
      | none => state
      | some piece =>
          let newBoard := setPiece (setPiece (setPiece state.board fromCoord none) toCoord (some piece)) capturedSquare none
          let newState := { state with
            board := newBoard
            turnColor := oppColor state.turnColor
            history := move :: state.history
            enPassantTarget := none
            halfMoveClock := 0  -- Pawn move resets clock
          }
          let newStateWithHash := addPositionHash newState
          if isCheckmate newStateWithHash then
            let winner := if newStateWithHash.turnColor == .white then Result.blackWin else Result.whiteWin
            { newStateWithHash with result := winner }
          else if isStalemate newStateWithHash then
            { newStateWithHash with result := Result.draw }
          else if isThreefoldRepetition newStateWithHash then
            { newStateWithHash with result := Result.draw }
          else
            newStateWithHash
  | .resign =>
      let winner := if state.turnColor == .white then Result.blackWin else Result.whiteWin
      { state with result := winner, history := move :: state.history }


-- =============================================================================
-- INPUT PARSING
-- =============================================================================

-- Parse file character to File
def parseFile (c : Char) : Option File :=
  match c with
  | 'a' | 'A' => some .A
  | 'b' | 'B' => some .B
  | 'c' | 'C' => some .C
  | 'd' | 'D' => some .D
  | 'e' | 'E' => some .E
  | 'f' | 'F' => some .F
  | 'g' | 'G' => some .G
  | 'h' | 'H' => some .H
  | _ => none

-- Parse rank character to Rank
def parseRank (c : Char) : Option Rank :=
  match c with
  | '1' => some ._1
  | '2' => some ._2
  | '3' => some ._3
  | '4' => some ._4
  | '5' => some ._5
  | '6' => some ._6
  | '7' => some ._7
  | '8' => some ._8
  | _ => none

-- Parse coordinate like "e4"
def parseCoord (s : String) : Option Coord :=
  let chars := s.toList
  match chars with
  | [fc, rc] =>
      match parseFile fc, parseRank rc with
      | some f, some r => some { file := f, rank := r }
      | _, _ => none
  | _ => none

-- Parse promotion piece (q/r/b/n)
def parsePromotionPiece (c : Char) : Option PieceType :=
  match c with
  | 'q' | 'Q' => some .queen
  | 'r' | 'R' => some .rook
  | 'b' | 'B' => some .bishop
  | 'n' | 'N' => some .knight
  | _ => none

-- Parse simple move like "e2e4" or "e2-e4" or "e7e8q" (promotion) or "O-O" (castling)
def parseSimpleMove (s : String) : Option Move :=
  -- Check for castling notation first
  if s == "O-O" || s == "0-0" then
    some (Move.castle .kingSide)
  else if s == "O-O-O" || s == "0-0-0" then
    some (Move.castle .queenSide)
  else if s == "resign" || s == "Resign" then
    some Move.resign
  else
    let s := s.replace "-" ""
    let s := s.replace "x" ""
    if s.length == 4 then
      match parseCoord (s.take 2), parseCoord (s.drop 2) with
      | some fromCoord, some toCoord => some (Move.standard fromCoord toCoord)
      | _, _ => none
    else if s.length == 5 then
      -- Check for promotion (e7e8q)
      let chars := s.toList
      match chars with
      | [_,_, _, _, promoChar] =>
          match parseCoord (s.take 2), parseCoord (s.drop 2 |>.take 2), parsePromotionPiece promoChar with
          | some fromCoord, some toCoord, some promoteTo =>
              some (Move.promotion fromCoord toCoord promoteTo)
          | _, _, _ => none
      | _ => none
    else
      none

-- =============================================================================
-- ALGEBRAIC NOTATION PARSER
-- =============================================================================

-- Parse piece type from character (K, Q, R, B, N)
def parsePieceType (c : Char) : Option PieceType :=
  match c with
  | 'K' => some .king
  | 'Q' => some .queen
  | 'R' => some .rook
  | 'B' => some .bishop
  | 'N' => some .knight
  | _ => none

-- Helper to check if a character is a file (a-h)
def isFileChar (c : Char) : Bool :=
  c == 'a' || c == 'b' || c == 'c' || c == 'd' ||
  c == 'e' || c == 'f' || c == 'g' || c == 'h'

-- Helper to check if a character is a rank (1-8)
def isRankChar (c : Char) : Bool :=
  c == '1' || c == '2' || c == '3' || c == '4' ||
  c == '5' || c == '6' || c == '7' || c == '8'

-- Structure to hold parsed algebraic notation components
structure AlgebraicMove where
  pieceType : Option PieceType  -- None for pawn moves
  fromFile : Option File        -- Disambiguator
  fromRank : Option Nat         -- Disambiguator
  capture : Bool
  toFile : File
  toRank : Rank
  promotion : Option PieceType
  deriving Repr

-- Parse algebraic notation like "Nf3", "exd5", "Qh4e1", "e8=Q", etc.
def parseAlgebraic (s : String) : Option AlgebraicMove :=
  -- Remove check/checkmate indicators
  let s := s.replace "+" ""
  let s := s.replace "#" ""
  let s := s.trimRight

  if s.length < 2 then none
  else
    let chars := s.toList

    -- Check for castling (handled separately)
    if s == "O-O" || s == "0-0" || s == "O-O-O" || s == "0-0-0" then
      none  -- Castling is handled by parseSimpleMove
    else
      -- Parse from left to right
      let (pieceType, rest) :=
        match chars with
        | c :: cs =>
            match parsePieceType c with
            | some pt => (some pt, cs)
            | none => (none, chars)  -- Pawn move
        | [] => (none, [])

      -- Now parse the rest: [disambig]x?[dest][=piece]?
      -- Work backwards from the destination

      -- Check for promotion at the end (=Q or just Q)
      let (promotion, rest) :=
        match rest.reverse with
        | promoChar :: '=' :: rest' => (parsePromotionPiece promoChar, rest'.reverse)
        | promoChar :: rest' =>
            match parsePromotionPiece promoChar with
            | some pt => (some pt, rest'.reverse)
            | none => (none, rest)
        | [] => (none, rest)

      -- Last two characters should be destination (file + rank)
      if rest.length < 2 then none
      else
        -- Get last two characters safely
        let destChars := rest.reverse.take 2 |>.reverse
        match destChars with
        | [destFile, destRank] =>
            match parseFile destFile, parseRank destRank with
            | some toFile, some toRank =>
                -- Remove destination from rest
                let rest := rest.take (rest.length - 2)

                -- Check for capture 'x'
                let (capture, rest) :=
                  match rest.reverse with
                  | 'x' :: rest' => (true, rest'.reverse)
                  | _ => (false, rest)

                -- Remaining characters are disambiguators (file and/or rank)
                let (fromFile, fromRank) :=
                  match rest with
                  | [] => (none, none)
                  | [c] =>
                      if isFileChar c then (parseFile c, none)
                      else if isRankChar c then
                        match c.toString.toNat? with
                        | some n => (none, some (n - 1))
                        | none => (none, none)
                      else (none, none)
                  | [fc, rc] =>
                      let file := if isFileChar fc then parseFile fc else none
                      let rank := if isRankChar rc then
                        match rc.toString.toNat? with
                        | some n => some (n - 1)
                        | none => none
                      else none
                      (file, rank)
                  | _ => (none, none)

                some {
                  pieceType := pieceType
                  fromFile := fromFile
                  fromRank := fromRank
                  capture := capture
                  toFile := toFile
                  toRank := toRank
                  promotion := promotion
                }
            | _, _ => none
        | _ => none

-- Find the piece that can make this algebraic move
def findAlgebraicMove (state : BoardState) (alg : AlgebraicMove) : Option Move :=
  let color := state.turnColor
  let toCoord : Coord := { file := alg.toFile, rank := alg.toRank }

  -- Determine piece type to look for
  let searchPieceType := match alg.pieceType with
    | some pt => pt
    | none => .pawn  -- No piece indicator means pawn

  -- Get all pieces of this type and color
  let pieces := getPieces state.board color
  let candidates := pieces.filter fun p =>
    p.piece.pieceType == searchPieceType &&
    -- Apply disambiguators if present
    (match alg.fromFile with
     | some f => p.coord.file == f
     | none => true) &&
    (match alg.fromRank with
     | some r => Coord.rank_ord p.coord == r
     | none => true)

  -- Filter to pieces that can legally make this move
  let validCandidates := candidates.filter fun p =>
    let fromCoord := p.coord

    -- Check if piece can move to destination (canPieceMove handles path checking)
    if not (canPieceMove state.board p.piece fromCoord toCoord) then
      false
    else
      -- Check capture consistency
      match getPiece state.board toCoord with
      | some destPiece =>
          -- Must be capture move and must be opponent piece
          alg.capture && destPiece.color != color
      | none =>
          -- Special handling for pawn captures (en passant)
          if searchPieceType == .pawn && alg.capture then
            -- Check en passant
            some toCoord == state.enPassantTarget
          else
            -- Regular non-capture move
            not alg.capture

  -- Should have exactly one valid candidate
  match validCandidates with
  | [candidate] =>
      let fromCoord := candidate.coord

      -- Create the appropriate move
      let baseMove :=
        if searchPieceType == .pawn && some toCoord == state.enPassantTarget then
          -- En passant capture
          let capturedRank := if color == .white then 4 else 3
          if h : capturedRank < 8 then
            let capturedSquare := { file := alg.toFile, rank := Coord.rankFromOrd capturedRank h }
            Move.enPassant fromCoord toCoord capturedSquare
          else
            Move.standard fromCoord toCoord
        else if let some promoPiece := alg.promotion then
          Move.promotion fromCoord toCoord promoPiece
        else
          Move.standard fromCoord toCoord

      -- Verify the move is legal (doesn't leave king in check)
      if isValidMove state baseMove then
        some baseMove
      else
        none
  | _ => none  -- Zero or multiple candidates = ambiguous or invalid

-- Main move parser that tries algebraic notation first, then falls back to coordinate notation
def parseMove (state : BoardState) (s : String) : Option Move :=
  -- Try castling first (works for both notations)
  if s == "O-O" || s == "0-0" then
    let move := Move.castle .kingSide
    if isValidMove state move then some move else none
  else if s == "O-O-O" || s == "0-0-0" then
    let move := Move.castle .queenSide
    if isValidMove state move then some move else none
  else if s == "resign" || s == "Resign" then
    some Move.resign
  else
    -- Try algebraic notation first
    match parseAlgebraic s with
    | some alg => findAlgebraicMove state alg
    | none =>
        -- Fall back to coordinate notation
        parseSimpleMove s

-- =============================================================================
-- IO / DISPLAY
-- =============================================================================

def pieceToUnicode (p : Piece) : String :=
  match p.color, p.pieceType with
  | .white, .king   => "♔"
  | .white, .queen  => "♕"
  | .white, .rook   => "♖"
  | .white, .bishop => "♗"
  | .white, .knight => "♘"
  | .white, .pawn   => "♙"
  | .black, .king   => "♚"
  | .black, .queen  => "♛"
  | .black, .rook   => "♜"
  | .black, .bishop => "♝"
  | .black, .knight => "♞"
  | .black, .pawn   => "♟"

def displayBoard (board : Board) : IO Unit := do
  IO.println ""
  IO.println "  ╔═══╤═══╤═══╤═══╤═══╤═══╤═══╤═══╗"
  for r in [7, 6, 5, 4, 3, 2, 1, 0] do
    let rank : Rank := match r with
      | 0 => ._1 | 1 => ._2 | 2 => ._3 | 3 => ._4
      | 4 => ._5 | 5 => ._6 | 6 => ._7 | _ => ._8
    IO.print s!"{r + 1} ║"
    for f in [0, 1, 2, 3, 4, 5, 6, 7] do
      let file : File := match f with
        | 0 => .A | 1 => .B | 2 => .C | 3 => .D
        | 4 => .E | 5 => .F | 6 => .G | _ => .H
      let coord : Coord := { file := file, rank := rank }
      match getPiece board coord with
      | some piece => IO.print s!" {pieceToUnicode piece} "
      | none =>
          -- Checkerboard pattern
          let isDark := (f + r) % 2 == 1
          if isDark then IO.print " · " else IO.print "   "
      if f < 7 then IO.print "│" else IO.print ""
    IO.println s!"║ {r + 1}"
    if r > 0 then
      IO.println "  ╟───┼───┼───┼───┼───┼───┼───┼───╢"
  IO.println "  ╚═══╧═══╧═══╧═══╧═══╧═══╧═══╧═══╝"
  IO.println "    a   b   c   d   e   f   g   h"
  IO.println ""

-- =============================================================================
-- GAME LOOP
-- =============================================================================

partial def gameLoop (state : BoardState) : IO Unit := do
  -- Check if game is over
  match state.result with
  | .whiteWin => IO.println "White wins!"
  | .blackWin => IO.println "Black wins!"
  | .draw => IO.println "Draw!"
  | .inProgress =>
      -- Display current state
      displayBoard state.board
      let colorName := if state.turnColor == .white then "White" else "Black"
      IO.println s!"{colorName} to move"
      IO.println "Enter move (e.g., 'e2e4' or 'e2-e4') or 'resign':"

      -- Get input
      let input ← (← IO.getStdin).getLine
      let input := input.trimRight.trimLeft

      -- Parse move
      match parseMove state input with
      | none =>
          IO.println "Invalid move format. Try again."
          gameLoop state
      | some move =>
          -- Validate move
          if isValidMove state move then
            let newState := applyMove state move
            gameLoop newState
          else
            IO.println "Invalid move. Try again."
            gameLoop state

def main : IO Unit := do
  IO.println "=== Chess Game ==="
  IO.println "Move format: e2e4 or e2-e4"
  IO.println "Type 'resign' to resign"
  IO.println ""
  gameLoop initialState

-- 2. **Path obstruction for sliding pieces** - Rooks, bishops, and queens can't jump over pieces. Your `canMoveToSquare` doesn't mention checking that the path is clear

-- 3. **Which rook** for castling - You have `Castle: Color, Side` but when you execute the move, you need to know where the rook actually is (and move it)

-- 4. **En passant target square tracking** - Your approach checks the previous move, which works, but many implementations explicitly track the en passant target square in board state (cleaner for threefold repetition comparison)

-- 5. **Threefold repetition comparison** - You mention it but don't define what constitutes "same position" (piece positions + castling rights + en passant square + whose turn)

-- 6. **Disambiguation in notation** - Your parser handles one piece able to move, but standard algebraic notation uses file/rank disambiguation (e.g., `Rab1`, `R1a3`, `Qh4e1`) when multiple pieces can reach the same square

-- 7. **Insufficient material draw** - K vs K, K+B vs K, K+N vs K, K+B vs K+B (same color bishops).
