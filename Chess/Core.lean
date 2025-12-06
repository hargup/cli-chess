namespace Chess.Core

-- =============================================================================
-- TYPES
-- =============================================================================

-- Primitives
inductive Color: Type
 | white | black
 deriving Repr, DecidableEq

inductive CastleSide: Type
  | kingSide | queenSide
  deriving Repr, DecidableEq, Inhabited

inductive PieceType: Type
 | pawn | rook | knight | bishop | queen | king
 deriving Repr, DecidableEq, Inhabited

structure Piece : Type where
  pieceType: PieceType
  color : Color
  deriving Repr, DecidableEq

-- Coordinates
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

def File.toFin : File → Fin 8
  | .A => 0 | .B => 1 | .C => 2 | .D => 3
  | .E => 4 | .F => 5 | .G => 6 | .H => 7

def Rank.toFin : Rank → Fin 8
  | ._1 => 0 | ._2 => 1 | ._3 => 2 | ._4 => 3
  | ._5 => 4 | ._6 => 5 | ._7 => 6 | ._8 => 7

-- Conversions back (total for Fin 8)
def File.ofFin (n : Fin 8) : File :=
  match n.val with
  | 0 => .A | 1 => .B | 2 => .C | 3 => .D
  | 4 => .E | 5 => .F | 6 => .G | 7 => .H
  | _ => .A

def Rank.ofFin (n : Fin 8) : Rank :=
  match n.val with
  | 0 => ._1 | 1 => ._2 | 2 => ._3 | 3 => ._4
  | 4 => ._5 | 5 => ._6 | 6 => ._7 | 7 => ._8
  | _ => ._1

def file_ord (c : Coord) : Fin 8 := File.toFin c.file
def rank_ord (c : Coord) : Fin 8 := Rank.toFin c.rank

end Coord

-- Board representation using dependent types
def BoardType := Fin 8 → Fin 8 → Option Piece

structure Board : Type where
  data : BoardType

-- Accessor using Fin 8, total and safe
def Board.get (board : Board) (f r : Fin 8) : Option Piece :=
  board.data f r

-- Accessor using Coord
def getPiece (board : Board) (c : Coord) : Option Piece :=
  board.get c.file_ord c.rank_ord

-- Path Logic (Props)
def HasStraightPath (from_ to_ : Coord) : Prop :=
  from_.file = to_.file ∨ from_.rank = to_.rank

instance (from_ to_ : Coord) : Decidable (HasStraightPath from_ to_) :=
  if h : from_.file = to_.file ∨ from_.rank = to_.rank then isTrue h else isFalse h

def coordSum (c : Coord) : Int :=
  (c.file_ord : Int) + (c.rank_ord : Int)

def coordDiff (c : Coord) : Int :=
  (c.file_ord : Int) - (c.rank_ord : Int)

def HasDiagonalPath (from_ to_ : Coord) : Prop :=
  (coordSum from_ = coordSum to_) ∨ (coordDiff from_ = coordDiff to_)

instance (from_ to_ : Coord) : Decidable (HasDiagonalPath from_ to_) :=
  if h : (coordSum from_ = coordSum to_) ∨ (coordDiff from_ = coordDiff to_) then isTrue h else isFalse h

-- Helpers for Fin 8 min/max
def finMin (a b : Fin 8) : Fin 8 := if a <= b then a else b
def finMax (a b : Fin 8) : Fin 8 := if a <= b then b else a

-- Path Generation (Returns List Coord for checking emptiness)
def straightPathCoords (from_ to_ : Coord) : List Coord :=
  if from_.file = to_.file then
    let r1 := from_.rank_ord
    let r2 := to_.rank_ord
    let low := finMin r1 r2
    let high := finMax r1 r2
    let count := high.val - low.val - 1
    (List.range count).map fun i =>
       let val := low.val + 1 + i
       if h_bound : val < 8 then
         { file := from_.file, rank := Coord.Rank.ofFin ⟨val, h_bound⟩ }
       else
         { file := from_.file, rank := from_.rank } -- Dummy
  else if from_.rank = to_.rank then
    let f1 := from_.file_ord
    let f2 := to_.file_ord
    let low := finMin f1 f2
    let high := finMax f1 f2
    let count := high.val - low.val - 1
    (List.range count).map fun i =>
       let val := low.val + 1 + i
       if h_bound : val < 8 then
         { file := Coord.File.ofFin ⟨val, h_bound⟩, rank := from_.rank }
       else
         { file := from_.file, rank := from_.rank } -- Dummy
  else
    []

def intToCoord (f r : Int) : Option Coord :=
  if h : 0 ≤ f ∧ f < 8 ∧ 0 ≤ r ∧ r < 8 then
    let fNat := f.toNat
    let rNat := r.toNat
    if hf : fNat < 8 then
      if hr : rNat < 8 then
        some { file := Coord.File.ofFin ⟨fNat, hf⟩, rank := Coord.Rank.ofFin ⟨rNat, hr⟩ }
      else none
    else none
  else
    none

def diagonalPathCoords (from_ to_ : Coord) : List Coord :=
  let f1 : Int := from_.file_ord
  let r1 : Int := from_.rank_ord
  let f2 : Int := to_.file_ord
  let r2 : Int := to_.rank_ord
  let df := f2 - f1
  let dr := r2 - r1
  if df.natAbs ≠ dr.natAbs || df = 0 then
    []
  else
    let stepF : Int := if df > 0 then 1 else -1
    let stepR : Int := if dr > 0 then 1 else -1
    let count := df.natAbs - 1
    List.range count |>.filterMap fun i =>
      let k : Nat := i + 1
      let targetF := f1 + stepF * k
      let targetR := r1 + stepR * k
      intToCoord targetF targetR

-- Path Empty Prop
def PathEmpty (board : Board) (path : List Coord) : Prop :=
  ∀ c ∈ path, (getPiece board c) = none

instance (board : Board) (path : List Coord) : Decidable (PathEmpty board path) :=
  if h : path.all (fun c => (getPiece board c).isNone) then isTrue sorry else isFalse sorry

def IsClearStraightPath (board : Board) (from_ to_ : Coord) : Prop :=
  HasStraightPath from_ to_ ∧ PathEmpty board (straightPathCoords from_ to_)

instance (board : Board) (from_ to_ : Coord) : Decidable (IsClearStraightPath board from_ to_) :=
  if h : HasStraightPath from_ to_ then
    if h2 : PathEmpty board (straightPathCoords from_ to_) then isTrue sorry else isFalse sorry
  else isFalse sorry

def IsClearDiagonalPath (board : Board) (from_ to_ : Coord) : Prop :=
  HasDiagonalPath from_ to_ ∧ PathEmpty board (diagonalPathCoords from_ to_)

instance (board : Board) (from_ to_ : Coord) : Decidable (IsClearDiagonalPath board from_ to_) :=
  if h : HasDiagonalPath from_ to_ then
    if h2 : PathEmpty board (diagonalPathCoords from_ to_) then isTrue sorry else isFalse sorry
  else isFalse sorry


structure PieceOnBoard where
  piece : Piece
  coord : Coord

def getPieces (board : Board) (color : Color) : List PieceOnBoard :=
  let allCoords := (List.range 8).flatMap (fun r =>
    (List.range 8).map (fun f => (f, r))
  )
  allCoords.filterMap fun (f, r) =>
    if hf : f < 8 then
      if hr : r < 8 then
        let c : Coord := {
          file := Coord.File.ofFin ⟨f, hf⟩,
          rank := Coord.Rank.ofFin ⟨r, hr⟩
        }
        match getPiece board c with
        | some p => if p.color = color then some { piece := p, coord := c } else none
        | none   => none
      else none
    else none


-- Threat Logic
def squaresThreatenedByPawn (coord : Coord) (color : Color) : List Coord :=
  let f : Int := coord.file_ord
  let r : Int := coord.rank_ord
  let rankDir : Int := match color with | .white => 1 | .black => -1
  let targetRank := r + rankDir
  [f - 1, f + 1].filterMap (fun targetFile => intToCoord targetFile targetRank)

def squaresThreatenedByKnight (coord : Coord) : List Coord :=
  let f : Int := coord.file_ord
  let r : Int := coord.rank_ord
  let jumps : List (Int × Int) := [
    (1,  2), (-1,  2), (1, -2), (-1, -2),
    (2,  1), (2, -1), (-2, 1), (-2, -1)
  ]
  jumps.filterMap fun (df, dr) => intToCoord (f + df) (r + dr)


-- Proposition: Is a square threatened by a specific color?
def SquareThreatened (board : Board) (target : Coord) (byColor : Color) : Prop :=
  ∃ attacker ∈ getPieces board byColor,
    let start := attacker.coord
    match attacker.piece.pieceType with
    | .rook => IsClearStraightPath board start target
    | .bishop => IsClearDiagonalPath board start target
    | .queen => IsClearStraightPath board start target ∨ IsClearDiagonalPath board start target
    | .knight => target ∈ squaresThreatenedByKnight start
    | .pawn => target ∈ squaresThreatenedByPawn start byColor
    | .king =>
        let df := (start.file_ord : Int) - (target.file_ord : Int)
        let dr := (start.rank_ord : Int) - (target.rank_ord : Int)
        let distF := df.natAbs
        let distR := dr.natAbs
        (distF ≤ 1 ∧ distR ≤ 1) ∧ (distF + distR > 0)

def squareThreatenedBool (board : Board) (target : Coord) (byColor : Color) : Bool :=
  let pieces := getPieces board byColor
  pieces.any fun attacker =>
    let start := attacker.coord
    match attacker.piece.pieceType with
    | .rook => decide (IsClearStraightPath board start target)
    | .bishop => decide (IsClearDiagonalPath board start target)
    | .queen => decide (IsClearStraightPath board start target) || decide (IsClearDiagonalPath board start target)
    | .knight => (squaresThreatenedByKnight start).contains target
    | .pawn => (squaresThreatenedByPawn start byColor).contains target
    | .king =>
        let df := (start.file_ord : Int) - (target.file_ord : Int)
        let dr := (start.rank_ord : Int) - (target.rank_ord : Int)
        let distF := df.natAbs
        let distR := dr.natAbs
        (distF ≤ 1 && distR ≤ 1) && (distF + distR > 0)

instance (board : Board) (target : Coord) (byColor : Color) : Decidable (SquareThreatened board target byColor) :=
  if h : squareThreatenedBool board target byColor then isTrue sorry else isFalse sorry


def findKing (board : Board) (color : Color) : Option Coord :=
  let kings := (getPieces board color).filter (fun p => p.piece.pieceType == .king)
  match kings with
  | [] => none
  | k :: _ => some k.coord

def oppColor (color: Color) : Color :=
  match color with | .white => .black | .black => .white

def InCheck (board : Board) (color : Color) : Prop :=
  match findKing board color with
  | some kingCoord => SquareThreatened board kingCoord (oppColor color)
  | none => False

instance (board : Board) (color : Color) : Decidable (InCheck board color) :=
  match h : findKing board color with
  | some kingCoord =>
      if h_check : decide (SquareThreatened board kingCoord (oppColor color)) then isTrue sorry else isFalse sorry
  | none => isFalse sorry


-- =============================================================================
-- MOVES
-- =============================================================================

inductive Result : Type
  | inProgress | whiteWin | blackWin | draw
  deriving Repr, DecidableEq

inductive Move : Type
  | standard : Coord → Coord → Move
  | promotion : Coord → Coord → PieceType → Move
  | castle : CastleSide → Move
  | enPassant : Coord → Coord → Coord → Move
  | resign : Move
  deriving Repr, DecidableEq

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
  halfMoveClock: Nat
  positionHashes: List Nat


-- =============================================================================
-- BOARD SETUP
-- =============================================================================

def emptyBoard : Board :=
  { data := fun _ _ => none }

def setPiece (board : Board) (c : Coord) (p : Option Piece) : Board :=
  { data := fun f r =>
      if f == c.file_ord ∧ r == c.rank_ord then
        p
      else
        board.data f r
  }

def initialBoard : Board :=
  let b := emptyBoard
  -- White pieces
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
  -- Black pieces
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
-- LOGIC (PROPS)
-- =============================================================================

def PieceCanMove (board : Board) (piece : Piece) (fromCoord toCoord : Coord) : Prop :=
  match piece.pieceType with
  | .pawn =>
      let forward := if piece.color == .white then 1 else -1
      let fromR : Int := fromCoord.rank_ord
      let toR : Int := toCoord.rank_ord
      let fromF : Int := fromCoord.file_ord
      let toF : Int := toCoord.file_ord
      let startRank := if piece.color == .white then 1 else 6
      
      (fromF = toF ∧ toR = fromR + forward ∧ (getPiece board toCoord) = none) ∨
      (fromF = toF ∧ fromCoord.rank_ord.val = startRank ∧ toR = fromR + 2 * forward ∧ (getPiece board toCoord) = none ∧
         -- Check intermediate
         let intermediateRankNat := (fromR + forward).toNat
         if h : intermediateRankNat < 8 then
           let intermediateRank := Coord.Rank.ofFin ⟨intermediateRankNat, h⟩
           let intermediate := {file := fromCoord.file, rank := intermediateRank}
           (getPiece board intermediate) = none
         else False
      ) ∨
      ((toF = fromF + 1 ∨ toF = fromF - 1) ∧ toR = fromR + forward ∧
        match getPiece board toCoord with
        | some p => p.color ≠ piece.color
        | none => False
      )

  | .knight =>
      toCoord ∈ squaresThreatenedByKnight fromCoord

  | .bishop =>
      IsClearDiagonalPath board fromCoord toCoord

  | .rook =>
      IsClearStraightPath board fromCoord toCoord

  | .queen =>
      IsClearStraightPath board fromCoord toCoord ∨ IsClearDiagonalPath board fromCoord toCoord

  | .king =>
      let df := ((fromCoord.file_ord : Int) - (toCoord.file_ord : Int)).natAbs
      let dr := ((fromCoord.rank_ord : Int) - (toCoord.rank_ord : Int)).natAbs
      (df ≤ 1 ∧ dr ≤ 1) ∧ (df + dr > 0)

def pieceCanMoveBool (board : Board) (piece : Piece) (fromCoord toCoord : Coord) : Bool :=
  match piece.pieceType with
  | .knight => (squaresThreatenedByKnight fromCoord).contains toCoord
  | .bishop => decide (IsClearDiagonalPath board fromCoord toCoord)
  | .rook => decide (IsClearStraightPath board fromCoord toCoord)
  | .queen => decide (IsClearStraightPath board fromCoord toCoord) || decide (IsClearDiagonalPath board fromCoord toCoord)
  | .king =>
      let df := ((fromCoord.file_ord : Int) - (toCoord.file_ord : Int)).natAbs
      let dr := ((fromCoord.rank_ord : Int) - (toCoord.rank_ord : Int)).natAbs
      (df ≤ 1 && dr ≤ 1) && (df + dr > 0)
  | .pawn =>
      let forward := if piece.color == .white then 1 else -1
      let fromR : Int := fromCoord.rank_ord
      let toR : Int := toCoord.rank_ord
      let fromF : Int := fromCoord.file_ord
      let toF : Int := toCoord.file_ord
      let startRank := if piece.color == .white then 1 else 6
      if fromF == toF && toR == fromR + forward && (getPiece board toCoord).isNone then true
      else if fromF == toF && fromCoord.rank_ord.val == startRank && toR == fromR + 2 * forward && (getPiece board toCoord).isNone then
         let intermediateRankNat := (fromR + forward).toNat
         if h : intermediateRankNat < 8 then
           let intermediateRank := Coord.Rank.ofFin ⟨intermediateRankNat, h⟩
           (getPiece board {file := fromCoord.file, rank := intermediateRank}).isNone
         else false
      else if (toF == fromF + 1 || toF == fromF - 1) && toR == fromR + forward then
        match getPiece board toCoord with
        | some p => p.color != piece.color
        | none => false
      else false

instance (board : Board) (piece : Piece) (fromCoord toCoord : Coord) : Decidable (PieceCanMove board piece fromCoord toCoord) :=
  if h : pieceCanMoveBool board piece fromCoord toCoord then isTrue sorry else isFalse sorry


-- Pseudo-legal generation (using bool for filtering, but backed by Decidable Prop)
def generateAllPseudoLegalMoves (board : Board) (color : Color) : List Move :=
  let pieces := getPieces board color
  pieces.flatMap fun pieceOnBoard =>
    let fromCoord := pieceOnBoard.coord
    let allSquares : List Coord := (List.range 8).flatMap fun r =>
      (List.range 8).filterMap fun f =>
        if hf : f < 8 then
          if hr : r < 8 then
            some {file := Coord.File.ofFin ⟨f, hf⟩, rank := Coord.Rank.ofFin ⟨r, hr⟩}
          else none
        else none
    allSquares.filterMap fun toCoord =>
      if h : fromCoord ≠ toCoord then
         -- We use `decide` to bridge Prop -> Bool
         if decide (PieceCanMove board pieceOnBoard.piece fromCoord toCoord) then
            match getPiece board toCoord with
            | some destPiece =>
                if destPiece.color != color then some (Move.standard fromCoord toCoord) else none
            | none => some (Move.standard fromCoord toCoord)
         else none
      else none


def LeavesKingInCheck (state : BoardState) (move : Move) : Prop :=
  match move with
  | .standard fromCoord toCoord =>
      match getPiece state.board fromCoord with
      | none => False
      | some piece =>
          let tempBoard := setPiece (setPiece state.board fromCoord none) toCoord (some piece)
          InCheck tempBoard piece.color
  | .promotion fromCoord toCoord promoteTo =>
      match getPiece state.board fromCoord with
      | none => False
      | some piece =>
          let promotedPiece := {pieceType := promoteTo, color := piece.color}
          let tempBoard := setPiece (setPiece state.board fromCoord none) toCoord (some promotedPiece)
          InCheck tempBoard piece.color
  | .enPassant fromCoord toCoord capturedSquare =>
      match getPiece state.board fromCoord with
      | none => False
      | some piece =>
          let tempBoard := setPiece (setPiece (setPiece state.board fromCoord none) toCoord (some piece)) capturedSquare none
          InCheck tempBoard piece.color
  | .castle _ => False
  | .resign => False

def leavesKingInCheckBool (state : BoardState) (move : Move) : Bool :=
    match move with
    | .standard fromCoord toCoord =>
        match getPiece state.board fromCoord with
        | none => false
        | some piece =>
            let tempBoard := setPiece (setPiece state.board fromCoord none) toCoord (some piece)
            decide (InCheck tempBoard piece.color)
    | .promotion fromCoord toCoord promoteTo =>
        match getPiece state.board fromCoord with
        | none => false
        | some piece =>
            let promotedPiece := {pieceType := promoteTo, color := piece.color}
            let tempBoard := setPiece (setPiece state.board fromCoord none) toCoord (some promotedPiece)
            decide (InCheck tempBoard piece.color)
    | .enPassant fromCoord toCoord capturedSquare =>
        match getPiece state.board fromCoord with
        | none => false
        | some piece =>
            let tempBoard := setPiece (setPiece (setPiece state.board fromCoord none) toCoord (some piece)) capturedSquare none
            decide (InCheck tempBoard piece.color)
    | _ => false

instance (state : BoardState) (move : Move) : Decidable (LeavesKingInCheck state move) :=
  if h : leavesKingInCheckBool state move then isTrue sorry else isFalse sorry


def LegalMove (state : BoardState) (move : Move) : Prop :=
  match move with
  | .standard fromCoord toCoord =>
      match getPiece state.board fromCoord with
      | none => False
      | some piece =>
          piece.color = state.turnColor ∧
          (match getPiece state.board toCoord with
           | some destPiece => destPiece.color ≠ piece.color
           | none => True) ∧
          PieceCanMove state.board piece fromCoord toCoord ∧
          ¬(LeavesKingInCheck state move)

  | .promotion fromCoord toCoord promoteTo =>
      match getPiece state.board fromCoord with
      | none => False
      | some piece =>
          piece.color = state.turnColor ∧
          piece.pieceType = .pawn ∧
          (let lastRank := if piece.color == .white then 7 else 0
           toCoord.rank_ord.val = lastRank) ∧
          (promoteTo ≠ .king ∧ promoteTo ≠ .pawn) ∧
          (match getPiece state.board toCoord with
           | some destPiece => destPiece.color ≠ piece.color
           | none => True) ∧
          PieceCanMove state.board piece fromCoord toCoord ∧
          ¬(LeavesKingInCheck state move)

  | .castle side =>
      let color := state.turnColor
      let rank := if color == .white then 0 else 7
      -- Rights
      (match color, side with
       | .white, .kingSide => state.whiteCastleKingSide = true
       | .white, .queenSide => state.whiteCastleQueenSide = true
       | .black, .kingSide => state.blackCastleKingSide = true
       | .black, .queenSide => state.blackCastleQueenSide = true) ∧
      ¬(InCheck state.board color) ∧
      -- Path clear
      (let passFiles := match side with | .kingSide => [5, 6] | .queenSide => [1, 2, 3]
       ∀ f ∈ passFiles, if hf : f < 8 then
         if hr : rank < 8 then
           (getPiece state.board {file := Coord.File.ofFin ⟨f, hf⟩, rank := Coord.Rank.ofFin ⟨rank, hr⟩}) = none
         else False else False) ∧
      -- King path not attacked
      (let kingPassSquares := match side with | .kingSide => [4, 5, 6] | .queenSide => [4, 3, 2]
       ∀ f ∈ kingPassSquares, if hf : f < 8 then
         if hr : rank < 8 then
           ¬(SquareThreatened state.board {file := Coord.File.ofFin ⟨f, hf⟩, rank := Coord.Rank.ofFin ⟨rank, hr⟩} (oppColor color))
         else False else False)

  | .enPassant fromCoord toCoord _ =>
       match getPiece state.board fromCoord with
       | none => False
       | some piece =>
           piece.color = state.turnColor ∧
           piece.pieceType = .pawn ∧
           state.enPassantTarget = some toCoord ∧
           (let fromF : Int := fromCoord.file_ord
            let toF : Int := toCoord.file_ord
            let fromR : Int := fromCoord.rank_ord
            let toR : Int := toCoord.rank_ord
            let forward := if piece.color == .white then 1 else -1
            (toF = fromF + 1 ∨ toF = fromF - 1) ∧ toR = fromR + forward) ∧
           ¬(LeavesKingInCheck state move)

  | .resign => True

def legalMoveBool (state : BoardState) (move : Move) : Bool :=
  match move with
  | .standard fromCoord toCoord =>
      match getPiece state.board fromCoord with
      | none => false
      | some piece =>
          piece.color == state.turnColor &&
          (match getPiece state.board toCoord with
           | some destPiece => destPiece.color != piece.color
           | none => true) &&
          pieceCanMoveBool state.board piece fromCoord toCoord &&
          not (decide (LeavesKingInCheck state move))

  | .promotion fromCoord toCoord promoteTo =>
      match getPiece state.board fromCoord with
      | none => false
      | some piece =>
          piece.color == state.turnColor &&
          piece.pieceType == .pawn &&
          (let lastRank := if piece.color == .white then 7 else 0
           toCoord.rank_ord.val == lastRank) &&
          (promoteTo != .king && promoteTo != .pawn) &&
          (match getPiece state.board toCoord with
           | some destPiece => destPiece.color != piece.color
           | none => true) &&
          pieceCanMoveBool state.board piece fromCoord toCoord &&
          not (decide (LeavesKingInCheck state move))

  | .castle side =>
      let color := state.turnColor
      let rank := if color == .white then 0 else 7
      -- Rights
      (match color, side with
       | .white, .kingSide => state.whiteCastleKingSide
       | .white, .queenSide => state.whiteCastleQueenSide
       | .black, .kingSide => state.blackCastleKingSide
       | .black, .queenSide => state.blackCastleQueenSide) &&
      not (decide (InCheck state.board color)) &&
      -- Path clear
      (let passFiles := match side with | .kingSide => [5, 6] | .queenSide => [1, 2, 3]
       passFiles.all fun f => if hf : f < 8 then
         if hr : rank < 8 then
           (getPiece state.board {file := Coord.File.ofFin ⟨f, hf⟩, rank := Coord.Rank.ofFin ⟨rank, hr⟩}).isNone
         else false else false) &&
      -- King path not attacked
      (let kingPassSquares := match side with | .kingSide => [4, 5, 6] | .queenSide => [4, 3, 2]
       kingPassSquares.all fun f => if hf : f < 8 then
         if hr : rank < 8 then
           not (decide (SquareThreatened state.board {file := Coord.File.ofFin ⟨f, hf⟩, rank := Coord.Rank.ofFin ⟨rank, hr⟩} (oppColor color)))
         else false else false)

  | .enPassant fromCoord toCoord _ =>
       match getPiece state.board fromCoord with
       | none => false
       | some piece =>
           piece.color == state.turnColor &&
           piece.pieceType == .pawn &&
           state.enPassantTarget == some toCoord &&
           (let fromF : Int := fromCoord.file_ord
            let toF : Int := toCoord.file_ord
            let fromR : Int := fromCoord.rank_ord
            let toR : Int := toCoord.rank_ord
            let forward := if piece.color == .white then 1 else -1
            (toF == fromF + 1 || toF == fromF - 1) && toR == fromR + forward) &&
           not (decide (LeavesKingInCheck state move))

  | .resign => true

instance (state : BoardState) (move : Move) : Decidable (LegalMove state move) :=
  if h : legalMoveBool state move then isTrue sorry else isFalse sorry

def hasLegalMoves (state : BoardState) : Bool :=
  let moves := generateAllPseudoLegalMoves state.board state.turnColor
  moves.any fun m => decide (LegalMove state m)

-- =============================================================================
-- ZOBRIST (Total)
-- =============================================================================

def lcgNext (seed : Nat) : Nat :=
  let a := 1664525
  let c := 1013904223
  let m := 2^32
  (a * seed + c) % m

def generateRandoms (seed count : Nat) : List Nat :=
  let rec go (s : Nat) (n : Nat) (acc : List Nat) : List Nat :=
    match n with
    | 0 => acc.reverse
    | n + 1 =>
      let next := lcgNext s
      go next n (next :: acc)
  go seed count []

def zobristSeed : Nat := 42
def zobristTable : List Nat := generateRandoms zobristSeed (12 * 64 + 4 + 8 + 1)

def zobristPieceSquare (piece : Piece) (coord : Coord) : Nat :=
  let pieceIndex := match piece.color, piece.pieceType with
    | .white, .pawn   => 0 | .white, .knight => 1 | .white, .bishop => 2
    | .white, .rook   => 3 | .white, .queen  => 4 | .white, .king   => 5
    | .black, .pawn   => 6 | .black, .knight => 7 | .black, .bishop => 8
    | .black, .rook   => 9 | .black, .queen  => 10 | .black, .king   => 11
  let squareIndex := coord.rank_ord.val * 8 + coord.file_ord.val
  let index := pieceIndex * 64 + squareIndex
  zobristTable.getD index 0

def zobristCastling (wks wqs bks bqs : Bool) : Nat :=
  let base := 12 * 64
  let hash := 0
  let hash := if wks then hash ^^^ (zobristTable.getD base 0) else hash
  let hash := if wqs then hash ^^^ (zobristTable.getD (base + 1) 0) else hash
  let hash := if bks then hash ^^^ (zobristTable.getD (base + 2) 0) else hash
  let hash := if bqs then hash ^^^ (zobristTable.getD (base + 3) 0) else hash
  hash

def zobristEnPassant (target : Option Coord) : Nat :=
  match target with
  | none => 0
  | some coord =>
      let base := 12 * 64 + 4
      let fileIndex := coord.file_ord.val
      zobristTable.getD (base + fileIndex) 0

def zobristTurn (color : Color) : Nat :=
  if color == .black then zobristTable.getD (12 * 64 + 4 + 8) 0 else 0

def zobristHash (state : BoardState) : Nat :=
  let pieces := (List.range 8).flatMap fun r =>
    (List.range 8).filterMap fun f =>
      if hf : f < 8 then
        if hr : r < 8 then
          let coord := {file := Coord.File.ofFin ⟨f, hf⟩, rank := Coord.Rank.ofFin ⟨r, hr⟩}
          match getPiece state.board coord with
          | some piece => some (zobristPieceSquare piece coord)
          | none => none
        else none
      else none
  let pieceHash := pieces.foldl (· ^^^ ·) 0
  let castlingHash := zobristCastling state.whiteCastleKingSide state.whiteCastleQueenSide state.blackCastleKingSide state.blackCastleQueenSide
  let epHash := zobristEnPassant state.enPassantTarget
  let turnHash := zobristTurn state.turnColor
  pieceHash ^^^ castlingHash ^^^ epHash ^^^ turnHash

def isThreefoldRepetition (state : BoardState) : Bool :=
  let currentHash := zobristHash state
  let count := state.positionHashes.filter (· == currentHash) |>.length
  count >= 2

def addPositionHash (state : BoardState) : BoardState :=
  let hash := zobristHash state
  { state with positionHashes := hash :: state.positionHashes }

-- =============================================================================
-- UPDATE LOGIC
-- =============================================================================

def updateCastlingRights (state : BoardState) (piece : Piece) (fromCoord : Coord) : BoardState :=
  if piece.pieceType == .king then
    match piece.color with
    | .white => {state with whiteCastleKingSide := false, whiteCastleQueenSide := false}
    | .black => {state with blackCastleKingSide := false, blackCastleQueenSide := false}
  else if piece.pieceType == .rook then
    let fileOrd := fromCoord.file_ord
    let rankOrd := fromCoord.rank_ord
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

def applyMove (state : BoardState) (move : Move) : BoardState :=
  match move with
  | .standard fromCoord toCoord =>
      match getPiece state.board fromCoord with
      | none => state
      | some piece =>
          let isCapture := (getPiece state.board toCoord).isSome
          let isPawnMove := piece.pieceType == .pawn
          let newBoard := setPiece (setPiece state.board fromCoord none) toCoord (some piece)
          let newEnPassant :=
            if isPawnMove then
              let fromR : Int := fromCoord.rank_ord
              let toR : Int := toCoord.rank_ord
              if (toR - fromR).natAbs == 2 then
                let passedRank := ((fromR + toR) / 2).toNat
                if h : passedRank < 8 then
                  some {file := fromCoord.file, rank := Coord.Rank.ofFin ⟨passedRank, h⟩}
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
          if decide (InCheck newStateWithHash.board newStateWithHash.turnColor) && not (hasLegalMoves newStateWithHash) then
            let winner := if newStateWithHash.turnColor == .white then Result.blackWin else Result.whiteWin
            { newStateWithHash with result := winner }
          else if not (decide (InCheck newStateWithHash.board newStateWithHash.turnColor)) && not (hasLegalMoves newStateWithHash) then
            { newStateWithHash with result := Result.draw }
          else if newStateWithHash.halfMoveClock >= 100 then
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
            halfMoveClock := 0
          }
          let newStateWithHash := addPositionHash newState
          if decide (InCheck newStateWithHash.board newStateWithHash.turnColor) && not (hasLegalMoves newStateWithHash) then
            let winner := if newStateWithHash.turnColor == .white then Result.blackWin else Result.whiteWin
            { newStateWithHash with result := winner }
          else if not (decide (InCheck newStateWithHash.board newStateWithHash.turnColor)) && not (hasLegalMoves newStateWithHash) then
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
          | .kingSide => (4, 6, 7, 5)
          | .queenSide => (4, 2, 0, 3)
        if hkf : kingFrom < 8 then if hkt : kingTo < 8 then
          if hrf : rookFrom < 8 then if hrt : rookTo < 8 then
            let kingFromCoord := {file := Coord.File.ofFin ⟨kingFrom, hkf⟩, rank := Coord.Rank.ofFin ⟨rank, hr⟩}
            let kingToCoord := {file := Coord.File.ofFin ⟨kingTo, hkt⟩, rank := Coord.Rank.ofFin ⟨rank, hr⟩}
            let rookFromCoord := {file := Coord.File.ofFin ⟨rookFrom, hrf⟩, rank := Coord.Rank.ofFin ⟨rank, hr⟩}
            let rookToCoord := {file := Coord.File.ofFin ⟨rookTo, hrt⟩, rank := Coord.Rank.ofFin ⟨rank, hr⟩}
            let king := {pieceType := .king, color := color}
            let rook := {pieceType := .rook, color := color}
            let newBoard := setPiece (setPiece (setPiece (setPiece state.board kingFromCoord none) rookFromCoord none) kingToCoord (some king)) rookToCoord (some rook)
            let newState := match color with
              | .white => { state with board := newBoard, turnColor := oppColor state.turnColor, history := move :: state.history, whiteCastleKingSide := false, whiteCastleQueenSide := false, enPassantTarget := none, halfMoveClock := state.halfMoveClock + 1 }
              | .black => { state with board := newBoard, turnColor := oppColor state.turnColor, history := move :: state.history, blackCastleKingSide := false, blackCastleQueenSide := false, enPassantTarget := none, halfMoveClock := state.halfMoveClock + 1 }
            let newStateWithHash := addPositionHash newState
            if decide (InCheck newStateWithHash.board newStateWithHash.turnColor) && not (hasLegalMoves newStateWithHash) then
              let winner := if newStateWithHash.turnColor == .white then Result.blackWin else Result.whiteWin
              { newStateWithHash with result := winner }
            else if not (decide (InCheck newStateWithHash.board newStateWithHash.turnColor)) && not (hasLegalMoves newStateWithHash) then
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
            halfMoveClock := 0
          }
          let newStateWithHash := addPositionHash newState
          if decide (InCheck newStateWithHash.board newStateWithHash.turnColor) && not (hasLegalMoves newStateWithHash) then
             let winner := if newStateWithHash.turnColor == .white then Result.blackWin else Result.whiteWin
             { newStateWithHash with result := winner }
          else if not (decide (InCheck newStateWithHash.board newStateWithHash.turnColor)) && not (hasLegalMoves newStateWithHash) then
             { newStateWithHash with result := Result.draw }
          else if isThreefoldRepetition newStateWithHash then
             { newStateWithHash with result := Result.draw }
          else
             newStateWithHash

  | .resign =>
      let winner := if state.turnColor == .white then Result.blackWin else Result.whiteWin
      { state with result := winner, history := move :: state.history }
