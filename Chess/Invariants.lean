import Chess.Core

namespace Chess.Invariants

open Chess.Core

-- =============================================================================
-- BOARD INVARIANTS
-- =============================================================================

/--
Invariant: There must be exactly one King of each color on the board.
-/
def KingCountInvariant (board : Board) : Prop :=
  let whiteKings := (getPieces board .white).filter (fun p => p.piece.pieceType == .king)
  let blackKings := (getPieces board .black).filter (fun p => p.piece.pieceType == .king)
  whiteKings.length = 1 ∧ blackKings.length = 1

/--
Invariant: Pawns cannot exist on the 1st (rank 0) or 8th (rank 7) ranks.
They should have promoted or not started there.
-/
def PawnRankInvariant (board : Board) : Prop :=
  ∀ (f r : Fin 8),
    match board.get f r with
    | some piece =>
        if piece.pieceType == .pawn then
          r.val ≠ 0 ∧ r.val ≠ 7
        else True
    | none => True

-- =============================================================================
-- STATE INVARIANTS
-- =============================================================================

/--
Invariant: If en passant target is set, it must be valid.
1. The target square must be empty.
2. There must be a pawn of the opponent's color "behind" the target (the one that just moved).
   (If White to move, target is rank 5 (index 5), pawn is at rank 4 (index 4)).
   (If Black to move, target is rank 2 (index 2), pawn is at rank 3 (index 3)).
-/
def EnPassantInvariant (state : BoardState) : Prop :=
  match state.enPassantTarget with
  | none => True
  | some target =>
      -- Target square must be empty
      (getPiece state.board target).isNone ∧
      -- Check for the pawn being captured
      let capturedRank := if state.turnColor == .white then 4 else 3
      if h : capturedRank < 8 then
        let capturedSquare := { file := target.file, rank := Coord.Rank.ofFin ⟨capturedRank, h⟩ }
        match getPiece state.board capturedSquare with
        | some p => p.pieceType == .pawn ∧ p.color ≠ state.turnColor
        | none => False
      else False -- Should not happen given rank logic

/--
Invariant: Castling rights must be consistent with the board.
If white has KingSide castling rights:
1. The White King must be at e1.
2. The White King-side Rook must be at h1.
(Similarly for other sides)
-/
def CastlingRightsInvariant (state : BoardState) : Prop :=
  (state.whiteCastleKingSide →
    (getPiece state.board {file := .E, rank := ._1} = some {pieceType := .king, color := .white}) ∧
    (getPiece state.board {file := .H, rank := ._1} = some {pieceType := .rook, color := .white})) ∧

  (state.whiteCastleQueenSide →
    (getPiece state.board {file := .E, rank := ._1} = some {pieceType := .king, color := .white}) ∧
    (getPiece state.board {file := .A, rank := ._1} = some {pieceType := .rook, color := .white})) ∧

  (state.blackCastleKingSide →
    (getPiece state.board {file := .E, rank := ._8} = some {pieceType := .king, color := .black}) ∧
    (getPiece state.board {file := .H, rank := ._8} = some {pieceType := .rook, color := .black})) ∧

  (state.blackCastleQueenSide →
    (getPiece state.board {file := .E, rank := ._8} = some {pieceType := .king, color := .black}) ∧
    (getPiece state.board {file := .A, rank := ._8} = some {pieceType := .rook, color := .black}))


/--
Invariant: The player NOT to move cannot be in check.
(In a valid game state, the previous player must have moved out of check, and couldn't have moved into check).
Exception: This doesn't apply if the game result is already decided (e.g. checkmate),
but strictly speaking in standard chess state, the king capture is never "realized".
-/
def TurnCheckInvariant (state : BoardState) : Prop :=
  ¬(InCheck state.board (oppColor state.turnColor))

-- =============================================================================
-- AGGREGATE VALIDITY
-- =============================================================================

/--
A BoardState is valid if it satisfies all invariants.
-/
def ValidState (state : BoardState) : Prop :=
  KingCountInvariant state.board ∧
  PawnRankInvariant state.board ∧
  EnPassantInvariant state ∧
  CastlingRightsInvariant state ∧
  TurnCheckInvariant state

end Chess.Invariants
