import Chess.Core

namespace Chess.Parser

open Chess.Core

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
     | some r => (p.coord.rank_ord : Nat) == r
     | none => true)

  -- Filter to pieces that can legally make this move
  let validCandidates := candidates.filter fun p =>
    let fromCoord := p.coord

    -- Check if piece can move to destination (canPieceMove handles path checking)
    -- Updated: use decide(PieceCanMove ...)
    if not (decide (PieceCanMove state.board p.piece fromCoord toCoord)) then
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
            let capturedSquare := { file := alg.toFile, rank := Coord.Rank.ofFin ⟨capturedRank, h⟩ }
            Move.enPassant fromCoord toCoord capturedSquare
          else
            Move.standard fromCoord toCoord
        else if let some promoPiece := alg.promotion then
          Move.promotion fromCoord toCoord promoPiece
        else
          Move.standard fromCoord toCoord

      -- Verify the move is legal (doesn't leave king in check)
      if decide (LegalMove state baseMove) then
        some baseMove
      else
        none
  | _ => none  -- Zero or multiple candidates = ambiguous or invalid

-- Main move parser that tries algebraic notation first, then falls back to coordinate notation
def parseMove (state : BoardState) (s : String) : Option Move :=
  -- Try castling first (works for both notations)
  if s == "O-O" || s == "0-0" then
    let move := Move.castle .kingSide
    if decide (LegalMove state move) then some move else none
  else if s == "O-O-O" || s == "0-0-0" then
    let move := Move.castle .queenSide
    if decide (LegalMove state move) then some move else none
  else if s == "resign" || s == "Resign" then
    some Move.resign
  else
    -- Try algebraic notation first
    match parseAlgebraic s with
    | some alg => findAlgebraicMove state alg
    | none =>
        -- Fall back to coordinate notation
        parseSimpleMove s
