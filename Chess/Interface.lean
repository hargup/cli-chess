import Chess.Core
import Chess.Parser

namespace Chess.Interface

open Chess.Core
open Chess.Parser

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
          if decide (LegalMove state move) then
            let newState := applyMove state move
            gameLoop newState
          else
            IO.println "Invalid move. Try again."
            gameLoop state
