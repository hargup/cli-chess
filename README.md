# Chess Game in Lean 4

> **Note:** This project was vibe coded with the help of Claude Code and Cursor. No guarantees.

A fully playable chess implementation in Lean 4 with complete rules enforcement, algebraic notation support, and beautiful Unicode display.

## Features

- **Complete Chess Rules**: All standard chess rules implemented
- **Algebraic Notation**: Full support for standard chess notation (Nf3, Bxe5, O-O, e8=Q)
- **Coordinate Notation**: Also supports e2e4 style moves
- **Move Validation**: Prevents illegal moves including check violations
- **Special Moves**: Castling (O-O/O-O-O), en passant, pawn promotion
- **Game End Detection**: Checkmate, stalemate, fifty-move rule, threefold repetition
- **Beautiful Display**: Unicode chess pieces with grid lines

## Prerequisites

- **Lean 4** (v4.25.2 or later)
- No other dependencies required

### Installing Lean 4

```bash
# Using elan (recommended)
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh
```

## Quick Start

### Option 1: Run directly with Lean (no build needed)
```bash
lean --run Chess.lean
```

### Option 2: Build and run (faster startup after first build)
```bash
lake build
.lake/build/bin/chess
```

### Option 3: Use the helper script
```bash
./play_chess.sh
```

## How to Play

### Move Notation

Moves can be entered in **algebraic notation** (standard) or **coordinate notation**:

#### Algebraic Notation (Recommended)
| Move Type | Example | Description |
|-----------|---------|-------------|
| Pawn move | `e4`, `d5` | Pawn to e4, pawn to d5 |
| Piece move | `Nf3`, `Bb5` | Knight to f3, Bishop to b5 |
| Capture | `Nxf3`, `exd5` | Knight captures on f3, pawn captures d5 |
| Castling | `O-O`, `O-O-O` | Kingside, queenside |
| Promotion | `e8=Q` | Promote to Queen |
| Disambiguation | `Nbd2`, `R1a3` | When multiple pieces can move |

#### Coordinate Notation
| Move Type | Example | Description |
|-----------|---------|-------------|
| Standard | `e2e4` | Move from e2 to e4 |
| Capture | `e4xd5` | Capture on d5 |
| Promotion | `e7e8q` | Pawn promotes to queen |

### Special Commands
- `resign` - Resign the game

## Board Display

```
  ╔═══╤═══╤═══╤═══╤═══╤═══╤═══╤═══╗
8 ║ ♜ │ ♞ │ ♝ │ ♛ │ ♚ │ ♝ │ ♞ │ ♜ ║ 8
  ╟───┼───┼───┼───┼───┼───┼───┼───╢
7 ║ ♟ │ ♟ │ ♟ │ ♟ │ ♟ │ ♟ │ ♟ │ ♟ ║ 7
  ╟───┼───┼───┼───┼───┼───┼───┼───╢
6 ║ · │   │ · │   │ · │   │ · │   ║ 6
  ╟───┼───┼───┼───┼───┼───┼───┼───╢
5 ║   │ · │   │ · │   │ · │   │ · ║ 5
  ╟───┼───┼───┼───┼───┼───┼───┼───╢
4 ║ · │   │ · │   │ · │   │ · │   ║ 4
  ╟───┼───┼───┼───┼───┼───┼───┼───╢
3 ║   │ · │   │ · │   │ · │   │ · ║ 3
  ╟───┼───┼───┼───┼───┼───┼───┼───╢
2 ║ ♙ │ ♙ │ ♙ │ ♙ │ ♙ │ ♙ │ ♙ │ ♙ ║ 2
  ╟───┼───┼───┼───┼───┼───┼───┼───╢
1 ║ ♖ │ ♘ │ ♗ │ ♕ │ ♔ │ ♗ │ ♘ │ ♖ ║ 1
  ╚═══╧═══╧═══╧═══╧═══╧═══╧═══╧═══╝
    a   b   c   d   e   f   g   h
```

### Piece Symbols
- **White**: ♔ ♕ ♖ ♗ ♘ ♙
- **Black**: ♚ ♛ ♜ ♝ ♞ ♟

## Implemented Features

| Feature | Status |
|---------|--------|
| All piece movements | ✅ |
| Piece capture | ✅ |
| Turn-based play | ✅ |
| Check validation | ✅ |
| Checkmate detection | ✅ |
| Stalemate detection | ✅ |
| Castling (O-O/O-O-O) | ✅ |
| En passant | ✅ |
| Pawn promotion | ✅ |
| Fifty-move rule | ✅ |
| Threefold repetition | ✅ |
| Algebraic notation | ✅ |
| Move history | ✅ |

## Limitations

- No computer player/AI
- No undo/redo
- No save/load games
- No PGN export

## Technical Details

- **Language**: Lean 4
- **Lines of Code**: ~1400
- **Single file**: Chess.lean contains the complete implementation

### Code Structure

1. **Types**: Color, File, Rank, Coord, PieceType, Piece, Board, Move, BoardState
2. **Board Functions**: getPiece, setPiece, initialBoard
3. **Move Validation**: isValidMove with full rule checking
4. **Threat Detection**: isSquareThreatened for check/checkmate
5. **Game Logic**: applyMove, checkmate/stalemate detection
6. **I/O**: parseMove, displayBoard, game loop

### Zobrist Hashing

Threefold repetition is detected using Zobrist hashing:
- Pre-computed hash values for each piece-square combination
- XOR-based position fingerprinting
- Efficient position comparison without full board comparison

## Example Session

```
=== Chess Game ===
Move format: e2e4 or e2-e4
Type 'resign' to resign

White to move
Enter move: e4

Black to move
Enter move: e5

White to move
Enter move: Nf3

...
```

## License

MIT License

## See Also

- [CHANGELOG.md](CHANGELOG.md) - Version history and feature additions
