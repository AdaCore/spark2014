--  PantherChess - based on AdaChess Copyright (C) 2017-2018 Bill Zuercher
--
--  AdaChess - Cool Chess Engine
--
--  Copyright (C) 2013-2017 - Alessandro Iavicoli
--  Email: adachess@gmail.com - Web Page: http://www.adachess.com
--
--  This program is free software: you can redistribute it and/or modify
--  it under the terms of the GNU General Public License as published by
--  the Free Software Foundation, either version 3 of the License, or
--  (at your option) any later version.
--
--  This program is distributed in the hope that it will be useful,
--  but WITHOUT ANY WARRANTY; without even the implied warranty of
--  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
--  GNU General Public License for more details.
--
--  You should have received a copy of the GNU General Public License
--  along with this program.  If not, see <http://www.gnu.org/licenses/>.


package ACPiece is

   type Piece_Type is
     (Frame, Empty,
      White_Pawn, White_Knight, White_Bishop, White_Panther, White_Rook, White_Queen, White_King,
      Black_Pawn, Black_Knight, Black_Bishop, Black_Panther, Black_Rook, Black_Queen, Black_King)
     with Size => 4;

   -- "Not" a piece tell us if a piece is empty or "Not" ;-)
   function "not" (Piece : in Piece_Type) return Boolean is
     (if Piece = Empty then True else False)
   with Pre => (Piece /= Frame);

   subtype Board_Piece_Type is Piece_Type range Empty .. Black_King;
   subtype Chess_Piece_Type is Piece_Type range White_Pawn .. Black_King;
   subtype White_Piece_Type is Piece_Type range White_Pawn .. White_King;
   subtype Black_Piece_Type is Piece_Type range Black_Pawn .. Black_King;

   Symbols : constant array (Piece_Type'Range) of Character :=
     (' ', ' ', 'P', 'N', 'B', 'X', 'R', 'Q', 'K', 'p', 'n', 'b', 'x', 'r', 'q', 'k');

end ACPiece;
