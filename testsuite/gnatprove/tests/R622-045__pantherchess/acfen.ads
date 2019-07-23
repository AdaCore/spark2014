--  PantherChess - based on AdaChess Copyright (C) 2017 Bill Zuercher
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



package ACFen is

   procedure Fen_Init;
   procedure Fen_Load_Pieces(Fen : in String);
   procedure Fen_Load_Side_To_Move(Fen : in String);
   procedure Fen_Load_Castle_Flags(Fen : in String);
   procedure Fen_Load_En_Passant(Fen : in String);
   procedure Fen_Load_Fifty_Move_Counter (Fen : in String);
   procedure Fen_Load_Ply_Depth (Fen : in String);


   -- Output current position into a string
   function Fen_Save_To_String return String;

end ACfen;
