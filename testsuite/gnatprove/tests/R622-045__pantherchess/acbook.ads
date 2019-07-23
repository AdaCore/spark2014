--  PantherChess - based on AdaChess - Copyright (C) 2017-2018 Bill Zuercher
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


with Ada.Text_IO; use Ada.Text_IO;
with ACChessboard; use ACChessboard;
with ACIOUtils; use ACIOUtils;

with Ada.Strings.Unbounded; use Ada.Strings.Unbounded;
with Ada.Numerics.Discrete_Random;


package ACBook is


   Book : File_Type;

   Default_Book : constant String (1 .. 16) := "Pantherchess.pgn";

   -- Opening_Book_Name : constant String (1 .. 15) := "Pantherchess.pgn";
   Opening_Book_Name : Ada.Strings.Unbounded.Unbounded_String := To_Unbounded_String (Default_Book);

   subtype Book_Range is Natural range 1 .. 61100; -- maximum size for book matches
   Book_Size : constant Natural := Book_Range'Last - Book_Range'First + 1;

   End_Of_Book_Line : exception;


   package Random_Opening is new Ada.Numerics.Discrete_Random (Natural);

   Seed_Generator : Random_Opening.Generator;


   procedure Open_Book;
   procedure Close_Book;

   function Book_Move return Move_Type;

private

   function Is_Pgn_File (File_Type : String) return Boolean;

   -- Split string in parts. Delimiter is the white space
   function Split (Str : in String) return Parameter_Type;


end ACBook;
