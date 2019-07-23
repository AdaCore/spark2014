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


with Ada.Text_IO; use Ada.Text_IO;
with Ada.Strings.Unbounded; use Ada.Strings.Unbounded;


package ACPgn is

--        Pgn_File_Name : constant String (1 .. 12) := "adachess.pgn";
--     Pgn_File_Name : constant String (1 .. 9) := "Arena.pgn";

--     Pgn_File : File_Type;

   type Pgn_Type is
      record
         Event        : Unbounded_String;
         Site         : Unbounded_String;
         Date         : Unbounded_String;
         Round        : Unbounded_String;
         White        : Unbounded_String;
         Black        : Unbounded_String;
         Result       : Unbounded_String;
         ECO          : Unbounded_String;
         Moves_List   : Unbounded_String;
         Formatted_Moves_List : Unbounded_String;
      end record;

   Pgn : Pgn_Type;

   Pgn_Games : array (1 .. 4026) of Pgn_Type;
   Pgn_Game_Counter : Natural := 0;

--     procedure Open_Pgn;
--     procedure Close_Pgn;

--     procedure Read_Pgn_Data;
   procedure Read_Pgn_Data (Book : out File_Type);
   procedure Print_Pgn_Data (Pgn : in Pgn_Type);

private

   function Format_Moves_List (Source : String) return String;

   Open_Tag : constant Character := '[';
   Close_Tag : constant Character := ']';
   Quotes    : constant Character := '"';

   function Clean_Comment_From_Pgn_String (Source : String) return String;


end ACPgn;

