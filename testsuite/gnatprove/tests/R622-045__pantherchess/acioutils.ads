
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


with Ada.Containers.Vectors;
with Ada.Characters.Handling;
with Ada.Strings.Unbounded; use Ada.Strings.Unbounded;


package ACIOUtils is

   type String_Access is access String;
   type Parameters_Array is array (1 .. 32) of Unbounded_String;

   type Parameter_Type is
      record
	 Command    : Unbounded_String;
	 Params     : Parameters_Array;
	 Tokens     : Integer;
      end record;

   function Parse_Input (Input : in String) return Parameter_Type;


   function Lower_Case (C : in Character) return Character renames Ada.Characters.Handling.To_Lower;
   function Upper_Case (C : in Character) return Character renames Ada.Characters.Handling.To_Upper;


   ------------------
   -- String utils --
   ------------------

   subtype String_Type is Ada.Strings.Unbounded.Unbounded_String;
   type String_Access_Type is access String_Type;

   type String_Array is array (Positive range <>) of String_Type;

   function To_String_Type (Source : String) return String_Type renames Ada.Strings.Unbounded.To_Unbounded_String;

   package String_Vector is new Ada.Containers.Vectors
     (Index_Type   => Natural,
      Element_Type => String_Type);
   use String_Vector;

--     function Split (Source : in String; Delimiter : in Character := ' ') return String_Vector.Vector;
   function Split_To_String (Source : in String; Delimiter : in Character := ' ') return String_Array;

   function Index_Of (Source : String; Item : Character) return Natural;

   -- Remove empty string from the array
   function Fix_String_Array (Source : String_Array) return String_Array;

   function Extract_Move_From_String (Source : String) return String;

private

   function Split (Str : in String) return Parameter_Type;

end ACIOUtils;
