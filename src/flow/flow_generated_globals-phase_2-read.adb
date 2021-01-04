------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--  F L O W . G E N E R A T E D _ G L O B A L S . P H A S E _ 2 . R E A D   --
--                                                                          --
--                                  B o d y                                 --
--                                                                          --
--                Copyright (C) 2018-2021, Altran UK Limited                --
--                                                                          --
-- gnat2why is  free  software;  you can redistribute  it and/or  modify it --
-- under terms of the  GNU General Public License as published  by the Free --
-- Software  Foundation;  either version 3,  or (at your option)  any later --
-- version.  gnat2why is distributed  in the hope that  it will be  useful, --
-- but WITHOUT ANY WARRANTY; without even the implied warranty of  MERCHAN- --
-- TABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the GNU General Public --
-- License for  more details.  You should have  received  a copy of the GNU --
-- General  Public License  distributed with  gnat2why;  see file COPYING3. --
-- If not,  go to  http://www.gnu.org/licenses  for a complete  copy of the --
-- license.                                                                 --
--                                                                          --
------------------------------------------------------------------------------

with Ada.Strings;           use Ada.Strings;
with Ada.Strings.Maps;      use Ada.Strings.Maps;
with Ada.Strings.Unbounded; use Ada.Strings.Unbounded;

package body Flow_Generated_Globals.Phase_2.Read is

   --  To read the consecutive items from a single line of an ALI file with a
   --  GG data we first store the entire line in a buffer, and then pick the
   --  items using the strongly typed interface exposed from the spec of this
   --  package.

   --  Internally, we maintain a position of where the next string token
   --  starts and increment it once this token is consumed. Those tokens are
   --  then converted to the typed values as requested by the users of this
   --  package.

   Buffer      : Unbounded_String;
   Token_Start : Positive;

   function Get_Token return String
   with Pre  => Token_Start <= Length (Buffer),
        Post => Get_Token'Result'First = 1
                and then Get_Token'Result'Length > 0;
   --  Returns the next token from the current line and increments the position
   --  of where the next token starts.
   --
   --  This is intentionally a function and not a procedure to simplify
   --  implementation of the callers; however, they must be careful about side
   --  effects and not call it in expressions where calls might be reordered by
   --  the compiler (e.g. it must not be used in different actual parameters of
   --  a single subprogram call). Luckily, this package is small enough to
   --  manually inspect that this doesn't happen.

   Separator : constant Character_Set := To_Set (' ');
   --  Individual tokens of the ALI line are separated by spaces

   ---------------
   -- Get_Token --
   ---------------

   function Get_Token return String is
      First  : Positive;
      Last   : Natural;
      Length : Positive;

   begin
      Ada.Strings.Unbounded.Find_Token
        (Source => Buffer,
         Set    => Separator,
         From   => Token_Start,
         Test   => Outside,
         First  => First,
         Last   => Last);

      pragma Assert (Last /= 0);

      Length := Last - First + 1;

      Token_Start := Last + 1;

      declare
         subtype Token is String (1 .. Length);

         Match : constant String :=
           Ada.Strings.Unbounded.Slice (Source => Buffer,
                                        Low    => First,
                                        High   => Last);
      begin
         return Token (Match);
      end;
   end Get_Token;

   -----------------
   -- New_GG_Line --
   -----------------

   procedure New_GG_Line (Line : String) is
   begin
      --  Copy line into the internal buffer but skip the "GG " prefix
      Set_Unbounded_String (Buffer, Line (Line'First + 3 .. Line'Last));
      Token_Start := 1;
   end New_GG_Line;

   -----------------------
   -- Terminate_GG_Line --
   -----------------------

   procedure Terminate_GG_Line is
   begin
      --  Check that entire line has been consumed and release the buffer
      pragma Assert (Token_Start = Length (Buffer) + 1);

      Set_Unbounded_String (Buffer, "");
   end Terminate_GG_Line;

   ---------------
   -- Serialize --
   ---------------

   procedure Serialize (E : out Entity_Name) is
   begin
      E := To_Entity_Name (Get_Token);
   end Serialize;

   ---------------
   -- Serialize --
   ---------------

   procedure Serialize (Names : in out Name_Sets.Set; Label : String := "") is
      Size : Natural;
   begin
      if Label /= ""
        and then Get_Token /= Label
      then
         raise Program_Error;
      end if;

      Size := Natural'Value (Get_Token);

      for J in 1 .. Size loop
         Names.Include (To_Entity_Name (Get_Token));
      end loop;
   end Serialize;

   procedure Serialize (Names : in out Name_Lists.List; Label : String := "")
   is
      Size : Natural;
   begin
      if Label /= ""
        and then Get_Token /= Label
      then
         raise Program_Error;
      end if;

      Size := Natural'Value (Get_Token);

      for J in 1 .. Size loop
         Names.Append (To_Entity_Name (Get_Token));
      end loop;
   end Serialize;

   procedure Serialize (N : out Int) is
   begin
      N := Int'Value (Get_Token);
   end Serialize;

   ------------------------
   -- Serialize_Discrete --
   ------------------------

   procedure Serialize_Discrete (A : out T; Label : String := "") is
   begin
      if Label /= ""
        and then Get_Token /= Label
      then
         raise Program_Error;
      end if;

      A := T'Value (Get_Token);
   end Serialize_Discrete;

end Flow_Generated_Globals.Phase_2.Read;
