------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                            T E M P L A T E S                             --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                     Copyright (C) 2010-2020, AdaCore                     --
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
-- gnat2why is maintained by AdaCore (http://www.adacore.com)               --
--                                                                          --
------------------------------------------------------------------------------

with Ada.Text_IO;                use Ada.Text_IO;
with Ada.Containers;             use Ada.Containers;
with GNAT.Regpat;                use GNAT.Regpat;

with Ada.Strings.Hash;
with Ada.Containers.Hashed_Maps;

package body Templates is

   type String_Access is access all String;

   type Printer is not null access procedure (O : in out Output_Record);

   type Substitution_Info is record
      --  Base type for substitutions

      Generator : Printer;
      --  Procedure to call in order to perform the substitution
   end record;

   function Hash (Key : String_Access) return Hash_Type;
   function Equivalent_Keys (Left, Right : String_Access) return Boolean;

   package Substitutions is
     new Ada.Containers.Hashed_Maps
     (Key_Type => String_Access,
      Element_Type => Substitution_Info,
      Hash => Hash,
      Equivalent_Keys => Equivalent_Keys,
      "=" => "=");

   Substitution_Map : Substitutions.Map;
   --  Hashtable for substitutions; it records the association between
   --  patterns and generators.

   ---------
   -- Add --
   ---------

   procedure Add
     (Pattern   : String;
      Generator : not null access procedure (O : in out Output_Record))
   is
      use Substitutions;

      SI : constant Substitution_Info :=
             Substitution_Info'(Generator => Generator);
   begin
      Substitution_Map.Insert (new String'(Pattern), SI);
   end Add;

   ---------------------
   -- Equivalent_Keys --
   ---------------------

   function Equivalent_Keys (Left, Right : String_Access) return Boolean is
   begin
      return Left.all = Right.all;
   end Equivalent_Keys;

   ----------
   -- Hash --
   ----------

   function Hash (Key : String_Access) return Hash_Type is
   begin
      return Ada.Strings.Hash (Key.all);
   end Hash;

   -------------
   -- Process --
   -------------

   procedure Process (Filename : String) is
      use Substitutions;

      Input   : File_Type;
      Matcher : constant Pattern_Matcher := Compile ("([ ]*)_@([A-Za-z_]+)@_");
      Matches : Match_Array (0 .. 2);
      O       : Output_Record;
   begin
      Open_Output (O, Filename);
      Open (Input, In_File, Filename & "-tmpl");
      loop
         declare
            Line : constant String := Get_Line (Input);
         begin
            if Match (Matcher, Line) then
               Match (Matcher, Line, Matches);

               declare
                  Key      : aliased String :=
                               Line (Matches (2).First .. Matches (2).Last);
                  Position : constant Cursor :=
                               Substitution_Map.Find (Key'Unrestricted_Access);
                  Indent   : constant Natural :=
                               Matches (1).Last - Matches (1).First + 1;
               begin
                  if Position = No_Element then
                     Put_Line ("warning: pattern " & Key & " not found");
                  else
                     declare
                        SI : constant Substitution_Info :=
                               Element (Position);
                     begin
                        Absolute_Indent (O, Indent);
                        SI.Generator (O);
                        Absolute_Indent (O, 0);
                     end;
                  end if;
               end;
            else
               if End_Of_File (Input) then
                  P (O, Line);
                  exit;
               else
                  PL (O, Line);
               end if;
            end if;
         end;
      end loop;
   end Process;

end Templates;
