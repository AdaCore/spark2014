------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                         S E R I A L I S A T I O N                        --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                  Copyright (C) 2015-2017, Altran UK Limited              --
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

with Ada.Strings;       use Ada.Strings;
with Ada.Strings.Fixed; use Ada.Strings.Fixed;
with Ada.Strings.Maps;
with Ada.Text_IO;       use Ada.Text_IO;

package body Serialisation is

   subtype Hex_String is String (1 .. 2);
   --  String of length 2 for text-representation of 8 bits in hex

   function To_Hex (C : Character) return Hex_String;
   --  Convert a character (such as ' ') to a two-digit hex representation
   --  ("20" in this example).

   function From_Hex (S : Hex_String) return Character;
   --  The inverse of the above. Raises Parse_Error if we get something that is
   --  not a hex string.

   function Escape (S : Unbounded_String) return Unbounded_String;
   --  Escape a string so that it contains no spaces or unprintable characters
   --
   --     * the empty string is encoded as "\0"
   --     * ' ' is translated to ':'
   --     * ':' and '\' are escaped with '\'
   --     * non-printable characters are encoded as '\xHH' where H is
   --       an upper-case hex digit.
   --
   --  This minimal translation ensures most strings are as long as they were
   --  before, and are reasonably readable. In particular most magic strings
   --  produced by SPARK 2014 should be untouched.

   function Interpret (S : Unbounded_String) return Unbounded_String;
   --  The inverse of Escape

   generic
      type T is private;
      type E is private;
      type Cursor is private;
      Null_Container : T;
      Null_Element   : E;
      with procedure Merge (Container : in out T;
                            New_Item  : E);
      with function First (Container : T) return Cursor is <>;
      with function Next (Position : Cursor) return Cursor is <>;
      with function Element (Position : Cursor) return E is <>;
      with function Length (Container : T) return Ada.Containers.Count_Type;
      with procedure Reserve_Capacity
        (Container : in out T;
         Capacity  : Ada.Containers.Count_Type);
      with procedure Serialize (A : in out Archive; V : in out E) is <>;
   procedure Serialize_Collection (A   : in out Archive;
                                   V   : in out T);
   --  Generic serialisation for Ada containers. Merge is a subprogram that
   --  is meant to add a single element to the container; we need this because
   --  Append (for lists) and Insert (for sets) have different signatures.

   ---------------
   -- To_String --
   ---------------

   function To_String (A : Archive) return Unbounded_String is
   begin
      return S : Unbounded_String do
         for E of A.Content loop
            if Length (S) > 0 then
               Append (S, " ");
            end if;
            Append (S, Escape (E));
         end loop;
      end return;
   end To_String;

   -----------------
   -- From_String --
   -----------------

   function From_String (S : String) return Archive is
      From : Positive := S'First;
      First, Last : Natural;

   begin
      return A : Archive (Input) do
         while From in S'Range loop
            Find_Token (Source => S,
                        Set    => Ada.Strings.Maps.To_Set (' '),
                        From   => From,
                        Test   => Outside,
                        First  => First,
                        Last   => Last);

            if Last /= 0 then
               A.Content.Append
                 (Interpret (To_Unbounded_String (S (First .. Last))));
               From := Last + 1;
            end if;
         end loop;
      end return;
   end From_String;

   ------------
   -- To_Hex --
   ------------

   function To_Hex (C : Character) return Hex_String is
      Upper : constant Natural := Character'Pos (C)   / 16;
      Lower : constant Natural := Character'Pos (C) mod 16;
      Conv  : constant array (0 .. 15) of Character :=
        ('0', '1', '2', '3', '4', '5', '6', '7',
         '8', '9', 'A', 'B', 'C', 'D', 'E', 'F');
   begin
      return S : Hex_String do
         S (1) := Conv (Upper);
         S (2) := Conv (Lower);
      end return;
   end To_Hex;

   --------------
   -- From_Hex --
   --------------

   function From_Hex (S : Hex_String) return Character is
      R : Natural := 0;
   begin
      for C of S loop
         R := R * 16;
         case C is
            when '0' .. '9' =>
               R := R + (Character'Pos (C) - Character'Pos ('0'));
            when 'A' .. 'F' =>
               R := R + (Character'Pos (C) - Character'Pos ('A')) + 10;
            when others =>
               raise Parse_Error with "malformed string data";
         end case;
      end loop;
      return Character'Val (R);
   end From_Hex;

   ------------
   -- Escape --
   ------------

   function Escape (S : Unbounded_String) return Unbounded_String is
      subtype Printable_Character is Character
        range Character'Val (32) .. Character'Val (126);

      subtype Escaped_Character is Character
        with Static_Predicate => Escaped_Character in ':' | '\' | ' ';

      subtype Unescaped_Printable_Character is Printable_Character
        with Static_Predicate =>
           Unescaped_Printable_Character not in Escaped_Character;

   begin
      if Length (S) = 0 then
         return To_Unbounded_String ("\0");
      end if;

      return V : Unbounded_String := Null_Unbounded_String do
         for I in Natural range 1 .. Length (S) loop
            declare
               C : constant Character := Element (S, I);
            begin
               case C is
                  when ' ' =>
                     Append (V, ':');
                  when ':' | '\' =>
                     Append (V, '\');
                     Append (V, C);
                  when Unescaped_Printable_Character =>
                     Append (V, C);
                  when others =>
                     Append (V, "\x");
                     Append (V, To_Hex (C));
               end case;
            end;
         end loop;
      end return;
   end Escape;

   ---------------
   -- Interpret --
   ---------------

   function Interpret (S : Unbounded_String) return Unbounded_String is
      Resume    : Natural := 0;
      In_Escape : Boolean := False;
   begin
      return V : Unbounded_String do
         for I in Natural range 1 .. Length (S) loop
            if Resume > I then
               null;
            else
               declare
                  C : constant Character := Element (S, I);
               begin
                  if In_Escape then
                     case C is
                        when '0' =>
                           null;
                        when ':' | '\' =>
                           Append (V, C);
                        when 'x' =>
                           if Length (S) < I + 2 then
                              raise Parse_Error with "malformed string data";
                           end if;
                           Resume := I + 3;
                           Append (V, From_Hex (Slice (S, I + 1, I + 2)));
                        when others =>
                           raise Parse_Error with "malformed string data";
                     end case;
                     In_Escape := False;
                  else
                     case C is
                        when '\' =>
                           In_Escape := True;
                        when ':' =>
                           Append (V, ' ');
                        when others =>
                           Append (V, C);
                     end case;
                  end if;
               end;
            end if;
         end loop;
      end return;
   end Interpret;

   ------------------------
   -- Debug_Dump_Archive --
   ------------------------

   procedure Debug_Dump_Archive (A : Archive) is
   begin
      Put_Line ("Archive (" & A.Kind'Img & ")");
      for C of A.Content loop
         Put_Line ("   <" & To_String (C) & ">");
      end loop;
   end Debug_Dump_Archive;

   ---------------
   -- Serialize --
   ---------------

   procedure Serialize (A : in out Archive; V : in out Unbounded_String) is
   begin
      case A.Kind is
         when Input =>
            if A.Content.Is_Empty then
               raise Parse_Error with "insufficient data";
            end if;
            V := A.Content.First_Element;
            A.Content.Delete_First;
         when Output =>
            A.Content.Append (V);
      end case;
   end Serialize;

   ------------------------
   -- Serialize_Discrete --
   ------------------------

   procedure Serialize_Discrete
     (A     : in out Archive;
      V     : in out T;
      Label : String := "")
   is
      Label_Str : Unbounded_String;
   begin
      if Label /= "" then
         case A.Kind is
            when Input =>
               Serialize (A, Label_Str);
               if Label_Str /= Label then
                  raise Parse_Error with "malformed label";
               end if;

            when Output =>
               Label_Str := To_Unbounded_String (Label);
               Serialize (A, Label_Str);
         end case;
      end if;

      case A.Kind is
         when Input =>
            if A.Content.Is_Empty then
               raise Parse_Error with "insufficient data";
            end if;
            V := T'Value (To_String (A.Content.First_Element));
            A.Content.Delete_First;

         when Output =>
            A.Content.Append (Trim (To_Unbounded_String (T'Image (V)), Left));
      end case;
   end Serialize_Discrete;

   --------------------------
   -- Serialize_Collection --
   --------------------------

   procedure Serialize_Collection (A : in out Archive;
                                   V : in out T)
   is
      Elt : E := Null_Element;

      procedure Serialize is new
        Serialize_Discrete (T => Ada.Containers.Count_Type);

      Count : Ada.Containers.Count_Type;

   begin
      case A.Kind is
         when Input =>
            Count := 0;
            Serialize (A, Count);
            Reserve_Capacity (V, Count);

            V := Null_Container;
            for J in 1 .. Count loop
               Serialize (A, Elt);
               Merge (V, Elt);
            end loop;

         when Output =>
            Count := Length (V);
            Serialize (A, Count);

            declare
               C : Cursor := First (V);
            begin
               for J in 1 .. Count loop
                  Elt := Element (C);
                  Serialize (A, Elt);
                  C := Next (C);
               end loop;
            end;
      end case;
   end Serialize_Collection;

   --------------------
   -- Serialize_List --
   --------------------

   procedure Serialize_List (A : in out Archive;
                             V : in out T)
   is
      procedure Merge (Container : in out T;
                       New_Item  : E);
      --  Wrapper for Append to eliminate the third argument

      procedure Reserve_Capacity
        (Container : in out T;
         Capactity : Ada.Containers.Count_Type) is null;
      --  Dummy procedure required by the collection serialization API

      -----------
      -- Merge --
      -----------

      procedure Merge (Container : in out T;
                       New_Item  : E)
      is
      begin
         Append (Container, New_Item, 1);
      end Merge;

      ---------------
      -- Serialize --
      ---------------

      procedure Serialize is new Serialize_Collection
        (T                => T,
         E                => E,
         Cursor           => Cursor,
         Null_Container   => Null_Container,
         Null_Element     => Null_Element,
         Merge            => Merge,
         Length           => Length,
         Reserve_Capacity => Reserve_Capacity);

   --  Start of processing for Serialize_List

   begin
      Serialize (A, V);
   end Serialize_List;

   -------------------
   -- Serialize_Set --
   -------------------

   procedure Serialize_Set (A     : in out Archive;
                            V     : in out T;
                            Label : String := "")
   is
      ---------------
      -- Serialize --
      ---------------

      procedure Serialize is new Serialize_Collection
        (T                => T,
         E                => E,
         Cursor           => Cursor,
         Null_Container   => Null_Container,
         Null_Element     => Null_Element,
         Merge            => Insert,
         Length           => Length,
         Reserve_Capacity => Reserve_Capacity);

      Label_Str : Unbounded_String;

   begin
      if Label /= "" then
         case A.Kind is
            when Input =>
               Serialize (A, Label_Str);
               if Label_Str /= Label then
                  raise Parse_Error with "malformed label";
               end if;

            when Output =>
               Label_Str := To_Unbounded_String (Label);
               Serialize (A, Label_Str);
         end case;
      end if;

      Serialize (A, V);
   end Serialize_Set;

end Serialisation;
