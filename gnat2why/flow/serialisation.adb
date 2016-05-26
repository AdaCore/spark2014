------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                         S E R I A L I S A T I O N                        --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                  Copyright (C) 2015-2016, Altran UK Limited              --
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

with Ada.Strings; use Ada.Strings;
with Ada.Text_IO; use Ada.Text_IO;

package body Serialisation is

   Coll_Begin : constant Unbounded_String := To_Unbounded_String ("[");
   Coll_End   : constant Unbounded_String := To_Unbounded_String ("]");
   --  Begin/end markers for collections (lists, sets).

   subtype Hex_String is String (1 .. 2);
   --  String of length 2 for text-representation of 8 bits in hex.

   procedure Match (A : in out Archive; S : Unbounded_String)
   with Pre => A.Kind = Input;
   --  A classic match-token-or-die helper subprogram. Returns if the next
   --  element of A is a tag equal to S, otherwise raises a Parse_Error
   --  exception.

   function Test (A : Archive; S : Unbounded_String) return Boolean
   with Pre => A.Kind = Input;
   --  Returns true iff the next element of A is a tag and equal to S.

   procedure Append_Tag (A : in out Archive; The_Tag : Unbounded_String)
   with Pre => The_Tag = Coll_Begin or else
               The_Tag = Coll_End or else
               (Length (The_Tag) > 2 and then Element (The_Tag, 2) = ':');
   --  Append a given tag to the archive.

   procedure Append_Data (A : in out Archive; The_Data : Unbounded_String);
   --  Append a given bit of data to the archive.

   function To_Hex (C : Character) return Hex_String;
   --  Convert a character (such as ' ') to a two-digit hex representation
   --  ("20" in this example).

   function From_Hex (S : Hex_String) return Character;
   --  The inverse of the above. Raises Parse_Error if we get something
   --  that is not a hex string.

   function Escape (S : Unbounded_String) return Unbounded_String;
   --  Escape a string so that it contains no spaces or unprintable
   --  characters.
   --
   --     * the empty string is encoded as "\0"
   --     * ' ' is translated to ':'
   --     * ':' and '\' are escaped with '\'
   --     * non-printable characters are encoded as '\xHH' where H is
   --       an upper-case hex digit.
   --
   --  This minimal translation ensures most strings are as long as they
   --  were before, and are reasonably readable. In particular most magic
   --  strings produced by SPARK 2014 should be untouched.

   function Interpret (S : Unbounded_String) return Unbounded_String;
   --  The inverse of Escape.

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
      with function Has_Element (Position : Cursor) return Boolean is <>;
      with function Element (Position : Cursor) return E is <>;
      with procedure Serialize (A : in out Archive; V : in out E) is <>;
   procedure Serialize_Collection (A   : in out Archive;
                                   V   : in out T;
                                   Tag : Unbounded_String);
   --  Generic serialisation for ada containers. Merge is a subprogram that
   --  is meant to add a single element to the container; we need this
   --  because append/insert have different signatures.

   -----------
   -- Match --
   -----------

   procedure Match (A : in out Archive; S : Unbounded_String)
   is
   begin
      if A.Content.Is_Empty then
         raise Parse_Error with "insufficient data";
      elsif A.Content.First_Element.Kind = Tag and then
        A.Content.First_Element.Value = S
      then
         A.Content.Delete_First;
      else
         raise Parse_Error with "unexpected data";
      end if;
   end Match;

   ----------
   -- Test --
   ----------

   function Test (A : Archive; S : Unbounded_String) return Boolean
   is (not A.Content.Is_Empty
       and then A.Content.First_Element.Kind = Tag
       and then A.Content.First_Element.Value = S);

   ----------------
   -- Append_Tag --
   ----------------

   procedure Append_Tag (A : in out Archive; The_Tag : Unbounded_String) is
   begin
      A.Content.Append ((Kind  => Tag,
                         Value => The_Tag));
   end Append_Tag;

   -----------------
   -- Append_Data --
   -----------------

   procedure Append_Data (A : in out Archive; The_Data : Unbounded_String) is
   begin
      A.Content.Append ((Kind  => Data,
                         Value => The_Data));
   end Append_Data;

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
            Append (S,
                    (case E.Kind is
                        when Tag  => E.Value,
                        when Data => Escape (E.Value)));
         end loop;
      end return;
   end To_String;

   -----------------
   -- From_String --
   -----------------

   function From_String (S : String) return Archive is
      Tmp : Unbounded_String;
   begin
      return A : Archive (Input) do
         for I in Natural range S'Range loop
            if S (I) /= ' ' then
               Append (Tmp, S (I));
            end if;
            if S (I) = ' ' or else I = S'Last then
               if Length (Tmp) > 0 then
                  if Tmp = Coll_Begin
                    or else Tmp = Coll_End
                    or else (Length (Tmp) >= 2 and then Element (Tmp, 2) = ':')
                  then
                     Append_Tag (A, Tmp);
                  else
                     Append_Data (A, Interpret (Tmp));
                  end if;
                  Tmp := Null_Unbounded_String;
               end if;
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
            case Element (S, I) is
               when ' ' =>
                  Append (V, ':');
               when ':' | '\' =>
                  Append (V, '\');
                  Append (V, Element (S, I));
               when Unescaped_Printable_Character =>
                  Append (V, Element (S, I));
               when others =>
                  Append (V, "\x");
                  Append (V, To_Hex (Element (S, I)));
            end case;
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
            elsif In_Escape then
               case Element (S, I) is
                  when '0' =>
                     null;
                  when ':' | '\' =>
                     Append (V, Element (S, I));
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
               case Element (S, I) is
                  when '\' =>
                     In_Escape := True;
                  when ':' =>
                     Append (V, ' ');
                  when others =>
                     Append (V, Element (S, I));
               end case;
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
         case C.Kind is
            when Tag =>
               Put_Line ("   Tag: " & To_String (C.Value));
            when Data =>
               Put_Line ("   <" & To_String (C.Value) & ">");
         end case;
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
            elsif A.Content.First_Element.Kind /= Data then
               raise Parse_Error with "expected data, not tag";
            end if;
            V := A.Content.First_Element.Value;
            A.Content.Delete_First;
         when Output =>
            Append_Data (A, V);
      end case;
   end Serialize;

   ------------------------
   -- Serialize_Discrete --
   ------------------------

   procedure Serialize_Discrete (A : in out Archive; V : in out T) is
   begin
      case A.Kind is
         when Input =>
            if A.Content.Is_Empty then
               raise Parse_Error with "insufficient data";
            elsif A.Content.First_Element.Kind /= Data then
               raise Parse_Error with "expected data, not tag";
            end if;
            V := T'Value (To_String (A.Content.First_Element.Value));
            A.Content.Delete_First;
         when Output =>
            Append_Data (A, (Trim (To_Unbounded_String (T'Image (V)), Both)));
      end case;
   end Serialize_Discrete;

   --------------------------
   -- Serialize_Collection --
   --------------------------

   procedure Serialize_Collection (A   : in out Archive;
                                   V   : in out T;
                                   Tag : Unbounded_String)
   is
      The_Tag : constant Unbounded_String := "c:" & Tag;
      Has_Tag : constant Boolean          := Length (Tag) > 0;
      Tmp     : E := Null_Element;
   begin
      case A.Kind is
         when Input =>
            V := Null_Container;
            if Has_Tag then
               if Test (A, The_Tag) then
                  Match (A, The_Tag);
               else
                  return;
               end if;
            end if;
            Match (A, Coll_Begin);
            while not Test (A, Coll_End) loop
               Serialize (A, Tmp);
               Merge (V, Tmp);
            end loop;
            Match (A, Coll_End);
         when Output =>
            declare
               C : Cursor := First (V);
            begin
               if Has_Tag then
                  if Has_Element (C) then
                     Append_Tag (A, The_Tag);
                  else
                     return;
                  end if;
               end if;
               Append_Tag (A, Coll_Begin);
               while Has_Element (C) loop
                  Tmp := Element (C);
                  Serialize (A, Tmp);
                  C := Next (C);
               end loop;
               Append_Tag (A, Coll_End);
            end;
      end case;
   end Serialize_Collection;

   --------------------
   -- Serialize_List --
   --------------------

   procedure Serialize_List (A   : in out Archive;
                             V   : in out T;
                             Tag : String := "")
   is
      procedure Merge (Container : in out T;
                       New_Item  : E);
      --  Local helper subprogram that wraps Append to eliminate the third
      --  argument.

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
        (T              => T,
         E              => E,
         Cursor         => Cursor,
         Null_Container => Null_Container,
         Null_Element   => Null_Element,
         Merge          => Merge);

   --  Start of processing for Serialize_List

   begin
      Serialize (A, V, To_Unbounded_String (Tag));
   end Serialize_List;

   -------------------
   -- Serialize_Set --
   -------------------

   procedure Serialize_Set (A   : in out Archive;
                            V   : in out T;
                            Tag : String := "")
   is
      ---------------
      -- Serialize --
      ---------------

      procedure Serialize is new Serialize_Collection
        (T              => T,
         E              => E,
         Cursor         => Cursor,
         Null_Container => Null_Container,
         Null_Element   => Null_Element,
         Merge          => Insert);
   begin
      Serialize (A, V, To_Unbounded_String (Tag));
   end Serialize_Set;

end Serialisation;
