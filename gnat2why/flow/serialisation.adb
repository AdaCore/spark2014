------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                         S E R I A L I S A T I O N                        --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                  Copyright (C) 2015, Altran UK Limited                   --
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

with Ada.Characters.Latin_1; use Ada.Characters.Latin_1;
with Ada.Strings;            use Ada.Strings;
with Ada.Text_IO;            use Ada.Text_IO;

package body Serialisation is

   Coll_Begin : constant Unbounded_String := To_Unbounded_String ("[");
   Coll_End   : constant Unbounded_String := To_Unbounded_String ("]");

   --  Begin/end markers for collections (lists, sets).

   procedure Match (A : in out Archive; S : Unbounded_String)
   with Pre => A.Kind = Input;
   --  A classic match-token-or-die helper subprogram. Returns if the next
   --  element of A is equal to S, otherwise raises a Parse_Error
   --  exception.

   function Test (A : Archive; S : Unbounded_String) return Boolean
   with Pre => A.Kind = Input;
   --  Returns true iff the next element of A is equal to S.

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
      elsif A.Content.First_Element = S then
         A.Content.Delete_First;
      else
         raise Parse_Error with "unexpected data";
      end if;
   end Match;

   ----------
   -- Test --
   ----------

   function Test (A : Archive; S : Unbounded_String) return Boolean
   is (not A.Content.Is_Empty and then A.Content.First_Element = S);

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
            Append (S, Trim (E, Both));
         end loop;
      end return;
   end To_String;

   -----------------
   -- From_String --
   -----------------

   function From_String (S : Unbounded_String) return Archive is
      Tmp : Unbounded_String;
   begin
      return A : Archive (Input) do
         for I in Natural range 1 .. Length (S) loop
            if Element (S, I) /= ' ' then
               Append (Tmp, Element (S, I));
            end if;
            if Element (S, I) = ' ' or I = Length (S) then
               if Length (Tmp) > 0 then
                  A.Content.Append (Tmp);
                  Tmp := Null_Unbounded_String;
               end if;
            end if;
         end loop;
      end return;
   end From_String;

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

   procedure Serialize (A : in out Archive; V : in out Unbounded_String)
   is
      S      : Unbounded_String;
      Escape : Boolean := False;
   begin
      case A.Kind is
         when Input =>
            if A.Content.Is_Empty then
               raise Parse_Error with "insufficient data";
            end if;
            S := A.Content.First_Element;
            A.Content.Delete_First;

            if Length (S) < 2
              or else (Element (S, 1) /= 's' and Element (S, 2) /= ':')
            then
               raise Parse_Error with "malformed data";
            end if;

            V := Null_Unbounded_String;
            for I in Natural range 3 .. Length (S) loop
               if Escape then
                  case Element (S, I) is
                     when '\' | '[' | ']' | '.' =>
                        Append (V, Element (S, I));
                     when 'n' =>
                        Append (V, LF);
                     when others =>
                        raise Parse_Error with "malformed data";
                  end case;
                  Escape := False;
               else
                  case Element (S, I) is
                     when '\' =>
                        Escape := True;
                     when '.' =>
                        Append (V, ' ');
                     when others =>
                        Append (V, Element (S, I));
                  end case;
               end if;
            end loop;

         when Output =>
            S := To_Unbounded_String ("s:");
            for I in Natural range 1 .. Length (V) loop
               case Element (V, I) is
                  when '\' | '[' | ']' | '.' =>
                     Append (S, '\');
                     Append (S, Element (V, I));
                  when LF =>
                     Append (S, "\n");
                  when ' ' =>
                     Append (S, ".");
                  when others =>
                     Append (S, Element (V, I));
               end case;
            end loop;
            A.Content.Append (S);
      end case;
   end Serialize;

   -------------------------
   -- Serialize_Discreete --
   -------------------------

   procedure Serialize_Discreete (A : in out Archive; V : in out T) is
   begin
      case A.Kind is
         when Input =>
            if A.Content.Is_Empty then
               raise Parse_Error with "insufficient data";
            end if;
            V := T'Value (To_String (A.Content.First_Element));
            A.Content.Delete_First;
         when Output =>
            A.Content.Append (To_Unbounded_String (T'Image (V)));
      end case;
   end Serialize_Discreete;

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
            if Has_Tag and then not Test (A, The_Tag) then
               return;
            end if;
            if Has_Tag then
               Match (A, The_Tag);
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
                     A.Content.Append (The_Tag);
                  else
                     return;
                  end if;
               end if;
               A.Content.Append (Coll_Begin);
               while Has_Element (C) loop
                  Tmp := Element (C);
                  Serialize (A, Tmp);
                  C := Next (C);
               end loop;
               A.Content.Append (Coll_End);
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
