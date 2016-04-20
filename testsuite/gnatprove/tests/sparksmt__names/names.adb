------------------------------------------------------------------------------
--                                                                          --
--                           SPARKSMT COMPONENTS                            --
--                                                                          --
--                                N A M E S                                 --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--               Copyright (C) 2016, Altran UK Limited                      --
--                                                                          --
-- sparksmt is  free  software;  you can redistribute  it and/or  modify it --
-- under terms of the  GNU General Public License as published  by the Free --
-- Software  Foundation;  either version 3,  or (at your option)  any later --
-- version.  sparksmt is distributed  in the hope that  it will be  useful, --
-- but WITHOUT ANY WARRANTY; without even the implied warranty of  MERCHAN- --
-- TABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the GNU General Public --
-- License for  more details.  You should have  received  a copy of the GNU --
-- General  Public License  distributed with  sparksmt;  see file COPYING3. --
-- If not,  go to  http://www.gnu.org/licenses  for a complete  copy of the --
-- license.                                                                 --
--                                                                          --
------------------------------------------------------------------------------

with Ada.Containers;   use Ada.Containers;
with Ada.Strings.Hash;

with Ada.Containers.Formal_Vectors;

package body Names
is

   subtype Valid_Name_Id is Name_Id range 1 .. Name_Id'Last;

   --  Initial hash table for strings -> name_id

   Hash_Table_Size : constant := 256;
   subtype Hash_Table_Index_T is Hash_Type range 0 .. (Hash_Table_Size - 1);
   type Hash_Table_T is array (Hash_Table_Index_T) of Name_Id;

   Hash_Table  : Hash_Table_T := (others => 0);

   --  Table for string content

   type Char_Table_Index is range 0 .. 2 ** 31 - 2;

   function Eq (A, B : Character) return Boolean is (A = B);
   --  Workaround for P414-029

   package Char_Tables is new Ada.Containers.Formal_Vectors
     (Index_Type   => Char_Table_Index,
      Element_Type => Character,
      "="          => Eq,
      Bounded      => False);
   use Char_Tables;

   Char_Table  : Char_Tables.Vector (1024);

   --  Combined table for string table pointers and hash chains.

   type Name_Entry is record
      Table_Index : Char_Table_Index;
      Length      : Positive;
      Next_Hash   : Name_Id;
   end record with
     Predicate =>
     (Name_Entry.Table_Index <=
        Char_Table_Index'Last - Char_Table_Index (Name_Entry.Length - 1));

   function Eq (A, B : Name_Entry) return Boolean is (A = B);
   --  Workaround for P414-029

   package Entry_Tables is new Ada.Containers.Formal_Vectors
     (Index_Type   => Valid_Name_Id,
      Element_Type => Name_Entry,
      "="          => Eq,
      Bounded      => False);
   use Entry_Tables;

   Entry_Table : Entry_Tables.Vector (256);

   ----------------
   -- Invariants --
   ----------------

   function Valid_Tables return Boolean is
      (Last_Index (Entry_Table) <= Name_Id'Last and
       Last_Index (Char_Table) <= Char_Table_Index'Last)
   with Ghost;

   function Valid_Hashes return Boolean is
      (for all H in Hash_Table_Index_T =>
         Hash_Table (H) <= Last_Index (Entry_Table))
   with Ghost;

   function Valid_Entry (E : Name_Entry) return Boolean is
      (E.Next_Hash <= Last_Index (Entry_Table) and
       E.Table_Index + Char_Table_Index (E.Length - 1) <= Last_Index (Char_Table))
   with Ghost,
        Pre => Valid_Tables;

   function Valid_Name_Table return Boolean is
      (for all I in Name_Id
         range First_Index (Entry_Table) .. Last_Index (Entry_Table) =>
         Valid_Entry (Element (Entry_Table, I)))
   with Ghost,
        Pre => Valid_Tables;

   procedure Merge (S : String;
                    N : out Name_Id)
   with Global => (In_Out   => (Char_Table, Entry_Table),
                   Proof_In => Hash_Table),
        Pre    => Invariant,
        Post   => Invariant and
                  Length (Entry_Table) = Length (Entry_Table)'Old + 1 and
                  Length (Char_Table) >= Length (Char_Table)'Old and
                  N = Last_Index (Entry_Table);
   --  Merge the given string into the table, producing a *new* name_id,
   --  i.e. does not check for duplicates using the hash table.

   procedure Merge (S : String;
                    N : out Name_Id)
   is
      --  If this is not true, then we're out of memory on the string or
      --  entry table...
      pragma Assume (Last_Index (Char_Table)
                       < Char_Table_Index'Last - S'Length);
      pragma Assume (Last_Index (Entry_Table) < Name_Id'Last);
   begin
      for I in Positive range 1 .. S'Length loop
         Append (Char_Table, S (I + (S'First - 1)));
         pragma Loop_Invariant
           (Invariant and
            Length (Char_Table) =
              Length (Char_Table)'Loop_Entry + Char_Tables.Capacity_Range (I));
      end loop;

      declare
         E : constant Name_Entry :=
           (Table_Index => Last_Index (Char_Table) - (S'Length - 1),
            Length      => S'Length,
            Next_Hash   => 0);
      begin
         Append (Entry_Table, E);
      end;
      N := Last_Index (Entry_Table);
   end Merge;

   ------------
   -- Lookup --
   ------------

   procedure Lookup (S : String;
                     N : out Name_Id)
   is
      Ptr : Name_Id := 0;
      H   : constant Hash_Table_Index_T :=
        Ada.Strings.Hash (S) mod Hash_Table_Size;
   begin
      if S'Length = 0 then
         N := 0;
         return;
      end if;

      N := Hash_Table (H);
      if N in Valid_Name_Id then
         Ptr := N;
         loop
            if To_String (Ptr) = S then
               N := Ptr;
               return;
            end if;

            pragma Loop_Invariant
              (Ptr in Valid_Name_Id and
               Ptr <= Last_Index (Entry_Table) and
               Invariant);

            exit when Element (Entry_Table, Ptr).Next_Hash = 0;
            Ptr := Element (Entry_Table, Ptr).Next_Hash;
         end loop;
      end if;

      Merge (S, N);

      if Ptr in Valid_Name_Id then
         Replace_Element (Entry_Table,
                          Ptr,
                          Element (Entry_Table, Ptr)'Update (Next_Hash => N));
      else
         Hash_Table (H) := N;
      end if;

   end Lookup;

   ---------------
   -- To_String --
   ---------------

   function To_String (N : Name_Id) return String
   is
      --  The only names are the ones produced by lookup.
      pragma Assume (N <= Last_Index (Entry_Table));
   begin
      if N = 0 then
         return "";
      end if;
      declare
         E : constant Name_Entry := Element (Entry_Table, N);
         L : constant Positive   := E.Length;
      begin
         pragma Annotate (GNATprove, False_Positive,
                          """S"" might not be initialized",
                          "it obviously is");
         return S : String (1 .. L) do
            for I in Positive range 1 .. L loop
               S (I) := Element (Char_Table,
                                 E.Table_Index + Char_Table_Index (I - 1));
               pragma Loop_Invariant (Invariant);
            end loop;
         end return;
      end;
   end To_String;

   ---------------
   -- Invariant --
   ---------------

   function Invariant return Boolean is
      ((Valid_Tables and then Valid_Name_Table) and
       Valid_Hashes);

end Names;
