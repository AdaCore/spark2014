with Ada.Containers;   use Ada.Containers;
with Ada.Strings.Hash;

with Ada.Containers.Formal_Indefinite_Vectors;

package body Names with
   SPARK_Mode
   --  Refined_State => (Name_Table => (Hash_Table,
   --                                   Char_Table,
   --                                   Entry_Table))
is

   subtype Valid_Name_Id is Name_Id range 1 .. Name_Id'Last;

   --  Initial hash table for strings -> name_id

   Hash_Table_Size : constant := 256;
   subtype Hash_Table_Index_T is Hash_Type range 0 .. (Hash_Table_Size - 1);
   type Hash_Table_T is array (Hash_Table_Index_T) of Name_Id;

   Hash_Table  : Hash_Table_T := (others => 0);

   --  Table for string content

   type Char_Table_Index is range 0 .. 2 ** 31 - 2;

   package Char_Tables is new Ada.Containers.Formal_Indefinite_Vectors
     (Index_Type   => Char_Table_Index,
      Element_Type => Character,
      Bounded      => False,
      Max_Size_In_Storage_Elements => Character'Size);
   use Char_Tables;

   Char_Table  : Char_Tables.Vector (1024);

   --  Combined table for string table pointers and hash chains.

   type Name_Entry is record
      Table_Index : Char_Table_Index;
      Length      : Positive;
      Next_Hash   : Name_Id;
   end record;

   package Entry_Tables is new Ada.Containers.Formal_Indefinite_Vectors
     (Index_Type   => Valid_Name_Id,
      Element_Type => Name_Entry,
      Bounded      => False,
      Max_Size_In_Storage_Elements => Name_Entry'Size);
   use Entry_Tables;

   Entry_Table : Entry_Tables.Vector (128);

   ------------
   -- Lookup --
   ------------

   procedure Lookup (S : String;
                     N : out Name_Id)
   --with Refined_Global => (In_Out => (Char_Table, Entry_Table))
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

            exit when Element (Entry_Table, Ptr).Next_Hash = 0;
            Ptr := Element (Entry_Table, Ptr).Next_Hash;
         end loop;
      end if;

      for Char of S loop
         Append (Char_Table, Char);
      end loop;

      pragma Assert (Integer (Last_Index (Char_Table)) = Integer (Length (Char_Table)) - 1);
      pragma Assert (Length (Char_Table) <= 2 ** 31 - 1);
      pragma Assert (Last_Index (Char_Table) <= Char_Table_Index'Last);

      Append (Entry_Table,
              (Table_Index => Last_Index (Char_Table) - (S'Length - 1),
               Length      => S'Length,
               Next_Hash   => 0));
      N := Last_Index (Entry_Table);

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
   --with Refined_Global => (Char_Table, Entry_Table)
   is
   begin
      if N = 0 then
         return "";
      end if;
      declare
         E : constant Name_Entry := Element (Entry_Table, N);
         L : constant Positive   := E.Length;
      begin
         return S : String (1 .. L) do
            for I in Positive range 1 .. L loop
               S (I) := Element (Char_Table,
                                 E.Table_Index + Char_Table_Index (I - 1));
            end loop;
         end return;
      end;
   end To_String;

   ---------------
   -- Invariant --
   ---------------

   function Invariant return Boolean is (True);
   --with Refined_Global => (Char_Table, Entry_Table);

end Names;
