with Ada.Unchecked_Deallocation;
procedure Test_Dealloc with SPARK_Mode is

   package Trie is
      pragma Unevaluated_Use_Of_Old (Allow);

      type Trie is private;

      procedure Erase (T : in out Trie);

   private

      type Trie_Cell;

      type Trie is access Trie_Cell;

      type Cell_Array is array (Character) of Trie;

      type Trie_Cell is record
         Value    : Natural;
         Children : Cell_Array;
      end record;
   end Trie;

   package body Trie is

      procedure Free_Cell is new Ada.Unchecked_Deallocation (Trie_Cell, Trie);

      procedure Erase (T : in out Trie) with
	Refined_Post => T = null
      is
      begin
         if T = null then
            return;
         end if;

         for C in Character loop
            Erase (T.Children (C));
            pragma Loop_Invariant
              (for all D in Character'First .. C => T.Children (D) = null);
         end loop;

         Free_Cell (T);
      end Erase;

   end Trie;
begin
   null;
end Test_Dealloc;
