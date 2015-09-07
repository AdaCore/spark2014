pragma SPARK_Mode(On);

package body Initializer_Demo is

   function Add_Elements (A : Integer_Array) return Integer is
      Sum : Integer := 0;  -- Ineffective initialization
   begin
      Sum := 0;
      for Index in A'Range loop
         Sum := Sum + A (Index);
      end loop;
      return Sum;
   end Add_Elements;


   function Add_Elements2 (A : Integer_Array) return Integer is
      Sum : Accumulator;
   begin
      -- Sum is automatically initialized.
      -- Yet assignment below does not cause a flow issue.
      Sum := 1;  -- Start with a bias value.
      for Index in A'Range loop
         Sum := Sum + Accumulator (A (Index)); -- note type conversion
      end loop;
      return Integer (Sum);
   end Add_Elements2;


   function Adjust_Pair (P : Pair_With_Default) return Pair_With_Default is
      Offset : Pair_With_Default;
   begin
      -- Offset is automatically initialized.
      -- Yet assignment below does not cause a flow issue.
      Offset.Y := 1;
      return (P.X + Offset.X, P.Y + Offset.Y);
   end Adjust_Pair;


   --function Adjust_Pair
   --  (P : Pair_With_YDefault) return Pair_With_YDefault is
   --
   --   Offset : Pair_With_Default;
   --begin
   --   -- Offset.Y is automatically initialized.
   --   Offset.Y := 1;
   --   -- Use of X is an error (not initialized).
   --   return (P.X + Offset.X, P.Y + Offset.Y);
   --end Adjust_Pair;

end Initializer_Demo;
