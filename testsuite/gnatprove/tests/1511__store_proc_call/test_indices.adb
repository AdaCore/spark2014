procedure Test_Indices with SPARK_Mode is
   subtype Index is Positive range 1 .. 2;

   type Cell is record
      Value, Unchanged : Integer;
   end record;

   type Cell_Array is array (Index) of Cell;

   procedure Set_Value (I : out Index; Value : out Integer)
   with Global => null, Post => I = 2 and Value = 42
   is
   begin
      I := 2;
      Value := 42;
   end Set_Value;

   I : Index := 1;
   A : Cell_Array :=
     (1 => (Value => 0, Unchanged => 10), 2 => (Value => 0, Unchanged => 20));
begin
   --  The call changes I, but the prefix of A (I).Value still denotes A (1)

   Set_Value (I, A (I).Value);

   --  The call only changes A (1).Value, so A (1).Unchanged remains 10

   pragma Assert (A (1).Unchanged = 20); -- @ASSERT:FAIL
end Test_Indices;
