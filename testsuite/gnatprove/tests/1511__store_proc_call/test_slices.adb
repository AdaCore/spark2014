procedure Test_Slices with SPARK_Mode is
   subtype Index is Positive range 1 .. 4;
   type Int_Array is array (Index range <>) of Integer;

   ------------------
   -- Set_Values --
   ------------------

   procedure Set_Values
     (Low, High : out Index; Values : out Int_Array; New_Low, New_High : Index)
   with
     Global => null,
     Pre    => Values'Length = 1,
     Post   =>
       Low = New_Low and High = New_High and Values = (Values'Range => 42)
   is
   begin
      Low := New_Low;
      High := New_High;
      Values := (others => 42);
   end Set_Values;

   Low  : Index := 1;
   High : Index := 2;
   A    : Int_Array (1 .. 4) := (10, 20, 30, 40);
begin
   --  Moving the lower bound past element 2 must not lose its value when
   --  copying back the update to element 1 through the original slice.

   Set_Values (Low, High, A (Low .. High) (1 .. 1), 3, 4);

   pragma Assert (A = (42, 20, 30, 40)); -- @ASSERT:PASS

   Low := 3;
   High := 4;
   A := (10, 20, 30, 40);

   --  Moving the upper bound before element 4 must likewise preserve its
   --  value when updating element 3 through the original slice.

   Set_Values (Low, High, A (Low .. High) (3 .. 3), 1, 2);

   pragma Assert (A = (10, 20, 42, 40)); -- @ASSERT:PASS
end Test_Slices;
