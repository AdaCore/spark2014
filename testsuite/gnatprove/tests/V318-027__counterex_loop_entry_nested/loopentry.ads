package LoopEntry is

   type Int is range 1 .. 10;

   type Int_Array is array (Int) of Int;

   procedure Increment_Array_Nested_Loop_Simple (A : in out Int_Array)
      with Pre => (for all J in A'Range => A(J) <= Int'Last - 2);

   procedure Increment_Array_Nested_Loop_Inner (A : in out Int_Array)
      with Pre => (for all J in A'Range => A(J) <= Int'Last - 2);

   procedure Increment_Array_Nested_Loop_Outter (A : in out Int_Array)
      with Pre => (for all J in A'Range => A(J) <= Int'Last - 2);

   procedure Very_Nested (A : in out Int_Array)
      with Pre => (for all J in A'Range => A(J) <= Int'Last - 3);

   procedure Loop_Entry_In_Loop_Spec (I : in out Int)
      with Pre => I > Int'First and I < Int'Last;
end LoopEntry;
