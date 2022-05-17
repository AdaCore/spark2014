package LoopEntry is

   type Int is range 1 .. 10;

   type Int_Array is array (Int) of Int;

   type Array_Record is record
      A : Int_Array := (others => 1);
   end record;

   function Same (I : in Int) return Int;

   function Same (A : in Int_Array) return Int_Array
      with Post => Same'Result = A;

   procedure Increment_Assert (I : in out Int)
      with Pre => I <= Int'Last - 3;

   procedure Increment_Invariant (I : in out Int)
      with Pre => I <= Int'Last - 3;

   procedure Increment_Array_Assert (A : in out Int_Array)
      with Pre => (for all J in A'Range => A(J) < Int'Last);

   procedure Increment_Array_Invariant (A : in out Int_Array)
      with Pre => (for all J in A'Range => A(J) < Int'Last);

   procedure Loop_Entry_On_Call_Assert (A : in out Int_Array)
      with Pre => (for all J in A'Range => A(J) < Int'Last);

   procedure Loop_Entry_On_Call_Invariant (A : in out Int_Array)
      with Pre => (for all J in A'Range => A(J) < Int'Last);

   procedure Loop_Entry_On_Arr_In_Record_Assert (R : in out Array_Record)
      with Pre => (for all J in R.A'Range => R.A(J) < Int'Last);

   procedure Loop_Entry_On_Arr_In_Record_Invariant (R : in out Array_Record)
      with Pre => (for all J in R.A'Range => R.A(J) < Int'Last);

   procedure Loop_Entry_In_Call_Param (I : in Int);

end LoopEntry;
