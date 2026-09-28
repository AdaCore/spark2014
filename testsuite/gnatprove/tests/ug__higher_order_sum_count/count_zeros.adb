package body Count_Zeros is

   procedure Reset (A : in out Int_Array; I : Positive) is
      Old : constant Int_Array := A with Ghost;
   begin
      A (I) := 0;
      Update_Count (Old, A, I);
   end Reset;

end Count_Zeros;
