with Int_Pointers; use Int_Pointers;

procedure Aliasing with SPARK_Mode is
   use Pointers, Copy_Operations;

   X, Y : Pointer;
begin
   Create_Int (1, X);
   Y := X;
   --  Y and X designate the same memory cell

   Assign (X, 2);
   pragma Assert (Deref (Y) = 2);

   --  The cell is reclaimed automatically when X and Y go out of scope
end Aliasing;
