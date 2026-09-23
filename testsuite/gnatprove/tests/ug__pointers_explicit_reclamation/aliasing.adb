with Int_Pointers; use Int_Pointers;

procedure Aliasing with SPARK_Mode is
   use Pointers, Pointers.Memory_Model, Copy_Operations;

   X, Y : Pointer;
begin
   Create_Int (1, X);
   Y := X;
   --  Y and X designate the same memory cell

   declare
      R : constant not null access Integer := Reference (Memory, X);
   begin
      R.all := 2;
   end;
   pragma Assert (Deref (Y) = 2);

   Dealloc (X);
   pragma Assert (not In_Memory (Model (Memory), Y));
   --  Y is now dangling, it cannot be dereferenced
end Aliasing;
