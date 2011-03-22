package body InRange is
   function Add1 (i : int20; j : int10) return Integer is
   begin
      return i + j;
   end Add1;
   function Add (i : int20; j : int10) return Integer is
   begin
      return i + Add1(j, j);
   end Add;

   procedure Add_Out (I : in out int20; J : int10)
   is
   begin
      I := I + J;
   end Add_Out;

   function Do_It return int10
   is
      X, Y : int10 := 10;
   begin
      Add_Out (X, Y);
      return X;
   end Do_It;

end InRange;
