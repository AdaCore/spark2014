package body InRange is
   function Add1 (i : int20; j : int10) return Integer is
   begin
      return i + j;
   end Add1;
   function Add (i : int20; j : int10) return Integer is
   begin
      return i + Add1(j, j);
   end Add;
end InRange;
