with Hidden; use Hidden;

procedure Bad2 is

   function Increment_And_Return return Integer with
     Side_Effects, Pre => True;

   function Increment_And_Return return Integer is
   begin
      Set_X (Get_X + 1);
      return Get_X;
   end Increment_And_Return;

   type Arr is array (1 .. 3) of Integer;
   A : Arr;
begin
   A (Get_X) := Increment_And_Return;
   pragma Assert (Get_X = A (Get_X));
end Bad2;
