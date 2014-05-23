package body Foo
is

   procedure Sum (A : in Array_T; S : out Integer)
   is
      Total : Integer;
      A_LB  : Integer;
      A_UB  : Integer;
      Item  : Integer;
   begin
      A_LB := A'First;
      A_UB := A'Last;
      Total := 0;
      for I in Integer range A_LB .. A_UB loop
         Item := A (I);
         Total := Total + Item;
      end loop;
      S := Total;
   end Sum;

end Foo;
