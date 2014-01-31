package body Foo
is

   function Sum (A : in Array_T) return Integer
   is
      Total : Integer;
   begin
      Total := 0;
      for I in A'Range loop
         Total := Total + A (I);
      end loop;
      return Total;
   end Sum;

end Foo;
