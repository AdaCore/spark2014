package body Test is
   procedure Foo (Index : My_Range;
                  Arr   : in out Arr_Of_Discr_T)
   is
   begin
      Arr (Index).X := 10;
   end Foo;
end Test;
